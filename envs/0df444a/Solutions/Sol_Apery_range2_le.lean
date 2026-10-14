-- Prove2me | solution 1 for Apery.range2_le
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T15:07:50.623041+00:00
-- url     : https://prove2.me/submissions/549a5160-3ef8-42a6-8a1b-a1b970d038f1

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The inner tail range (source `Apery/Growth/Assembly3.lean`)

This file proves the platform theorem `Apery.range2_le`: for $n \ge 10400$,

$$\sum_{K/400 < p \le K/20} c(k)\,\bigl(-L_k\bigr) \;\le\;
\operatorname{psum}\Bigl(xF(x) + \frac{27}{16}\Bigr)\,20\,400\,K \;+\; 10^7\,\theta(2n),
\qquad K = 40n,$$

where $c(k) = \log k$ for primes and $0$ otherwise, $L_k$ is the local exponent of the
normaliser, $F$ the tail profile and $\operatorname{psum}$ the weighted prime sum. A faithful
port of the pinned source project mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0:
the class-basis and counting framework (`Apery/Arith/ClassFrame.lean`,
`Apery/Arith/ClassCount.lean`, `Apery/Arith/SmallPrimeTau.lean`), the inner weights
(`Apery/Arith/InnerWeights.lean`), the water-filling allocation and its weight sum
(`Apery/Arith/InnerAlloc.lean`), the parameters of Section 4.1 and the $p$-adic valuation of
$S_K$ (`Apery/Normalization.lean`, `Apery/Legendre.lean`), the class-sum approximation
(`Apery/Growth/ClassSum.lean`, `Apery/Growth/ClassData.lean`), the inner per-prime bound
`inner_Lp_le` (`Apery/Growth/InnerPrime.lean`), then `tail_Lp_le` and `Ctail_le`
(`Apery/Growth/TailPrime.lean`, `Apery/Growth/Assembly2.lean`) and the summation over the
range.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceGrowth

set_option autoImplicit false

section Port0
/-!
# The inner tail range `K/400 < p ≤ K/20` (source `Apery/Growth/Assembly3.lean`)

This file proves the platform theorem `Apery.range2_le`:

`∑_{K/400 < p ≤ K/20} c(k)(-L_k) ≤ psum (x F(x) + 27/16) 20 400 K + 10^7 θ(2n)` for `n ≥ 10400`.

A faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: the class-basis and counting
framework (`Apery/Arith/ClassFrame.lean`, `Apery/Arith/ClassCount.lean`,
`Apery/Arith/SmallPrimeTau.lean`), the inner weights (`Apery/Arith/InnerWeights.lean`), the
water-filling allocation and its weight sums (`Apery/Arith/InnerAlloc.lean`), the parameters of
Section 4.1 and the `p`-adic valuation of `S_K` (`Apery/Normalization.lean`,
`Apery/Legendre.lean`), the class-sum approximation (`Apery/Growth/ClassSum.lean`,
`Apery/Growth/ClassData.lean`), the inner per-prime bound `inner_Lp_le`
(`Apery/Growth/InnerPrime.lean`, with `Sep_PlK` from `Apery/Norm.lean`), the tail bound
`tail_Lp_le` and the additive error `Ctail_le` (`Apery/Growth/TailPrime.lean`,
`Apery/Growth/Assembly2.lean`), and the final summation over the range
(`Apery/Growth/Assembly3.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Finset Polynomial

namespace Apery

/-! ## The pole count and the class-basis framework -/

section PoleCount

def plc (p : ℕ) (Pl : Finset ℤ) (c : ZMod p) : Finset ℤ := Pl.filter fun r : ℤ => (r : ZMod p) = c

lemma PlK_disjoint (K : ℕ) :
    Disjoint ((Icc 1 K).image (fun j : ℕ => (j : ℤ))) ((Icc 1 K).image (fun j : ℕ => -(j : ℤ))) := by
  rw [Finset.disjoint_left]
  intro r h1 h2
  rw [Finset.mem_image] at h1 h2
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, hab⟩ := h2
  rw [Finset.mem_Icc] at ha hb
  omega

variable {p : ℕ} [hp : Fact p.Prime]

lemma mem_PlK_iff {K : ℕ} {r : ℤ} (hr : r ∈ PlK K) :
    ∃ j ∈ Icc 1 K, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ r = ε * j := by
  simp only [PlK, Finset.mem_union, Finset.mem_image] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨j, hj, 1, Or.inl rfl, by ring⟩
  · exact ⟨j, hj, -1, Or.inr rfl, by ring⟩

variable {p : ℕ} [hp : Fact p.Prime]

lemma Sep_PlK {K : ℕ} (hK : 2 * K < p ^ 2) : Sep p (PlK K) := by
  intro r hr s hs hrs _ hdvd
  obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hr
  obtain ⟨j', hj', ε', hε', rfl⟩ := mem_PlK_iff hs
  have h1 := Finset.mem_Icc.mp hj
  have h2 := Finset.mem_Icc.mp hj'
  have hlt : |ε * (j : ℤ) - ε' * j'| < (p : ℤ) ^ 2 := by
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> rw [abs_lt] <;> constructor <;>
      push_cast <;> nlinarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  exact hrs (by linarith)

end PoleCount

section ClassFrame

def classRoots {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) : Multiset ℤ :=
  (∑ c ∈ Finset.univ.erase a, Multiset.replicate (L c) ((c : ℕ) : ℤ)) +
    Multiset.replicate i ((a : ℕ) : ℤ)

lemma card_classRoots {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) :
    (classRoots L a i).card = ∑ c ∈ Finset.univ.erase a, L c + i := by
  simp [classRoots, Multiset.card_sum]

lemma sq_injective {p m : ℕ} [hp : Fact p.Prime] (hm : 2 * m + 1 = p) :
    Function.Injective fun c : Fin (m + 1) => -(((c : ℕ) : ZMod p) ^ 2) := by
  intro c c' h
  simp only [neg_inj] at h
  have h2 : (p : ℤ) ∣ ((c : ℕ) - (c' : ℕ) : ℤ) * ((c : ℕ) + (c' : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
    linear_combination h
  have hc := c.isLt; have hc' := c'.isLt
  rcases (Int.Prime.dvd_mul' hp.out h2) with h3 | h3
  · have := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> push_cast <;> omega)
    exact Fin.ext (by omega)
  · have := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> push_cast <;> omega)
    exact Fin.ext (by omega)

def entryRoots {m : ℕ} (N : ℕ) (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a)) :
    Multiset ℤ :=
  6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ)) + classRoots L s.1 s.2 + classRoots L t.1 t.2

noncomputable def classCount (p : ℕ) (K : ℕ) (M : Multiset ℤ) (c : ZMod p) : ℚ :=
  (((if c = 0 then 5 else 0) + (M.filter fun γ : ℤ => (γ : ZMod p) = c).card +
    (M.filter fun γ : ℤ => (γ : ZMod p) = -c).card : ℕ) : ℚ) - (plc p (PlK K) c).card

end ClassFrame

section ClassCount

/-!
# Class counting

For `p = 2m + 1` every residue `c` mod `p` is `≡ ±a` for a unique `a ∈ {0, …, m}` (`ccls c`).
We express the per-class counts `classCount` of the framework in terms of these classes.
-/

open Finset Polynomial


variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-- `μ(a, c) = [a ≡ c] + [a ≡ -c]`. -/
def mu (p : ℕ) (a : ℕ) (c : ZMod p) : ℕ :=
  (if ((a : ℤ) : ZMod p) = c then 1 else 0) + (if ((a : ℤ) : ZMod p) = -c then 1 else 0)

lemma ccls_spec (hm : 2 * m + 1 = p) (c : ZMod p) :
    (((ccls hm c : ℕ) : ℤ) : ZMod p) = c ∨ (((ccls hm c : ℕ) : ℤ) : ZMod p) = -c := by
  have hp0 : NeZero p := ⟨hp.out.ne_zero⟩
  unfold ccls
  split_ifs with h
  · left; simp
  · right
    have hv := c.val_lt
    simp only [Fin.val_mk]
    rw [show ((p - c.val : ℕ) : ℤ) = (p : ℤ) - (c.val : ℤ) by push_cast [Nat.cast_sub hv.le]; ring]
    push_cast
    rw [ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]

lemma two_ne_zero_zmod (hm : 2 * m + 1 = p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  rcases (Nat.le_succ_iff.mp this) with h1 | h1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h2 | h2
    · exact hp.out.ne_zero h2
    · exact hp.out.ne_one h2
  · omega

/-- Uniqueness of the class. -/
lemma ccls_unique (hm : 2 * m + 1 = p) (c : ZMod p) (a : Fin (m + 1))
    (h : (((a : ℕ) : ℤ) : ZMod p) = c ∨ (((a : ℕ) : ℤ) : ZMod p) = -c) : a = ccls hm c := by
  have h1 := ccls_spec hm c
  apply sq_injective hm
  simp only
  have e : ∀ x : ZMod p, x = c ∨ x = -c → x ^ 2 = c ^ 2 := by
    rintro x (rfl | rfl) <;> ring
  have ha := e _ h
  have hc := e _ h1
  push_cast at ha hc
  rw [ha, hc]

lemma mu_eq (hm : 2 * m + 1 = p) (a : Fin (m + 1)) (c : ZMod p) :
    mu p a c = if a = ccls hm c then (if c = 0 then 2 else 1) else 0 := by
  unfold mu
  by_cases ha : a = ccls hm c
  · rw [if_pos ha]
    have hs := ccls_spec hm c
    rw [← ha] at hs
    by_cases hc : c = 0
    · subst hc
      rw [if_pos rfl]
      have : (((a : ℕ) : ℤ) : ZMod p) = 0 := by rcases hs with h | h <;> simpa using h
      rw [if_pos this, if_pos (by rw [this, neg_zero])]
    · rw [if_neg hc]
      have hnot : ¬ ((((a : ℕ) : ℤ) : ZMod p) = c ∧ (((a : ℕ) : ℤ) : ZMod p) = -c) := by
        rintro ⟨h1, h2⟩
        apply hc
        have : (2 : ZMod p) * c = 0 := by
          have := h1.symm.trans h2; linear_combination this
        exact (mul_eq_zero.mp this).resolve_left (two_ne_zero_zmod hm)
      rcases hs with h | h
      · rw [if_pos h, if_neg (fun h' => hnot ⟨h, h'⟩)]
      · rw [if_neg (fun h' => hnot ⟨h', h⟩), if_pos h]
  · rw [if_neg ha]
    rw [if_neg (fun h => ha (ccls_unique hm c a (Or.inl h))),
      if_neg (fun h => ha (ccls_unique hm c a (Or.inr h)))]

lemma SX_neg (X : ℕ) (c : ZMod p) : SX p X (-c) = SX p X c := by
  unfold SX; rw [neg_neg, add_comm]

lemma SX_ccls (hm : 2 * m + 1 = p) (X : ℕ) (c : ZMod p) :
    SX p X c = SX p X (((ccls hm c : ℕ) : ℤ) : ZMod p) := by
  rcases ccls_spec hm c with h | h <;> rw [h]
  rw [SX_neg]

/-- The vanishing order of the row `s = (a, i)` at the class `b`. -/
def nu {m : ℕ} (L : Fin (m + 1) → ℕ) (s : Σ a : Fin (m + 1), Fin (L a)) (b : Fin (m + 1)) : ℕ :=
  if b = s.1 then s.2 else L b

lemma card_filter_replicate (k : ℕ) (v : ℤ) (P : ℤ → Prop) [DecidablePred P] :
    ((Multiset.replicate k v).filter P).card = if P v then k else 0 := by
  split_ifs with h
  · rw [Multiset.filter_eq_self.mpr fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact h]
    simp
  · rw [Multiset.filter_eq_nil.mpr fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact h]
    simp

lemma card_filter_sum_replicate {α : Type*} (s : Finset α) (L : α → ℕ) (v : α → ℤ) (P : ℤ → Prop)
    [DecidablePred P] :
    ((∑ c ∈ s, Multiset.replicate (L c) (v c)).filter P).card = ∑ c ∈ s, if P (v c) then L c else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.filter_add, Multiset.card_add, ih, Finset.sum_insert ha,
      card_filter_replicate]

lemma count_classRoots (hm : 2 * m + 1 = p) (L : Fin (m + 1) → ℕ) (s : Σ a : Fin (m + 1), Fin (L a))
    (c : ZMod p) :
    ((classRoots L s.1 s.2).filter fun γ : ℤ => (γ : ZMod p) = c).card +
      ((classRoots L s.1 s.2).filter fun γ : ℤ => (γ : ZMod p) = -c).card =
      (if c = 0 then 2 else 1) * nu L s (ccls hm c) := by
  unfold classRoots
  simp only [Multiset.filter_add, Multiset.card_add, card_filter_sum_replicate, card_filter_replicate]
  have key : ∀ b : Fin (m + 1), ∀ k : ℕ, ((if (((b : ℕ) : ℤ) : ZMod p) = c then k else 0) +
      (if (((b : ℕ) : ℤ) : ZMod p) = -c then k else 0)) = k * mu p b c := by
    intro b k; unfold mu; split_ifs <;> ring
  have e : ∀ S : Finset (Fin (m + 1)),
      (∑ b ∈ S, if (((b : ℕ) : ℤ) : ZMod p) = c then L b else 0) +
        (∑ b ∈ S, if (((b : ℕ) : ℤ) : ZMod p) = -c then L b else 0) = ∑ b ∈ S, L b * mu p b c := by
    intro S; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => key b (L b)
  have e2 := key s.1 s.2
  calc _ = ((∑ b ∈ Finset.univ.erase s.1, if (((b : ℕ) : ℤ) : ZMod p) = c then L b else 0) +
        (∑ b ∈ Finset.univ.erase s.1, if (((b : ℕ) : ℤ) : ZMod p) = -c then L b else 0)) +
        ((if (((s.1 : ℕ) : ℤ) : ZMod p) = c then (s.2 : ℕ) else 0) +
        (if (((s.1 : ℕ) : ℤ) : ZMod p) = -c then (s.2 : ℕ) else 0)) := by ring
    _ = ∑ b ∈ Finset.univ.erase s.1, L b * mu p b c + s.2 * mu p s.1 c := by rw [e, e2]
    _ = _ := by
      simp_rw [mu_eq hm]
      unfold nu
      by_cases h : ccls hm c = s.1
      · rw [if_pos h, if_pos h.symm, Finset.sum_eq_zero fun b hb => by
          rw [if_neg (fun h' => (Finset.mem_erase.mp hb).1 (h'.trans h)), mul_zero]]
        ring
      · rw [if_neg h, if_neg (Ne.symm h), mul_zero, add_zero,
          Finset.sum_eq_single_of_mem (ccls hm c) (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
            fun b _ hb => by rw [if_neg hb, mul_zero]]
        rw [if_pos rfl]; ring

lemma count_DN (N : ℕ) (c : ZMod p) :
    ((6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ))).filter fun γ : ℤ => (γ : ZMod p) = c).card +
      ((6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ))).filter fun γ : ℤ => (γ : ZMod p) = -c).card =
      6 * SX p N c := by
  unfold SX
  simp only [Multiset.filter_nsmul, Multiset.card_nsmul, Multiset.filter_map, Multiset.card_map]
  rw [mul_add]
  rfl

lemma card_plc_PlK (K : ℕ) (c : ZMod p) : (plc p (PlK K) c).card = SX p K c := by
  unfold plc PlK SX
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter (PlK_disjoint K)),
    Finset.filter_image, Finset.filter_image,
    Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_filter, Function.comp, Int.cast_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> [rw [← h2]; rw [h2]] <;> ring

lemma ccls_eq_zero_iff (hm : 2 * m + 1 = p) (c : ZMod p) : ccls hm c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have hs := ccls_spec hm c
    rw [h] at hs
    simp only [Fin.val_zero, Nat.cast_zero, Int.cast_zero] at hs
    rcases hs with h1 | h1
    · exact h1.symm
    · exact neg_eq_zero.mp h1.symm
  · rintro rfl
    unfold ccls
    rw [dif_pos (by simp)]
    ext; simp

/-- **The class counts** in terms of `Bse` and the row vanishing orders. -/
theorem classCount_eq (hm : 2 * m + 1 = p) (K N : ℕ) (L : Fin (m + 1) → ℕ)
    (s t : Σ a : Fin (m + 1), Fin (L a)) (c : ZMod p) :
    classCount p K (entryRoots N L s t) c =
      Bse p K N (ccls hm c) + (if ccls hm c = 0 then 2 else 1) *
        ((nu L s (ccls hm c) : ℚ) + nu L t (ccls hm c)) := by
  unfold classCount entryRoots Bse
  simp only [Multiset.filter_add, Multiset.card_add]
  have h1 := count_DN (p := p) N c
  have h2 := count_classRoots hm L s c
  have h3 := count_classRoots hm L t c
  rw [card_plc_PlK, ← SX_ccls hm N c, ← SX_ccls hm K c]
  have hz : ((if c = 0 then 5 else 0 : ℕ) : ℚ) = if (ccls hm c : ℕ) = 0 then 5 else 0 := by
    by_cases hc : c = 0
    · rw [if_pos hc, if_pos (by rw [(ccls_eq_zero_iff hm c).mpr hc]; rfl)]; norm_num
    · have hne : (ccls hm c : ℕ) ≠ 0 := fun h => hc ((ccls_eq_zero_iff hm c).mp (Fin.ext h))
      simp [hc, hne]
  have hz2 : ((if c = 0 then 2 else 1 : ℕ) : ℚ) = if ccls hm c = 0 then 2 else 1 := by
    by_cases hc : c = 0
    · rw [if_pos hc, if_pos ((ccls_eq_zero_iff hm c).mpr hc)]; norm_num
    · rw [if_neg hc, if_neg (fun h => hc ((ccls_eq_zero_iff hm c).mp h))]; norm_num
  have h1' : (((Multiset.filter (fun γ : ℤ => (γ : ZMod p) = c)
      (6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ)))).card : ℕ) : ℚ) +
      ((Multiset.filter (fun γ : ℤ => (γ : ZMod p) = -c)
      (6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ)))).card : ℕ) = 6 * (SX p N c : ℚ) := by
    exact_mod_cast h1
  have h2' := congrArg (fun x : ℕ => (x : ℚ)) h2
  have h3' := congrArg (fun x : ℕ => (x : ℚ)) h3
  simp only [Nat.cast_add, Nat.cast_mul] at h2' h3'
  rw [hz2] at h2' h3'
  push_cast
  rw [← hz]
  push_cast
  linarith

end ClassCount

section InnerWeights

variable {m : ℕ}

lemma tmin_le (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ) {c : Fin (m + 1)} (hc : c ≠ 0) :
    tmin hm L b ≤ topw L b c :=
  Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩)

end InnerWeights

section InnerAlloc

/-!
# The inner-range allocation (water filling)

Classes `c ≠ 0` with integer offsets `β c` (the row weights of class `c` are `i + β c / 2`).
At a level `k` (weights `< k/2`), class `c` receives `lrow k (β c) = ⌈(k - β c)/2⌉⁺` rows.
We take the largest feasible level `kf ∈ [klo, ktop]` (at most `h - L0min` rows used) and put the
remaining rows into the zero class. Then

* the allocation is valid for `inner_bound_cap` (the zero-class condition),
* `∑ wcap ≥ Φ(kf) - B₀`, with `Φ(k) = h k/2 - ∑_c ψ(k, β c)` concave in `k`,
* `Φ(kf) ≥ Φ(k) - (k - klo) L0min/2` for every `k ∈ [klo, ktop]`.
-/

open Finset


lemma lrow_ge (k β : ℤ) : ((k : ℚ) - β) / 2 ≤ lrow k β := by
  unfold lrow
  have h1 : (k - β + 1) / 2 ≤ ((k - β + 1) / 2).toNat := Int.self_le_toNat _
  have h2 : k - β ≤ 2 * ((k - β + 1) / 2) := by omega
  have h3 : ((k - β : ℤ) : ℚ) ≤ 2 * (((k - β + 1) / 2).toNat : ℤ) := by exact_mod_cast h2.trans (by omega)
  push_cast at h3
  linarith

lemma lrow_lt {k β : ℤ} {i : ℕ} (hi : i < lrow k β) : 2 * (i : ℚ) + β < k := by
  unfold lrow at hi
  have : 2 * (i : ℤ) + β < k := by omega
  exact_mod_cast this

lemma lrow_le_max (k β : ℤ) : (lrow k β : ℚ) + β / 2 ≤ max (β : ℚ) (k + 1) / 2 := by
  unfold lrow
  rcases le_or_gt (k - β + 1) 0 with h | h
  · have : ((k - β + 1) / 2).toNat = 0 := by omega
    rw [this]; push_cast
    have := le_max_left (β : ℚ) (k + 1); linarith
  · have e : (((k - β + 1) / 2).toNat : ℤ) ≤ (k - β + 1) / 2 := by omega
    have e2 : 2 * ((k - β + 1) / 2) ≤ k - β + 1 := by omega
    have e3 : ((((k - β + 1) / 2).toNat : ℤ) : ℚ) * 2 ≤ ((k - β + 1 : ℤ) : ℚ) := by
      exact_mod_cast (by omega : (((k - β + 1) / 2).toNat : ℤ) * 2 ≤ k - β + 1)
    push_cast at e3
    have := le_max_right (β : ℚ) (k + 1); linarith

lemma lrow_mono {k k' : ℤ} (h : k ≤ k') (β : ℤ) : lrow k β ≤ lrow k' β := by
  unfold lrow; omega

lemma lrow_succ (k β : ℤ) :
    lrow (k + 1) β = lrow k β ∨ (lrow (k + 1) β = lrow k β + 1 ∧ 2 * (lrow k β : ℤ) + β = k) := by
  unfold lrow; omega

/-- `ψ(k, β) = ∑_{i < lrow} (k/2 - i - β/2)`. -/
noncomputable def psiR (k β : ℤ) : ℚ := ∑ i ∈ range (lrow k β), (((k : ℚ) - 2 * i - β) / 2)

lemma psiR_succ (k β : ℤ) : psiR (k + 1) β = psiR k β + (lrow (k + 1) β : ℚ) / 2 := by
  unfold psiR
  rcases lrow_succ k β with h | ⟨h, h2⟩
  · rw [h, show (lrow k β : ℚ) / 2 = ∑ _i ∈ range (lrow k β), (1 / 2 : ℚ) by simp; ring,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring
  · rw [h, Finset.sum_range_succ]
    have h2' : 2 * ((lrow k β : ℕ) : ℚ) + β = k := by exact_mod_cast h2
    rw [show ((lrow k β + 1 : ℕ) : ℚ) / 2 = ∑ _i ∈ range (lrow k β), (1 / 2 : ℚ) + 1 / 2 by
      simp; ring]
    have : ∑ i ∈ range (lrow k β), (((k + 1 : ℤ) : ℚ) - 2 * i - β) / 2 =
        ∑ i ∈ range (lrow k β), ((((k : ℚ) - 2 * i - β) / 2) + 1 / 2) := by
      refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring
    rw [this, Finset.sum_add_distrib]
    push_cast
    linarith

variable {m : ℕ}

/-- `Φ(k) = h k / 2 - ∑ ψ`. -/
noncomputable def PhiK (β : Fin (m + 1) → ℤ) (h : ℕ) (k : ℤ) : ℚ :=
  (h : ℚ) * k / 2 - ∑ c ∈ univ.erase (0 : Fin (m + 1)), psiR k (β c)

lemma PhiK_succ (β : Fin (m + 1) → ℤ) (h : ℕ) (k : ℤ) :
    PhiK β h (k + 1) = PhiK β h k + ((h : ℚ) - rowsK β (k + 1)) / 2 := by
  unfold PhiK rowsK
  simp only [psiR_succ, Finset.sum_add_distrib, ← Finset.sum_div]
  push_cast
  ring

lemma rowsK_mono (β : Fin (m + 1) → ℤ) {k k' : ℤ} (h : k ≤ k') : rowsK β k ≤ rowsK β k' :=
  Finset.sum_le_sum fun c _ => lrow_mono h _

section
variable (β : Fin (m + 1) → ℤ) (h L0min : ℕ) (klo ktop : ℤ)

lemma kfSel_feasible (hlo : rowsK β klo + L0min ≤ h) :
    rowsK β (kfSel β h L0min klo ktop) + L0min ≤ h := by
  unfold kfSel
  have := Nat.findGreatest_spec (P := fun j : ℕ => rowsK β (klo + j) + L0min ≤ h)
    (n := (ktop - klo).toNat) (Nat.zero_le _) (by simpa using hlo)
  exact this

lemma kfSel_ge : klo ≤ kfSel β h L0min klo ktop := by unfold kfSel; omega

lemma kfSel_le (hk : klo ≤ ktop) : kfSel β h L0min klo ktop ≤ ktop := by
  unfold kfSel
  have := Nat.findGreatest_le (P := fun j : ℕ => rowsK β (klo + j) + L0min ≤ h)
    (n := (ktop - klo).toNat)
  omega

lemma kfSel_max {k : ℤ} (hk1 : kfSel β h L0min klo ktop < k) (hk2 : k ≤ ktop) :
    h < rowsK β k + L0min := by
  unfold kfSel at hk1
  have hj := Nat.findGreatest_is_greatest (P := fun j : ℕ => rowsK β (klo + j) + L0min ≤ h)
    (n := (ktop - klo).toNat) (k := (k - klo).toNat) (by omega) (by omega)
  simp only [not_le] at hj
  rwa [show klo + ((k - klo).toNat : ℤ) = k by omega] at hj

/-- **Concavity comparison**: `Φ(k) ≤ Φ(kf) + (k - klo) L0min / 2` on `[klo, ktop]`. -/
theorem PhiK_le_kf (hlo : rowsK β klo + L0min ≤ h) {k : ℤ} (hk1 : klo ≤ k) (hk2 : k ≤ ktop) :
    PhiK β h k ≤ PhiK β h (kfSel β h L0min klo ktop) + ((k - klo : ℤ) : ℚ) * L0min / 2 := by
  have hfeas := kfSel_feasible β h L0min klo ktop hlo
  have hge := kfSel_ge β h L0min klo ktop
  have hmax : ∀ k', kfSel β h L0min klo ktop < k' → k' ≤ ktop → h < rowsK β k' + L0min :=
    fun k' h1 h2 => kfSel_max β h L0min klo ktop h1 h2
  generalize kfSel β h L0min klo ktop = kf at *
  have hL0 : (0 : ℚ) ≤ L0min := by positivity
  rcases le_or_gt k kf with hle | hgt
  · -- below `kf` the steps are nonnegative
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, kf = k + t := ⟨(kf - k).toNat, by omega⟩
    have : ∀ s : ℕ, s ≤ t → PhiK β h k ≤ PhiK β h (k + s) := by
      intro s
      induction s with
      | zero => intro _; simp
      | succ s ih =>
        intro hs
        have := ih (by omega)
        rw [show k + ((s + 1 : ℕ) : ℤ) = (k + s) + 1 by push_cast; ring, PhiK_succ]
        have hr : rowsK β (k + s + 1) ≤ rowsK β (k + t) := rowsK_mono β (by omega)
        have : ((rowsK β (k + s + 1) : ℕ) : ℚ) ≤ h := by exact_mod_cast (by omega : rowsK β (k + s + 1) ≤ h)
        linarith
    have h1 := this t le_rfl
    have : (0 : ℚ) ≤ ((k - klo : ℤ) : ℚ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ k - klo)
    nlinarith
  · -- above `kf` each step is less than `L0min / 2`
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = kf + t := ⟨(k - kf).toNat, by omega⟩
    have : ∀ s : ℕ, s ≤ t → PhiK β h (kf + s) ≤ PhiK β h kf + (s : ℚ) * L0min / 2 := by
      intro s
      induction s with
      | zero => intro _; simp
      | succ s ih =>
        intro hs
        have := ih (by omega)
        rw [show kf + ((s + 1 : ℕ) : ℤ) = (kf + s) + 1 by push_cast; ring, PhiK_succ]
        have hr := hmax (kf + s + 1) (by omega) (by omega)
        have : (h : ℚ) < rowsK β (kf + s + 1) + L0min := by exact_mod_cast hr
        push_cast
        linarith
    have h1 := this t le_rfl
    have : (t : ℚ) ≤ ((kf + t - klo : ℤ) : ℚ) := by
      have : ((t : ℤ) : ℚ) ≤ ((kf + t - klo : ℤ) : ℚ) := by exact_mod_cast (by omega)
      simpa using this
    nlinarith
end

lemma sum_allocK (β : Fin (m + 1) → ℤ) (h : ℕ) (kf : ℤ) (hkf : rowsK β kf ≤ h) :
    ∑ c, allocK β h kf c = h := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
  unfold allocK
  rw [if_pos rfl, Finset.sum_congr rfl (fun c hc => if_neg (Finset.mem_erase.mp hc).1)]
  unfold rowsK at hkf ⊢
  omega

/-- The zero-class deficit: `∑_{i<L} (D - 2i)⁺ ≤ D⁺ (D⁺/2 + 1)`. -/
lemma sum_deficit_le (D : ℚ) (L : ℕ) :
    ∑ i ∈ range L, max 0 (D - 2 * i) ≤ max 0 D * (max 0 D / 2 + 1) := by
  set E := max 0 D with hE
  have hE0 : 0 ≤ E := le_max_left _ _
  set N0 := ⌊E / 2⌋₊ + 1 with hN0
  have hz : ∀ i, N0 ≤ i → max 0 (D - 2 * i) = 0 := by
    intro i hi
    have : E / 2 < (N0 : ℚ) := by rw [hN0]; push_cast; exact Nat.lt_floor_add_one _
    have : (N0 : ℚ) ≤ i := by exact_mod_cast hi
    apply max_eq_left
    have := le_max_right 0 D; linarith
  have h1 : ∑ i ∈ range L, max 0 (D - 2 * i) ≤ ∑ i ∈ range N0, max 0 (D - 2 * i) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show min L N0 ≤ L from min_le_left _ _),
      ← Finset.sum_range_add_sum_Ico _ (show min L N0 ≤ N0 from min_le_right _ _)]
    have hA : ∑ i ∈ Ico (min L N0) L, max 0 (D - 2 * (i : ℚ)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => hz i ?_
      have := Finset.mem_Ico.mp hi; omega
    have hB : 0 ≤ ∑ i ∈ Ico (min L N0) N0, max 0 (D - 2 * (i : ℚ)) :=
      Finset.sum_nonneg fun _ _ => le_max_left _ _
    linarith
  have h2 : ∑ i ∈ range N0, max 0 (D - 2 * (i : ℚ)) ≤ ∑ _i ∈ range N0, E :=
    Finset.sum_le_sum fun i _ => max_le hE0 (by
      have h1 := le_max_right (0 : ℚ) D
      have h2 : (0 : ℚ) ≤ (i : ℚ) := by positivity
      rw [hE]; linarith)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  have h3 : (N0 : ℚ) ≤ E / 2 + 1 := by
    rw [hN0]; push_cast; have := Nat.floor_le (show 0 ≤ E / 2 by positivity); linarith
  nlinarith

section
variable (hm1 : 1 ≤ m) (b : ℕ → ℚ) (β : Fin (m + 1) → ℤ)
  (hβ : ∀ c : Fin (m + 1), c ≠ 0 → b c = (β c : ℚ) + 4)

include hβ in
lemma tmin_allocK_ge (h : ℕ) (kf : ℤ) : (kf : ℚ) / 2 ≤ tmin hm1 (allocK β h kf) b := by
  unfold tmin
  refine Finset.le_inf' _ _ fun c hc => ?_
  have hc0 := (Finset.mem_erase.mp hc).1
  unfold topw allocK
  rw [if_neg hc0, hβ c hc0]
  have := lrow_ge kf (β c)
  linarith

include hβ in
lemma tmin_allocK_le (h : ℕ) (kf : ℤ) :
    tmin hm1 (allocK β h kf) b ≤ max (β ⟨1, by omega⟩ : ℚ) (kf + 1) / 2 := by
  have hc : (⟨1, by omega⟩ : Fin (m + 1)) ≠ 0 := by simp [Fin.ext_iff]
  refine (tmin_le hm1 _ b hc).trans ?_
  unfold topw allocK
  rw [if_neg hc, hβ _ hc]
  have := lrow_le_max kf (β ⟨1, by omega⟩)
  linarith

include hβ in
/-- **The weight sum of the allocation**: `∑ wcap ≥ Φ(kf) - B₀`. -/
theorem sum_wcap_allocK (h : ℕ) (kf : ℤ) (hkf : rowsK β kf ≤ h) :
    PhiK β h kf - max 0 ((kf : ℚ) / 2 - (b 0 - 4) / 2) *
        (max 0 ((kf : ℚ) / 2 - (b 0 - 4) / 2) / 2 + 1) ≤
      ∑ s, wcap hm1 (allocK β h kf) b s := by
  set L := allocK β h kf with hL
  set T := tmin hm1 L b with hT
  have hTge : (kf : ℚ) / 2 ≤ T := tmin_allocK_ge hm1 b β hβ h kf
  rw [Fintype.sum_sigma]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
  -- nonzero classes
  have hnz : ∀ c ∈ univ.erase (0 : Fin (m + 1)), ∑ i : Fin (L c), wcap hm1 L b ⟨c, i⟩ =
      ∑ i ∈ range (lrow kf (β c)), ((i : ℚ) + (β c : ℚ) / 2) := by
    intro c hc
    have hc0 := (Finset.mem_erase.mp hc).1
    have hLc : L c = lrow kf (β c) := by rw [hL]; unfold allocK; rw [if_neg hc0]
    have hpt : ∀ i : Fin (L c), wcap hm1 L b ⟨c, i⟩ = ((i : ℕ) : ℚ) + (β c : ℚ) / 2 := by
      intro i
      unfold wcap wraw
      simp only
      rw [if_neg hc0, hβ c hc0, show ((β c : ℚ) + 4 - 4) / 2 = (β c : ℚ) / 2 by ring]
      apply min_eq_left
      have hi : (i : ℕ) < lrow kf (β c) := hLc ▸ i.isLt
      have := lrow_lt hi
      linarith [hTge, hT]
    rw [Finset.sum_congr rfl (fun i _ => hpt i),
      Fin.sum_univ_eq_sum_range (fun i => (i : ℚ) + (β c : ℚ) / 2) (L c), hLc]
  -- the zero class
  have hz : ((L 0 : ℕ) : ℚ) * kf / 2 - max 0 ((kf : ℚ) / 2 - (b 0 - 4) / 2) *
        (max 0 ((kf : ℚ) / 2 - (b 0 - 4) / 2) / 2 + 1) ≤
      ∑ i : Fin (L 0), wcap hm1 L b ⟨0, i⟩ := by
    have hpt : ∀ i : Fin (L 0), (kf : ℚ) / 2 - max 0 ((kf : ℚ) / 2 - (b 0 - 4) / 2 - 2 * (i : ℕ)) ≤
        wcap hm1 L b ⟨0, i⟩ := by
      intro i
      unfold wcap wraw
      simp only [ite_true]
      refine le_min ?_ ?_
      · have := le_max_right (0 : ℚ) ((kf : ℚ) / 2 - (b 0 - 4) / 2 - 2 * (i : ℕ)); linarith
      · have := le_max_left (0 : ℚ) ((kf : ℚ) / 2 - (b 0 - 4) / 2 - 2 * (i : ℕ)); linarith [hTge, hT]
    refine le_trans ?_ (Finset.sum_le_sum fun i _ => hpt i)
    rw [Fin.sum_univ_eq_sum_range (fun i => (kf : ℚ) / 2 - max 0 ((kf : ℚ) / 2 - (b 0 - 4) / 2 -
      2 * (i : ℚ))) (L 0), Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have := sum_deficit_le ((kf : ℚ) / 2 - (b 0 - 4) / 2) (L 0)
    linarith
  rw [Finset.sum_congr rfl hnz]
  have hL0 : L 0 = h - rowsK β kf := by rw [hL]; unfold allocK; rw [if_pos rfl]
  have hL0q : ((L 0 : ℕ) : ℚ) = (h : ℚ) - rowsK β kf := by rw [hL0]; push_cast [hkf]; ring
  have hpsi : ∀ c ∈ univ.erase (0 : Fin (m + 1)), psiR kf (β c) =
      (lrow kf (β c) : ℚ) * kf / 2 - ∑ i ∈ range (lrow kf (β c)), ((i : ℚ) + (β c : ℚ) / 2) := by
    intro c _
    unfold psiR
    rw [show (lrow kf (β c) : ℚ) * kf / 2 = ∑ _i ∈ range (lrow kf (β c)), (kf : ℚ) / 2 by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hΦ : PhiK β h kf = (h : ℚ) * kf / 2 - ((rowsK β kf : ℕ) : ℚ) * kf / 2 +
      ∑ c ∈ univ.erase (0 : Fin (m + 1)), ∑ i ∈ range (lrow kf (β c)), ((i : ℚ) + (β c : ℚ) / 2) := by
    unfold PhiK
    rw [Finset.sum_congr rfl hpsi, Finset.sum_sub_distrib]
    unfold rowsK
    push_cast
    rw [Finset.sum_mul, Finset.sum_div]
    ring
  rw [hΦ]
  rw [hL0q] at hz
  linarith

end

end InnerAlloc

section Normalization

/-!
# The normalisation `m_{K,M}` of Section 5

We define the local exponents `L_p(K, M)` of (5.1) exactly as in the paper (with the counts
`ℓ_A(a)`, the allocation `T, E, ε_a, L_a`, the weights (4.6)–(4.7), the inner exponent
`γ_p^in` (4.8), the outer exponent `γ_p^out` (4.14)) and the normalising factor
`m_{K,M} = ∏_{p ≤ 2h} p^{-L_p}` of (5.2).

These are the paper's definitions, kept for reference and for `vS` (used by `Apery.Legendre`).
The normalisation actually used in the proof is `Apery.mN` (`Apery/Norm.lean`), whose local
exponents are the bounds proved in `Apery/Arith`.
-/

open Finset Polynomial


/-- `ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ ±a (mod p)}`. -/
def ellA (p A a : ℕ) : ℕ := ((Icc 1 A).filter fun j => j % p = a % p ∨ (j + a) % p = 0).card

/-- The parameters of Section 4.1 for `K = 40 n`, `N = 3 n`, `h = 37 n`, cutoff `M`, prime `p`. -/
structure InnerData where
  n : ℕ
  M : ℕ
  p : ℕ

namespace InnerData

variable (D : InnerData)

def K : ℕ := 40 * D.n
def N : ℕ := 3 * D.n
def h : ℕ := 37 * D.n
def L0 : ℕ := 4 * D.M + 10
/-- `m = (p - 1)/2`. -/
def m : ℕ := (D.p - 1) / 2
def mN : ℕ := D.N / D.p
def mK : ℕ := D.K / D.p
def ellK (a : ℕ) : ℕ := ellA D.p D.K a
def ellN (a : ℕ) : ℕ := ellA D.p D.N a
/-- `b_a = 3 ℓ_N(a)`. -/
def b (a : ℕ) : ℕ := 3 * D.ellN a
/-- The total number of ordinary rows `h - L₀ + 3(N - m_N)` (as an integer). -/
def total : ℤ := (D.h : ℤ) - D.L0 + 3 * ((D.N : ℤ) - D.mN)
/-- `T` of (4.4). -/
def T : ℤ := D.total / D.m
/-- `E` of (4.4). -/
def E : ℤ := D.total % D.m
/-- The rank of the class `a` in decreasing order of `ℓ_K` (ties broken by the index). -/
def rank (a : ℕ) : ℕ :=
  ((Icc 1 D.m).filter fun c => D.ellK c > D.ellK a ∨ (D.ellK c = D.ellK a ∧ c < a)).card
/-- `ε_a = 1` for the first `E` classes in decreasing order of `ℓ_K(a)`. -/
def eps (a : ℕ) : ℤ := if (D.rank a : ℤ) < D.E then 1 else 0
/-- `L_a = T - b_a + ε_a`. -/
def L (a : ℕ) : ℤ := D.T - D.b a + D.eps a
/-- `Z_a = T + ε_a`. -/
def Z (a : ℕ) : ℤ := D.T + D.eps a
/-- The row weights (4.6) for `a > 0` (as rationals, they are half-integers). -/
def w (a : ℕ) (i : ℤ) : ℚ := i + D.b a - ((D.ellK a : ℚ) + 4) / 2
/-- The minimum over the ordinary classes in (4.7). -/
def w0min : ℚ :=
  if hm : 1 ≤ D.m then
    ((Icc 1 D.m).image fun c => (D.Z c : ℚ) - ((D.ellK c : ℚ) + 4) / 2).min'
      (by simpa using hm)
  else 0
/-- The zero-block weights (4.7). -/
def w0 (i : ℤ) : ℚ := min (2 * i + 6 * (D.mN : ℚ) - D.mK + 1 / 2) D.w0min
/-- The inner exponent `γ_p^in` of (4.8) (an integer; we take the floor of the rational sum). -/
def gammaIn : ℤ :=
  ⌊2 * ((∑ i ∈ range D.L0, D.w0 i) + ∑ a ∈ Icc 1 D.m, ∑ i ∈ range (D.L a).toNat, D.w a i)⌋

/-! ### The outer range (4.14) -/

/-- `v = K - p ⌊K/p⌋`. -/
def v : ℕ := D.K % D.p
def u : ℤ := max 0 ((D.N : ℤ) + D.v - D.p + 1)
def tp : ℤ := min (D.N : ℤ) D.v + D.u
def rp : ℤ := max 0 ((D.K : ℤ) + 4 * D.N - 2 * D.p + 2)
/-- The outer exponent `γ_p^out` of (4.14) (`0` for `p > K`). -/
def gammaOut : ℤ :=
  if D.K < D.p then 0
  else if D.K < 2 * D.p then
    -7 * ((D.K : ℤ) - D.p) + 6 * D.tp - 1 - min D.rp ((D.p : ℤ) - 1 - D.N + D.u)
  else -7 * ((D.K : ℤ) - D.p) + 3 + 12 * D.N + 5 * D.tp - min D.rp ((D.p : ℤ) + D.u)

/-- `v_p(S_K)`. -/
noncomputable def vS : ℤ := padicValRat D.p (S D.n)

/-- The local exponent `L_p(K, M)` of (5.1). -/
noncomputable def Lp : ℤ :=
  if D.p * D.M ≤ D.K then -6 * (D.h : ℤ) * Nat.log D.p (5 * D.K) - D.h * padicValNat D.p 24
  else if 3 * D.p ≤ D.K then D.vS + D.gammaIn
  else D.vS + D.gammaOut

end InnerData

/-- The normalising factor `m_{K,M} = ∏_{p ≤ 2h} p^{-L_p(K,M)}` of (5.2). -/
noncomputable def mKM (n M : ℕ) : ℚ :=
  ∏ p ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime,
    (p : ℚ) ^ (-(InnerData.mk n M p).Lp)

lemma mKM_pos (n M : ℕ) : 0 < mKM n M := by
  unfold mKM
  apply Finset.prod_pos
  intro p hp
  have : 0 < p := (Finset.mem_filter.mp hp).2.pos
  exact zpow_pos (by exact_mod_cast this) _

end Normalization

section Legendre

/-!
# The `p`-adic valuation of `S_K` (5.3)

`v_p(S_K) = 2h v_p(K!) - 12h v_p(N!) - 2 ∑_{i=1}^{h-1} v_p((2i)!) + (h-1) v_p(4)`,
where each factorial valuation is given by Legendre's formula (`padicValNat_factorial`).
-/

open Finset


lemma padicValNat_finset_prod (p : ℕ) [hp : Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul (hf a (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `S_K` as a quotient of natural numbers. -/
lemma S_eq_div (n : ℕ) :
    S n = (((40 * n).factorial ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) : ℕ) : ℚ) /
      (((3 * n).factorial ^ (12 * (37 * n)) * ∏ i ∈ Icc 1 (37 * n - 1), (2 * i).factorial ^ 2 : ℕ) : ℚ) := by
  unfold S
  push_cast
  ring

/-- **(5.3)**: the valuation of `S_K` in terms of factorial valuations. -/
theorem vS_eq {n : ℕ} (hn : 0 < n) {p : ℕ} (hp : p.Prime) :
    (InnerData.mk n 200 p).vS =
      2 * (37 * n : ℤ) * padicValNat p (40 * n).factorial -
        12 * (37 * n : ℤ) * padicValNat p (3 * n).factorial -
        2 * ∑ i ∈ Icc 1 (37 * n - 1), (padicValNat p (2 * i).factorial : ℤ) +
        ((37 * n : ℤ) - 1) * padicValNat p 4 := by
  have := Fact.mk hp
  unfold InnerData.vS
  rw [S_eq_div]
  have hA : (((40 * n).factorial ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) : ℕ) : ℚ) ≠ 0 := by
    norm_cast; positivity
  have hB : (((3 * n).factorial ^ (12 * (37 * n)) *
      ∏ i ∈ Icc 1 (37 * n - 1), (2 * i).factorial ^ 2 : ℕ) : ℚ) ≠ 0 := by
    norm_cast
    apply mul_ne_zero (by positivity)
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  rw [padicValRat.div hA hB, ← padicValRat_of_nat, ← padicValRat_of_nat,
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (Finset.prod_ne_zero_iff.mpr fun i _ => by positivity),
    padicValNat.pow, padicValNat.pow, padicValNat.pow,
    padicValNat_finset_prod p _ _ (fun i _ => by positivity)]
  simp only [padicValNat.pow]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ 37 * n)]
  push_cast
  simp only [Finset.mul_sum]
  ring

end Legendre

section ClassSum

/-!
# Class sums and their continuous limits

For `p = 2m + 1` and `0 ≤ v, v' < p` put, for `1 ≤ c ≤ m`,
`a_c = [c ≤ v] + [p - v ≤ c]` and `a'_c = [c ≤ v'] + [p - v' ≤ c]`.
Every function `h` of `(a_c, a'_c)` is a combination of the products of the interval indicators
`1 = [1 ≤ c ≤ m]`, `A = [c ≤ v]`, `E = [p - v ≤ c]`, so `∑_c h(a_c, a'_c)` is a combination of
nine interval counts. Each count is within `5/2` of `p` times its continuous analogue, where
`v/p = f`, `v'/p = g`.

We also prove `SX p X c = 2 ⌊X/p⌋ + a_c(X mod p)`.
-/

open Finset


/-- The interval `[lo i, hi i]` of the indicator `i ∈ {1, A, E}`. -/
def ivLo (p v : ℕ) : Fin 3 → ℕ := ![1, 1, p - v]
def ivHi (m v : ℕ) : Fin 3 → ℕ := ![m, v, m]

/-- The continuous intervals. -/
noncomputable def cvLo (f : ℝ) : Fin 3 → ℝ := ![0, 0, 1 - f]
noncomputable def cvHi (f : ℝ) : Fin 3 → ℝ := ![1 / 2, f, 1 / 2]

/-- The coefficients of `h` in the basis `1, A, E`. -/
def bcoef (h : ℕ → ℝ) : Fin 3 → ℝ := ![h 0, h 1 - h 0, h 2 - h 1]

/-- `a(c) = [c ≤ v] + [p - v ≤ c]`. -/
def aCnt (p v c : ℕ) : ℕ := (if c ≤ v then 1 else 0) + (if p - v ≤ c then 1 else 0)

/-- The interval indicator. -/
def ivInd (p m v : ℕ) (i : Fin 3) (c : ℕ) : ℝ :=
  if ivLo p v i ≤ c ∧ c ≤ ivHi m v i then 1 else 0

lemma expand_one {p m v c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hc1 : 1 ≤ c) (hcm : c ≤ m)
    (h : ℕ → ℝ) : h (aCnt p v c) = ∑ i, bcoef h i * ivInd p m v i c := by
  simp only [Fin.sum_univ_three, bcoef, ivInd, ivLo, ivHi, aCnt, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  by_cases h1 : c ≤ v <;> by_cases h2 : p - v ≤ c
  · simp [h1, h2, hc1, hcm]
  · simp [h1, h2, hc1, hcm]
  · exfalso; omega
  · simp [h1, h2, hc1, hcm]

lemma expand_two {p m v v' c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p) (hc1 : 1 ≤ c)
    (hcm : c ≤ m) (h : ℕ → ℕ → ℝ) :
    h (aCnt p v c) (aCnt p v' c) =
      ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i * (ivInd p m v i c * ivInd p m v' j c) := by
  rw [expand_one hm hv hc1 hcm (fun a => h a (aCnt p v' c))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ a, h a (aCnt p v' c) = ∑ j, bcoef (fun b => h a b) j * ivInd p m v' j c :=
    fun a => expand_one hm hv' hc1 hcm (fun b => h a b)
  simp only [e]
  simp only [bcoef, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  fin_cases i <;> simp <;> ring

/-- The discrete count of an intersection of two intervals within `[1, m]`. -/
lemma card_two_intervals (m lo hi lo' hi' : ℕ) :
    ((Icc 1 m).filter fun c => (lo ≤ c ∧ c ≤ hi) ∧ (lo' ≤ c ∧ c ≤ hi')).card =
      min (min hi hi') m + 1 - max (max lo lo') 1 := by
  have : (Icc 1 m).filter (fun c => (lo ≤ c ∧ c ≤ hi) ∧ (lo' ≤ c ∧ c ≤ hi')) =
      Icc (max (max lo lo') 1) (min (min hi hi') m) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]

/-- **Class sums as interval counts.** -/
theorem class_sum {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (h : ℕ → ℕ → ℝ) :
    ∑ c ∈ Icc 1 m, h (aCnt p v c) (aCnt p v' c) =
      ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i *
        ((min (min (ivHi m v i) (ivHi m v' j)) m + 1 - max (max (ivLo p v i) (ivLo p v' j)) 1 : ℕ) : ℝ) := by
  rw [Finset.sum_congr rfl fun c hc => expand_two hm hv hv' (Finset.mem_Icc.mp hc).1
    (Finset.mem_Icc.mp hc).2 h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, ← card_two_intervals]
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ivInd]
  split_ifs <;> simp_all

/-- The continuous analogue of an interval count. -/
noncomputable def ccount (f g : ℝ) (i j : Fin 3) : ℝ :=
  max 0 (min (min (cvHi f i) (cvHi g j)) (1 / 2) - max (max (cvLo f i) (cvLo g j)) 0)

lemma cast_trunc_sub (a b : ℕ) : ((a - b : ℕ) : ℝ) = max 0 ((a : ℝ) - b) := by
  rcases le_or_gt b a with h | h
  · have h' : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.cast_sub h, max_eq_right (by linarith)]
  · have h' : (a : ℝ) < b := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h.le, max_eq_left (by linarith)]
    simp

lemma abs_max0_sub (u w : ℝ) : |max 0 u - max 0 w| ≤ |u - w| := by
  have := abs_max_sub_max_le_max (0 : ℝ) u 0 w
  simpa using this

lemma hi_approx {p m v : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (i : Fin 3) :
    |(ivHi m v i : ℝ) - p * cvHi ((v : ℝ) / p) i| ≤ 1 / 2 := by
  have hp : (0 : ℝ) < p := by have : 0 < p := by omega
                              exact_mod_cast this
  have hmR : (m : ℝ) = (p - 1) / 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) = p := by exact_mod_cast hm
    push_cast at this; linarith
  fin_cases i <;> simp [ivHi, cvHi, hmR]
  · rw [abs_le]; constructor <;> linarith
  · rw [mul_div_cancel₀ _ hp.ne']; simp
  · rw [abs_le]; constructor <;> linarith

lemma lo_approx {p v : ℕ} (hv : v < p) (i : Fin 3) :
    |(ivLo p v i : ℝ) - p * cvLo ((v : ℝ) / p) i| ≤ 1 := by
  have hp : (0 : ℝ) < p := by have : 0 < p := by omega
                              exact_mod_cast this
  fin_cases i <;> simp [ivLo, cvLo]
  rw [Nat.cast_sub hv.le, mul_sub, mul_one, mul_div_cancel₀ _ hp.ne']
  simp

/-- **Each interval count is within `5/2` of `p` times its continuous analogue.** -/
lemma count_approx {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p) (i j : Fin 3) :
    |((min (min (ivHi m v i) (ivHi m v' j)) m + 1 - max (max (ivLo p v i) (ivLo p v' j)) 1 : ℕ) : ℝ) -
      (p : ℝ) * ccount ((v : ℝ) / p) ((v' : ℝ) / p) i j| ≤ 5 / 2 := by
  have hp : (0 : ℝ) < p := by have : 0 < p := by omega
                              exact_mod_cast this
  have hmR : (m : ℝ) = (p - 1) / 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) = p := by exact_mod_cast hm
    push_cast at this; linarith
  rw [cast_trunc_sub]
  unfold ccount
  rw [mul_max_of_nonneg _ _ hp.le, mul_zero, mul_sub, mul_min_of_nonneg _ _ hp.le,
    mul_min_of_nonneg _ _ hp.le, mul_max_of_nonneg _ _ hp.le, mul_max_of_nonneg _ _ hp.le, mul_zero]
  refine (abs_max0_sub _ _).trans ?_
  push_cast
  have h1 : |min (min (ivHi m v i : ℝ) (ivHi m v' j)) m -
      min (min (p * cvHi ((v : ℝ) / p) i) (p * cvHi ((v' : ℝ) / p) j)) (p * (1 / 2))| ≤ 1 / 2 := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (hi_approx hm hv i) (hi_approx hm hv' j))
    · rw [hmR, abs_le]; constructor <;> linarith
  have h2 : |max (max (ivLo p v i : ℝ) (ivLo p v' j)) 1 -
      max (max (p * cvLo ((v : ℝ) / p) i) (p * cvLo ((v' : ℝ) / p) j)) 0| ≤ 1 := by
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ (by norm_num))
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (lo_approx hv i) (lo_approx hv' j))
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Class sums versus their continuous limit.** -/
theorem class_sum_approx {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (h : ℕ → ℕ → ℝ) :
    |∑ c ∈ Icc 1 m, h (aCnt p v c) (aCnt p v' c) -
      (p : ℝ) * ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i *
        ccount ((v : ℝ) / p) ((v' : ℝ) / p) i j| ≤
      5 / 2 * ∑ i, ∑ j, |bcoef (fun a => bcoef (fun b => h a b) j) i| := by
  rw [class_sum hm hv hv', Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_left_comm, ← mul_sub, abs_mul, mul_comm (5 / 2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (count_approx hm hv hv' i j) (abs_nonneg _)

end ClassSum

section ClassData

/-!
# Class data and `v_p(S_K)` in the inner and outer ranges

* `SX p X c = 2 ⌊X/p⌋ + a_c(X mod p)` for `1 ≤ c ≤ m`;
* `-v_p(S_K) ≤ -2h⌊K/p⌋ + 12h⌊N/p⌋ + 2 ∑_{j ≥ 1} (h - jp/2)⁺` when `p² > max(2h, N)`, `p` odd.
-/

open Finset


variable {p : ℕ} [hp : Fact p.Prime]

lemma succ_mod_cases (X q : ℕ) (hq : 0 < q) :
    ((X + 1) % q = X % q + 1 ∧ (X + 1) / q = X / q) ∨
      (X % q = q - 1 ∧ (X + 1) % q = 0 ∧ (X + 1) / q = X / q + 1) := by
  have h := Nat.div_add_mod X q
  have hl := Nat.mod_lt X hq
  rcases Nat.lt_or_ge (X % q + 1) q with h1 | h1
  · left
    have : (X + 1) / q = X / q ∧ (X + 1) % q = X % q + 1 :=
      (Nat.div_mod_unique hq).mpr ⟨by linarith, h1⟩
    exact ⟨this.2, this.1⟩
  · right
    have hb : X % q = q - 1 := by omega
    have : (X + 1) / q = X / q + 1 ∧ (X + 1) % q = 0 :=
      (Nat.div_mod_unique hq).mpr ⟨by rw [Nat.mul_add, mul_one]; omega, hq⟩
    exact ⟨hb, this.2, this.1⟩

lemma count_res (r : ℕ) (hr1 : 1 ≤ r) (hrp : r < p) (X : ℕ) :
    ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = ((r : ℤ) : ZMod p)).card =
      X / p + (if r ≤ X % p then 1 else 0) := by
  have hp0 : 0 < p := by omega
  induction X with
  | zero => simp; omega
  | succ X ih =>
    rw [← insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
    have hiff : ((((X + 1 : ℕ) : ℤ) : ZMod p) = ((r : ℤ) : ZMod p)) ↔ (X + 1) % p = r := by
      rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hrp]
    have hnot : X + 1 ∉ (Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = ((r : ℤ) : ZMod p) := by
      simp
    rcases succ_mod_cases X p hp0 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · by_cases h : (X + 1) % p = r
      · rw [if_pos (hiff.mpr h), Finset.card_insert_of_notMem hnot, ih, h2]
        split_ifs <;> omega
      · rw [if_neg (fun h' => h (hiff.mp h')), ih, h2]
        split_ifs <;> omega
    · rw [if_neg (fun h' => by have := hiff.mp h'; omega), ih, h3, h2, h1]
      split_ifs <;> omega

/-- **`SX` on a class**: `SX p X c = 2 ⌊X/p⌋ + a_c(X mod p)`. -/
lemma SX_class {m : ℕ} (hm : 2 * m + 1 = p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ m) (X : ℕ) :
    SX p X (((c : ℕ) : ℤ) : ZMod p) = 2 * (X / p) + aCnt p (X % p) c := by
  unfold SX aCnt
  have hneg : -(((c : ℕ) : ℤ) : ZMod p) = (((p - c : ℕ) : ℤ) : ZMod p) := by
    rw [Nat.cast_sub (by omega), Int.cast_sub]; simp
  rw [hneg, count_res c hc1 (by omega) X, count_res (p - c) (by omega) (by omega) X]
  have := Nat.mod_lt X (show 0 < p by omega)
  split_ifs <;> omega

lemma SX_zero (X : ℕ) : SX p X 0 = 2 * (X / p) := by
  unfold SX
  have h : ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = 0).card = X / p := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div X p]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Int.cast_natCast,
      ZMod.natCast_eq_zero_iff]
    omega
  rw [neg_zero, h]; ring

/-! ### `v_p(S_K)` -/

lemma padicValNat_factorial_ge {k : ℕ} : k / p ≤ padicValNat p k.factorial := by
  rcases Nat.lt_or_ge k p with h | h
  · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
  · rw [padicValNat_factorial (b := Nat.log p k + 1) (by omega)]
    have h1 : 1 ∈ Ico 1 (Nat.log p k + 1) := by
      simp only [Finset.mem_Ico]
      exact ⟨le_rfl, by have := Nat.log_pos hp.out.one_lt h; omega⟩
    have := Finset.single_le_sum (f := fun i => k / p ^ i) (fun i _ => Nat.zero_le _) h1
    simpa using this

lemma padicValNat_factorial_small {k : ℕ} (hk : k < p ^ 2) : padicValNat p k.factorial = k / p := by
  rw [padicValNat_factorial (b := 2)]
  · simp
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp
    · exact Nat.log_lt_of_lt_pow h0.ne' hk

/-- The layer-cake function `T(t) = ∑_{j ≤ J} (t - j p/2)⁺`. -/
noncomputable def layer (p J : ℕ) (t : ℝ) : ℝ := ∑ j ∈ Icc 1 J, max 0 (t - j * p / 2)

lemma layer_step (J : ℕ) (i : ℕ) (hJ : 2 * i / p ≤ J) :
    ((2 * i / p : ℕ) : ℝ) ≤ layer p J (i + 1) - layer p J i := by
  unfold layer
  rw [← Finset.sum_sub_distrib]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  calc ((2 * i / p : ℕ) : ℝ) = ∑ j ∈ Icc 1 J, (if j * p ≤ 2 * i then (1 : ℝ) else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
        have : (Icc 1 J).filter (fun j => j * p ≤ 2 * i) = Icc 1 (2 * i / p) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, (Nat.le_div_iff_mul_le hp.out.pos).mpr h3⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hJ⟩, (Nat.le_div_iff_mul_le hp.out.pos).mp h2⟩
        rw [this, Nat.card_Icc]; simp
    _ ≤ _ := by
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs with h
        · have h' : (j : ℝ) * p ≤ 2 * i := by exact_mod_cast h
          rw [max_eq_right (by push_cast; linarith), max_eq_right (by linarith)]
          push_cast; linarith
        · have := le_max_left (0 : ℝ) ((i : ℝ) + 1 - j * p / 2)
          have := max_le_max (le_refl (0 : ℝ)) (show (i : ℝ) - j * p / 2 ≤ (i : ℝ) + 1 - j * p / 2 by linarith)
          push_cast at *
          linarith

/-- **Layer cake**: `∑_{i < H} ⌊2i/p⌋ ≤ ∑_{j ≤ J} (H - jp/2)⁺` if `2H ≤ Jp`. -/
lemma sum_floor_le_layer (J H : ℕ) (hJ : 2 * H ≤ J * p) :
    (∑ i ∈ range H, ((2 * i / p : ℕ) : ℝ)) ≤ layer p J H := by
  have h0 : layer p J 0 = 0 := by
    unfold layer
    refine Finset.sum_eq_zero fun j hj => ?_
    have := (Finset.mem_Icc.mp hj).1
    have : (0 : ℝ) ≤ j * p / 2 := by positivity
    exact max_eq_left (by linarith)
  have : ∀ H' ≤ H, (∑ i ∈ range H', ((2 * i / p : ℕ) : ℝ)) ≤ layer p J H' := by
    intro H'
    induction H' with
    | zero => intro _; simp [h0]
    | succ H' ih =>
      intro hH
      rw [Finset.sum_range_succ]
      have := ih (by omega)
      have hstep := layer_step J H' (by
        rw [Nat.div_le_iff_le_mul_add_pred hp.out.pos]
        nlinarith [hp.out.pos])
      push_cast at hstep ⊢
      linarith
  exact this H le_rfl

end ClassData

section InnerPrime

/-!
# The inner range: a per-prime upper bound for `-L_p`

For `K/400 < p ≤ K/3` (and `n` large enough for the side conditions), every level `k` in
`[klo, ktop]` gives
`-L_p ≤ -2h q + 12h q' + 2 T(h) - h k + 2 ∑_{c=1}^m ψ(k, B + 6a'_c - a_c) + (k - klo) L₀ + 2B₀ + 1`,
with `q = ⌊K/p⌋`, `q' = ⌊N/p⌋`, `B = 12q' - 2q - 4`, the class counts `a_c, a'_c` of
`ClassSum`, and the layer-cake function `T`.
-/

open Finset


variable {p : ℕ} [hp : Fact p.Prime]

lemma sum_erase_zero_eq_Icc {m : ℕ} (F : ℕ → ℚ) :
    ∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, F c = ∑ c ∈ Icc 1 m, F c := by
  have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun c => F c) (Finset.mem_univ 0)
  rw [Fin.sum_univ_eq_sum_range (fun c => F c), Finset.sum_range_eq_add_Ico _ (by omega)] at h1
  simp only [Fin.val_zero] at h1
  have h2 : Ico 1 (m + 1) = Icc 1 m := by ext c; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [h2] at h1
  linarith

/-- `-v_p(S_K)` in the inner and outer ranges. -/
lemma neg_vSK_le {n : ℕ} (hn : 1 ≤ n) (hp3 : 3 ≤ p) (hN : 3 * n < p ^ 2)
    (hH : 2 * (37 * n) < p ^ 2) (J : ℕ) (hJ : 2 * (37 * n) ≤ J * p) :
    -(vSK n p : ℝ) ≤ -2 * (37 * n : ℕ) * ((40 * n / p : ℕ) : ℝ) + 12 * (37 * n : ℕ) * ((3 * n / p : ℕ) : ℝ) +
      2 * layer p J (37 * n : ℕ) := by
  have h := vS_eq (by omega : 0 < n) hp.out
  have e : vSK n p = (InnerData.mk n 200 p).vS := rfl
  rw [e, h]
  have h1 := padicValNat_factorial_ge (p := p) (k := 40 * n)
  have h2 := padicValNat_factorial_small (p := p) (k := 3 * n) hN
  have h3 : ∀ i ∈ Icc 1 (37 * n - 1), padicValNat p (2 * i).factorial = 2 * i / p := fun i hi =>
    padicValNat_factorial_small (by have := (Finset.mem_Icc.mp hi).2; omega)
  have hsum : (((∑ i ∈ Icc 1 (37 * n - 1), 2 * i / p : ℕ)) : ℝ) ≤ layer p J (37 * n : ℕ) := by
    have := sum_floor_le_layer (p := p) J (37 * n) hJ
    rw [Finset.sum_range_eq_add_Ico _ (by omega)] at this
    have e2 : Ico 1 (37 * n) = Icc 1 (37 * n - 1) := by
      ext c; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [e2] at this
    rw [Nat.cast_sum]
    simpa using this
  have hs : ∑ i ∈ Icc 1 (37 * n - 1), (padicValNat p (2 * i).factorial : ℤ) =
      ((∑ i ∈ Icc 1 (37 * n - 1), 2 * i / p : ℕ) : ℤ) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun i hi => by rw [h3 i hi])
  rw [hs, h2]
  generalize padicValNat p (40 * n).factorial = A at h1 ⊢
  generalize padicValNat p 4 = B
  generalize (∑ i ∈ Icc 1 (37 * n - 1), 2 * i / p) = Sg at hsum ⊢
  generalize 40 * n / p = q at h1 ⊢
  generalize 3 * n / p = q'
  have h1R : (q : ℝ) ≤ (A : ℝ) := by exact_mod_cast h1
  have hB : (0 : ℝ) ≤ (B : ℝ) := by positivity
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at hsum ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1R (show (0 : ℝ) ≤ 74 * n by positivity),
    mul_nonneg (show (0 : ℝ) ≤ 37 * n - 1 by linarith) hB]

/-- The zero-class deficit bound. -/
noncomputable def Bmax (n p : ℕ) : ℝ :=
  max 0 ((ktopI n p : ℝ) / 2 - ((5 + 12 * ((3 * n / p : ℕ) : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ)) - 4) / 2) *
    (max 0 ((ktopI n p : ℝ) / 2 - ((5 + 12 * ((3 * n / p : ℕ) : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ)) - 4) / 2) / 2 + 1)

/-- The class function of the inner range. -/
noncomputable def hIn (n p : ℕ) (k : ℤ) (a a' : ℕ) : ℝ :=
  (psiR k (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 + 6 * (a' : ℤ) - a) : ℝ)

section
variable {n : ℕ} (hn : 33 ≤ n) (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p)
  (hsmall : ¬ p * Mcut ≤ 40 * n) (hin : 3 * p ≤ 40 * n) (hsq : 2 * (40 * n) < p ^ 2)
  (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)

include hodd in
lemma betaI_eq {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ p / 2) :
    betaI n p (m := p / 2) (⟨c, by omega⟩ : Fin (p / 2 + 1)) =
      12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 +
        6 * (aCnt p (3 * n % p) c : ℤ) - aCnt p (40 * n % p) c := by
  unfold betaI
  simp only
  rw [SX_class hodd hc1 hcm, SX_class hodd hc1 hcm]
  push_cast; ring

include hodd hsmall in
lemma q_lt : 40 * n / p < 400 := by
  unfold Mcut at hsmall
  rw [not_le] at hsmall
  exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)

include hodd in
lemma klo_le_beta (c : Fin (p / 2 + 1)) (hc : c ≠ 0) : kloI n p ≤ betaI n p c := by
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc
    · exact h
  have hcm := Nat.lt_succ_iff.mp c.isLt
  have e := betaI_eq (n := n) hodd hc1 hcm
  simp only [Fin.eta] at e
  rw [e]
  unfold kloI aCnt
  generalize 3 * n / p = q' at *
  generalize 40 * n / p = q at *
  split_ifs <;> omega

include hodd in
lemma rowsK_klo : rowsK (betaI n p (m := p / 2)) (kloI n p) = 0 := by
  unfold rowsK
  refine Finset.sum_eq_zero fun c hc => ?_
  have := klo_le_beta (n := n) hodd c (Finset.mem_erase.mp hc).1
  unfold lrow; omega

include hodd in
lemma Bse_eq_beta (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
    Bse p (40 * n) (3 * n) (c : ℕ) = (betaI n p c : ℚ) + 4 := by
  have hc0 : (c : ℕ) ≠ 0 := fun h => hc (Fin.ext h)
  unfold Bse betaI
  rw [if_neg hc0]
  push_cast; ring

lemma Bse_zero_eq : Bse p (40 * n) (3 * n) 0 = 5 + 12 * ((3 * n / p : ℕ) : ℚ) - 2 * ((40 * n / p : ℕ) : ℚ) := by
  unfold Bse
  simp only [if_pos, Nat.cast_zero, Int.cast_zero]
  rw [SX_zero, SX_zero]
  push_cast; ring

include hn hodd hp7 hsmall hin hsq hdeg in
/-- The inner side conditions hold. -/
lemma innerOK_of : InnerOK n p := by
  have hm1 : 1 ≤ p / 2 := by omega
  set β := betaI n p (m := p / 2) with hβdef
  have hq := q_lt hodd hsmall
  have hlo : rowsK β (kloI n p) + L0I n p ≤ 37 * n := by
    rw [rowsK_klo hodd]; unfold L0I; omega
  set kf := kfSel β (37 * n) (L0I n p) (kloI n p) (ktopI n p) with hkf
  have hfeas : rowsK β kf + L0I n p ≤ 37 * n :=
    kfSel_feasible β (37 * n) (L0I n p) (kloI n p) (ktopI n p) hlo
  have hkfle : kf ≤ ktopI n p := kfSel_le β (37 * n) (L0I n p) (kloI n p) (ktopI n p) (by
    unfold kloI ktopI; generalize 40 * n / p = q; omega)
  have hβ : ∀ c : Fin (p / 2 + 1), c ≠ 0 → Bse p (40 * n) (3 * n) (c : ℕ) = (β c : ℚ) + 4 :=
    fun c hc => Bse_eq_beta hodd c hc
  refine ⟨hodd, hm1, by omega, Sep_PlK hsq, by nlinarith, hdeg, ?_, ?_⟩
  · exact sum_allocK β (37 * n) kf (by omega)
  · -- the zero-class condition
    have h1 := tmin_allocK_le hm1 (Bse p (40 * n) (3 * n)) β hβ (37 * n) kf
    have hA0 : allocI n p (p / 2) 0 = 37 * n - rowsK β kf := by
      unfold allocI allocK; rw [if_pos rfl]
    have hL0 : L0I n p ≤ allocI n p (p / 2) 0 := by rw [hA0]; omega
    have hL0R : ((L0I n p : ℕ) : ℚ) ≤ (allocI n p (p / 2) 0 : ℚ) := by exact_mod_cast hL0
    rw [Bse_zero_eq]
    have hb1 : (β ⟨1, by omega⟩ : ℚ) ≤ 12 * ((3 * n / p : ℕ) : ℚ) + 8 := by
      have e := betaI_eq (n := n) hodd (c := 1) le_rfl (by omega)
      have : β ⟨1, by omega⟩ ≤ 12 * ((3 * n / p : ℕ) : ℤ) + 8 := by
        rw [hβdef, e]; unfold aCnt; generalize 3 * n / p = q' at *; generalize 40 * n / p = q at *
        split_ifs <;> omega
      have h' := (Int.cast_le (R := ℚ)).mpr this
      rw [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h'
      norm_num at h'
      exact h'
    have hkfR : (kf : ℚ) ≤ ktopI n p := by exact_mod_cast hkfle
    unfold ktopI at hkfR
    unfold L0I at hL0R
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hkfR
    norm_num at hkfR
    push_cast at hL0R
    refine h1.trans ?_
    rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 2)]
    have hq0 : (0 : ℚ) ≤ ((40 * n / p : ℕ) : ℚ) := by positivity
    have hq0' : (0 : ℚ) ≤ ((3 * n / p : ℕ) : ℚ) := by positivity
    refine max_le ?_ ?_ <;> linarith

include hn hodd hp7 hsmall hin hsq hdeg in
/-- **The inner per-prime bound** (discrete form). -/
theorem inner_Lp_le (k : ℤ) (hk1 : kloI n p ≤ k) (hk2 : k ≤ ktopI n p) :
    -(Lp n p : ℝ) ≤ -2 * (37 * n : ℕ) * ((40 * n / p : ℕ) : ℝ) +
      12 * (37 * n : ℕ) * ((3 * n / p : ℕ) : ℝ) + 2 * layer p 1000 (37 * n : ℕ) -
      (37 * n : ℕ) * (k : ℝ) +
      2 * ∑ c ∈ Icc 1 (p / 2), hIn n p k (aCnt p (40 * n % p) c) (aCnt p (3 * n % p) c) +
      ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1 := by
  have hm1 : 1 ≤ p / 2 := by omega
  have hOK := innerOK_of hn hodd hp7 hsmall hin hsq hdeg
  have hLp : Lp n p = vSK n p + ⌊2 * WI n p⌋ := by
    unfold Lp; rw [if_neg hsmall, if_pos hin, if_pos hOK]
  have hq := q_lt hodd hsmall
  -- `v_p(S_K)`
  have hv := neg_vSK_le (p := p) (n := n) (by omega) (by omega) (by nlinarith) (by nlinarith) 1000
    (by
      unfold Mcut at hsmall; rw [not_le] at hsmall
      nlinarith)
  -- the allocation
  set β := betaI n p (m := p / 2) with hβdef
  have hlo : rowsK β (kloI n p) + L0I n p ≤ 37 * n := by
    rw [rowsK_klo hodd]; unfold L0I; omega
  set kf := kfSel β (37 * n) (L0I n p) (kloI n p) (ktopI n p) with hkf
  have hfeas : rowsK β kf + L0I n p ≤ 37 * n :=
    kfSel_feasible β (37 * n) (L0I n p) (kloI n p) (ktopI n p) hlo
  have hkfle : kf ≤ ktopI n p := kfSel_le β (37 * n) (L0I n p) (kloI n p) (ktopI n p) (by
    unfold kloI ktopI; generalize 40 * n / p = q; omega)
  have hβ : ∀ c : Fin (p / 2 + 1), c ≠ 0 → Bse p (40 * n) (3 * n) (c : ℕ) = (β c : ℚ) + 4 :=
    fun c hc => Bse_eq_beta hodd c hc
  have hW := sum_wcap_allocK hm1 (Bse p (40 * n) (3 * n)) β hβ (37 * n) kf (by omega)
  have hWI : WI n p = ∑ s, wcap hm1 (allocK β (37 * n) kf) (Bse p (40 * n) (3 * n)) s := by
    unfold WI; rw [dif_pos hm1]; rfl
  rw [← hWI] at hW
  have hPhi := PhiK_le_kf β (37 * n) (L0I n p) (kloI n p) (ktopI n p) hlo hk1 hk2
  -- `Φ(k)` as a class sum
  have hsumQ : ∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0, psiR k (β c) =
      ∑ c ∈ Icc 1 (p / 2), psiR k (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 +
        6 * (aCnt p (3 * n % p) c : ℤ) - aCnt p (40 * n % p) c) := by
    have e := sum_erase_zero_eq_Icc (m := p / 2) (fun c => psiR k
      (6 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) - (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) - 4))
    refine e.trans (Finset.sum_congr rfl fun c hc => ?_)
    have hc' := Finset.mem_Icc.mp hc
    have := betaI_eq (n := n) hodd hc'.1 hc'.2
    unfold betaI at this
    simp only at this ⊢
    rw [this]
  have hPhik : (PhiK β (37 * n) k : ℝ) = ((37 * n : ℕ) : ℝ) * k / 2 -
      ∑ c ∈ Icc 1 (p / 2), hIn n p k (aCnt p (40 * n % p) c) (aCnt p (3 * n % p) c) := by
    unfold PhiK
    rw [hsumQ]
    unfold hIn
    push_cast
    ring
  -- the zero-class deficit
  have hB0 : max 0 ((kf : ℚ) / 2 - (Bse p (40 * n) (3 * n) 0 - 4) / 2) *
      (max 0 ((kf : ℚ) / 2 - (Bse p (40 * n) (3 * n) 0 - 4) / 2) / 2 + 1) ≤ (Bmax n p : ℝ) := by
    rw [Bse_zero_eq]
    unfold Bmax
    have hkR : ((kf : ℤ) : ℝ) ≤ ((ktopI n p : ℤ) : ℝ) := by exact_mod_cast hkfle
    push_cast
    generalize ((40 * n / p : ℕ) : ℝ) = qR
    generalize ((3 * n / p : ℕ) : ℝ) = qR'
    generalize ((ktopI n p : ℤ) : ℝ) = tR at hkR ⊢
    generalize ((kf : ℤ) : ℝ) = kR at hkR ⊢
    set D1 := max 0 (kR / 2 - (5 + 12 * qR' - 2 * qR - 4) / 2) with hD1
    set D2 := max 0 (tR / 2 - (5 + 12 * qR' - 2 * qR - 4) / 2) with hD2
    have h0 : 0 ≤ D1 := le_max_left _ _
    have h12 : D1 ≤ D2 := max_le_max (le_refl 0) (by linarith)
    nlinarith
  have hfl : ((⌊2 * WI n p⌋ : ℤ) : ℝ) ≥ 2 * (WI n p : ℝ) - 1 := by
    have := Int.lt_floor_add_one (2 * WI n p)
    have : ((2 * WI n p : ℚ) : ℝ) < ((⌊2 * WI n p⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast this
    push_cast at this; linarith
  have hWR : ((PhiK β (37 * n) kf : ℚ) : ℝ) - ((max 0 ((kf : ℚ) / 2 - (Bse p (40 * n) (3 * n) 0 - 4) / 2) *
      (max 0 ((kf : ℚ) / 2 - (Bse p (40 * n) (3 * n) 0 - 4) / 2) / 2 + 1) : ℚ) : ℝ) ≤ (WI n p : ℝ) := by
    exact_mod_cast hW
  have hPR : ((PhiK β (37 * n) k : ℚ) : ℝ) ≤ ((PhiK β (37 * n) kf : ℚ) : ℝ) +
      ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hPhi
    push_cast at this ⊢
    linarith
  rw [hLp]
  push_cast
  rw [hPhik] at hPR
  push_cast at hWR hB0 hv hPR
  linarith

end

end InnerPrime

section TailPrime

/-!
# The inner tail: `-L_p ≤ p (x F(x) + 27/16) + O(x²)`

For an explicit level `k` (the rounded minimiser of the quadratic majorant) the discrete bound of
`inner_Lp_le` is at most `p (x F(x) + 27/16) + C(x)`, where
`F(x) = 4λ + 2λ{x} - 12λ{αx}`, `λ = 37/40`, `α = 3/40`, `x = K/p`.
-/

open Finset


/-! ### Elementary facts -/

lemma sum_range_tri (t : ℚ) (L : ℕ) :
    ∑ i ∈ range L, ((t - 2 * i) / 2) = (L : ℚ) * (t - L + 1) / 2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma psiR_le (k β : ℤ) : psiR k β ≤ ((k - β + 1 : ℤ) : ℚ) ^ 2 / 8 := by
  unfold psiR
  set t := k - β with ht
  have hsum : ∑ i ∈ range (lrow k β), (((k : ℚ) - 2 * i - β) / 2) =
      (lrow k β : ℚ) * ((t : ℚ) - lrow k β + 1) / 2 := by
    rw [← sum_range_tri]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht]; push_cast; ring
  rw [hsum]
  unfold lrow
  rcases le_or_gt (t + 1) 0 with h | h
  · have : ((k - β + 1) / 2).toNat = 0 := by omega
    rw [this]; simp only [Nat.cast_zero, zero_mul, zero_div]; positivity
  · rcases Int.emod_two_eq_zero_or_one t with h2 | h2
    · have e : (((k - β + 1) / 2).toNat : ℚ) = (t : ℚ) / 2 := by
        have : (((k - β + 1) / 2).toNat : ℤ) * 2 = t := by omega
        have : ((((k - β + 1) / 2).toNat : ℤ) : ℚ) * 2 = (t : ℚ) := by exact_mod_cast this
        push_cast at this; linarith
      rw [e]; push_cast; nlinarith [sq_nonneg ((t : ℚ) + 1)]
    · have e : (((k - β + 1) / 2).toNat : ℚ) = ((t : ℚ) + 1) / 2 := by
        have : (((k - β + 1) / 2).toNat : ℤ) * 2 = t + 1 := by omega
        have : ((((k - β + 1) / 2).toNat : ℤ) : ℚ) * 2 = (t : ℚ) + 1 := by exact_mod_cast this
        push_cast at this; linarith
      rw [e]; push_cast; nlinarith [sq_nonneg ((t : ℚ) + 1)]

lemma sum_aCnt {p m v : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) :
    ∑ c ∈ Icc 1 m, aCnt p v c = v := by
  unfold aCnt
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero,
    Finset.sum_const_zero, add_zero, add_zero, Finset.sum_const, Finset.sum_const, smul_eq_mul,
    smul_eq_mul, mul_one, mul_one]
  have h1 : (Icc 1 m).filter (fun c => c ≤ v) = Icc 1 (min m v) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have h2 : (Icc 1 m).filter (fun c => p - v ≤ c) = Icc (max 1 (p - v)) m := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [h1, h2, Nat.card_Icc, Nat.card_Icc]
  omega

lemma aCnt_range {p m v c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hc1 : 1 ≤ c) (hcm : c ≤ m) :
    (if m < v then 1 else 0) ≤ aCnt p v c ∧ aCnt p v c ≤ (if m < v then 1 else 0) + 1 := by
  unfold aCnt; split_ifs <;> omega

/-- **Popoviciu**: values in an interval of length `7` have `∑ φ² ≤ (∑ φ)²/m + 49m/4`. -/
lemma popoviciu {ι : Type*} (s : Finset ι) (φ : ι → ℝ) (L : ℝ) (hφ : ∀ c ∈ s, L ≤ φ c ∧ φ c ≤ L + 7)
    (hs : 0 < s.card) :
    ∑ c ∈ s, φ c ^ 2 ≤ (∑ c ∈ s, φ c) ^ 2 / s.card + 49 * s.card / 4 := by
  set m : ℝ := (s.card : ℝ) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; exact_mod_cast hs
  have h1 : ∑ c ∈ s, (φ c - L) ^ 2 ≤ 7 * ∑ c ∈ s, (φ c - L) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have := hφ c hc
    nlinarith
  set U := ∑ c ∈ s, (φ c - L) with hU
  have hsumφ : ∑ c ∈ s, φ c = U + m * L := by
    rw [hU, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  have hsq : ∑ c ∈ s, φ c ^ 2 = ∑ c ∈ s, (φ c - L) ^ 2 + 2 * L * U + m * L ^ 2 := by
    rw [hU, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show m * L ^ 2 = ∑ _c ∈ s, L ^ 2 by rw [Finset.sum_const, nsmul_eq_mul]]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_; ring
  rw [hsq, hsumφ]
  have h2 : 7 * U ≤ U ^ 2 / m + 49 * m / 4 := by
    rw [div_add' _ _ _ hm0.ne', le_div_iff₀ hm0]
    nlinarith [sq_nonneg (U - 7 * m / 2)]
  have e : (U + m * L) ^ 2 / m = U ^ 2 / m + 2 * L * U + m * L ^ 2 := by
    field_simp; ring
  rw [e]
  linarith

/-- The continuous layer function `J(u) = ∑_{j ≤ 1000} (u - j/2)⁺`. -/
noncomputable def Jc (u : ℝ) : ℝ := ∑ j ∈ (Icc 1 1000 : Finset ℕ), max 0 (u - (j : ℝ) / 2)

lemma layer_eq {p : ℕ} (hp : 0 < p) (h : ℕ) :
    layer p 1000 h = (p : ℝ) * Jc ((h : ℝ) / p) := by
  unfold layer Jc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [mul_max_of_nonneg _ _ hpR.le, mul_zero, mul_sub, mul_div_cancel₀ _ hpR.ne']
  congr 1; ring

/-- `2 J(u) = 2u² - u + η(1 - η)/2` with `η = {2u}`, for `0 ≤ u ≤ 500`. -/
lemma two_Jc_eq {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 500) :
    2 * Jc u = 2 * u ^ 2 - u + Int.fract (2 * u) * (1 - Int.fract (2 * u)) / 2 := by
  set μ := ⌊2 * u⌋₊ with hμ
  have hμ1 : (μ : ℝ) ≤ 2 * u := Nat.floor_le (by linarith)
  have hμ2 : 2 * u < μ + 1 := Nat.lt_floor_add_one _
  have hμ1000 : μ ≤ 1000 := by
    have : (μ : ℝ) ≤ 1000 := by linarith
    exact_mod_cast this
  have hfr : Int.fract (2 * u) = 2 * u - μ := by
    rw [Int.fract, show ⌊2 * u⌋ = (μ : ℤ) by
      rw [hμ, ← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by linarith))]]
    push_cast; ring
  have hsplit : Jc u = ∑ j ∈ (Icc 1 μ : Finset ℕ), (u - (j : ℝ) / 2) := by
    unfold Jc
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hμ1000) (fun j hj hjn => by
      simp only [Finset.mem_Icc, not_and, not_le] at hj hjn
      have := hjn hj.1
      have : (μ : ℝ) + 1 ≤ j := by exact_mod_cast this
      exact max_eq_left (by linarith))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := (Finset.mem_Icc.mp hj).2
    have : (j : ℝ) ≤ μ := by exact_mod_cast this
    exact max_eq_right (by linarith)
  have hclosed : ∑ j ∈ (Icc 1 μ : Finset ℕ), (u - (j : ℝ) / 2) = μ * u - (μ : ℝ) * (μ + 1) / 4 := by
    induction μ with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring
  rw [hsplit, hclosed, hfr]
  ring

lemma phi_bounds {p m v v' c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (hc1 : 1 ≤ c) (hcm : c ≤ m) :
    6 * (if m < v' then (1 : ℝ) else 0) - (if m < v then (1 : ℝ) else 0) - 1 ≤
        6 * (aCnt p v' c : ℝ) - aCnt p v c ∧
      6 * (aCnt p v' c : ℝ) - aCnt p v c ≤
        6 * (if m < v' then (1 : ℝ) else 0) - (if m < v then (1 : ℝ) else 0) - 1 + 7 := by
  have r1 := aCnt_range hm hv hc1 hcm
  have r2 := aCnt_range hm hv' hc1 hcm
  split_ifs at r1 r2 ⊢ <;>
  · have e1 : ((aCnt p v c : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show aCnt p v c ≤ 2 by omega)
    have e2 : ((aCnt p v' c : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show aCnt p v' c ≤ 2 by omega)
    first
      | (have f1 : (1 : ℝ) ≤ aCnt p v c := by exact_mod_cast (show 1 ≤ aCnt p v c by omega)
         have f2 : (1 : ℝ) ≤ aCnt p v' c := by exact_mod_cast (show 1 ≤ aCnt p v' c by omega)
         constructor <;> linarith)
      | (have f1 : (1 : ℝ) ≤ aCnt p v c := by exact_mod_cast (show 1 ≤ aCnt p v c by omega)
         have f2 : (aCnt p v' c : ℝ) ≤ 1 := by exact_mod_cast (show aCnt p v' c ≤ 1 by omega)
         have f3 : (0 : ℝ) ≤ aCnt p v' c := by positivity
         constructor <;> linarith)
      | (have f1 : (aCnt p v c : ℝ) ≤ 1 := by exact_mod_cast (show aCnt p v c ≤ 1 by omega)
         have f2 : (1 : ℝ) ≤ aCnt p v' c := by exact_mod_cast (show 1 ≤ aCnt p v' c by omega)
         have f3 : (0 : ℝ) ≤ aCnt p v c := by positivity
         constructor <;> linarith)
      | (have f1 : (aCnt p v c : ℝ) ≤ 1 := by exact_mod_cast (show aCnt p v c ≤ 1 by omega)
         have f2 : (aCnt p v' c : ℝ) ≤ 1 := by exact_mod_cast (show aCnt p v' c ≤ 1 by omega)
         have f3 : (0 : ℝ) ≤ aCnt p v c := by positivity
         have f4 : (0 : ℝ) ≤ aCnt p v' c := by positivity
         constructor <;> linarith)

lemma hIn_le_sq (n p : ℕ) (k τ : ℤ)
    (hk : k = τ + (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4) - 1) (a a' : ℕ) :
    hIn n p k a a' ≤ ((τ : ℝ) - (6 * (a' : ℝ) - a)) ^ 2 / 8 := by
  unfold hIn
  have h1 := psiR_le k (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 + 6 * (a' : ℤ) - a)
  have hz : k - (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 + 6 * (a' : ℤ) - a) + 1 =
      τ - (6 * (a' : ℤ) - a) := by rw [hk]; ring
  rw [hz] at h1
  have h2 := (Rat.cast_le (K := ℝ)).mpr h1
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_intCast] at h2
  refine h2.trans (le_of_eq ?_)
  push_cast; ring

lemma layer_le {p : ℕ} (hp0 : 0 < p) (H : ℕ) (hu500 : (H : ℝ) / p ≤ 500) :
    2 * layer p 1000 H ≤ 2 * (H : ℝ) ^ 2 / p - H + p / 8 := by
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp0
  have hu0 : (0 : ℝ) ≤ (H : ℝ) / p := by positivity
  rw [layer_eq hp0]
  have e := two_Jc_eq hu0 hu500
  set η := Int.fract (2 * ((H : ℝ) / p)) with hη
  have hη0 : 0 ≤ η := Int.fract_nonneg _
  have hη1 : η < 1 := Int.fract_lt_one _
  have hηb : η * (1 - η) ≤ 1 / 4 := by nlinarith [sq_nonneg (η - 1 / 2)]
  have : 2 * ((p : ℝ) * Jc ((H : ℝ) / p)) = p * (2 * Jc ((H : ℝ) / p)) := by ring
  rw [this, e]
  have e2 : (p : ℝ) * (2 * ((H : ℝ) / p) ^ 2 - (H : ℝ) / p) = 2 * (H : ℝ) ^ 2 / p - H := by
    field_simp
  have e3 : (p : ℝ) * (2 * ((H : ℝ) / p) ^ 2 - (H : ℝ) / p + η * (1 - η) / 2) =
      2 * (H : ℝ) ^ 2 / p - H + p * (η * (1 - η)) / 2 := by rw [← e2]; ring
  rw [e3]
  have := mul_le_mul_of_nonneg_left hηb hpR0.le
  linarith

lemma quad_le {hR SR m τ : ℝ} (hm0 : 0 < m) (h1 : τ ≤ (SR + 2 * hR) / m + 1 / 2)
    (h2 : (SR + 2 * hR) / m + 1 / 2 < τ + 1) :
    -hR * τ + (m * τ ^ 2 - 2 * τ * SR + SR ^ 2 / m) / 4 ≤ -hR * SR / m - hR ^ 2 / m + m / 16 := by
  set τs := (SR + 2 * hR) / m with hτs
  have hd : (τ - τs) ^ 2 ≤ 1 / 4 := by nlinarith
  have e : -hR * τ + (m * τ ^ 2 - 2 * τ * SR + SR ^ 2 / m) / 4 =
      -hR * SR / m - hR ^ 2 / m + m * (τ - τs) ^ 2 / 4 := by
    rw [hτs]; field_simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left hd hm0.le
  linarith

lemma diff_le {hR SR p : ℝ} (hp : 1 < p) (hh0 : 0 ≤ hR) (hhS : 0 ≤ hR + SR) :
    2 * hR ^ 2 / p - hR ^ 2 / ((p - 1) / 2) - hR * SR / ((p - 1) / 2) + 2 * hR * SR / p ≤ 0 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have e : 2 * hR ^ 2 / p - hR ^ 2 / ((p - 1) / 2) - hR * SR / ((p - 1) / 2) + 2 * hR * SR / p =
      -(2 * (hR * (hR + SR))) / (p * (p - 1)) := by
    field_simp; ring
  rw [e]
  apply div_nonpos_of_nonpos_of_nonneg
  · have := mul_nonneg hh0 hhS; linarith
  · positivity

/-- The additive error of the tail bound. -/
noncomputable def Ctail (n p : ℕ) : ℝ :=
  4 * (37 * n : ℝ) / p + ((ktopI n p - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1

variable {p : ℕ} [hp : Fact p.Prime]

section
variable {n : ℕ} (hn : 33 ≤ n) (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p)
  (hsmall : ¬ p * Mcut ≤ 40 * n) (hin : 3 * p ≤ 40 * n) (hsq : 2 * (40 * n) < p ^ 2)
  (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)

set_option maxHeartbeats 2000000 in
include hn hodd hp7 hsmall hin hsq hdeg in
/-- **The tail bound**: `-L_p ≤ p (x F(x) + 27/16) + C`. -/
theorem tail_Lp_le :
    -(Lp n p : ℝ) ≤ (p : ℝ) * ((40 * n / p : ℝ) * Ftail (40 * n / p) + 27 / 16) + Ctail n p := by
  -- notation
  have hp0 : 0 < p := by omega
  have hpR : (7 : ℝ) ≤ p := by exact_mod_cast hp7
  set m := p / 2 with hmdef
  have hmR : (m : ℝ) = ((p : ℝ) - 1) / 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) = p := by exact_mod_cast hodd
    push_cast at this; linarith
  have hm0 : (0 : ℝ) < m := by rw [hmR]; linarith
  set v := 40 * n % p with hv
  set v' := 3 * n % p with hv'
  have hvp : v < p := Nat.mod_lt _ hp0
  have hv'p : v' < p := Nat.mod_lt _ hp0
  set q := 40 * n / p with hq
  set q' := 3 * n / p with hq'
  have hdivK : (40 * n : ℝ) = q * p + v := by
    have := Nat.div_add_mod (40 * n) p
    have h' : ((p * q + v : ℕ) : ℝ) = ((40 * n : ℕ) : ℝ) := by rw [this]
    push_cast at h'; linarith
  have hdivN : (3 * n : ℝ) = q' * p + v' := by
    have := Nat.div_add_mod (3 * n) p
    have h' : ((p * q' + v' : ℕ) : ℝ) = ((3 * n : ℕ) : ℝ) := by rw [this]
    push_cast at h'; linarith
  set hR : ℝ := (37 * n : ℝ) with hhR
  set SR : ℝ := 6 * (v' : ℝ) - v with hSR
  set τs : ℝ := (SR + 2 * hR) / m with hτs
  set τ : ℤ := ⌊τs + 1 / 2⌋ with hτ
  have hδ1 : (τ : ℝ) ≤ τs + 1 / 2 := Int.floor_le _
  have hδ2 : τs + 1 / 2 < τ + 1 := Int.lt_floor_add_one _
  set B : ℤ := 12 * (q' : ℤ) - 2 * (q : ℤ) - 4 with hB
  set k : ℤ := τ + B - 1 with hk
  -- basic size facts
  have hqlt : (40 * n : ℝ) < ((q : ℝ) + 1) * p := by
    have := Nat.lt_div_mul_add (a := 40 * n) hp0
    have : ((40 * n : ℕ) : ℝ) < ((q * p + p : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hq'le : (q' : ℝ) * p ≤ 3 * n := by rw [hdivN]; have : (0 : ℝ) ≤ v' := by positivity
                                          linarith
  have hnin : (3 : ℝ) * p ≤ 40 * n := by exact_mod_cast hin
  have hvR : (v : ℝ) < p := by exact_mod_cast hvp
  have hv'R : (v' : ℝ) < p := by exact_mod_cast hv'p
  have hv0 : (0 : ℝ) ≤ v := by positivity
  have hv'0 : (0 : ℝ) ≤ v' := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq'0 : (0 : ℝ) ≤ q' := by positivity
  have hτsm : τs * m = SR + 2 * hR := by rw [hτs]; field_simp
  -- `τs` bounds
  have hτs_lo : 8 ≤ τs := by
    have : 8 * (m : ℝ) ≤ SR + 2 * hR := by rw [hmR, hSR, hhR]; linarith
    rw [hτs, le_div_iff₀ hm0]; linarith
  have h40 : 40 * (q' : ℝ) ≤ 3 * q + 3 := by
    have e1 : 40 * ((q' : ℝ) * p) ≤ 120 * n := by linarith
    have e2 : 120 * (n : ℝ) < 3 * ((q : ℝ) * p) + 3 * p := by linarith
    have : (40 * (q' : ℝ) - 3 * q - 3) * p < 0 := by ring_nf; ring_nf at e1 e2; linarith
    by_contra hc
    rw [not_le] at hc
    have := mul_nonneg (show (0 : ℝ) ≤ 40 * q' - 3 * q - 3 by linarith) (show (0 : ℝ) ≤ p by linarith)
    linarith
  have hτs_hi : τs ≤ 10 * (q : ℝ) + 24 - 12 * q' := by
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 7 := by linarith
    have f1 := mul_nonneg hq0 hp1
    have f2 := mul_le_mul_of_nonneg_right h40 (show (0 : ℝ) ≤ (p : ℝ) - 1 by linarith)
    have : (SR + 2 * hR) ≤ (10 * (q : ℝ) + 24 - 12 * q') * m := by
      rw [hmR, hSR, hhR]; ring_nf; ring_nf at f1 f2 hqlt; nlinarith
    rw [hτs, div_le_iff₀ hm0]; linarith
  -- `k` is admissible
  have hk1 : kloI n p ≤ k := by
    have : (1 : ℝ) ≤ τ := by
      have : (8 : ℝ) + 1 / 2 - 1 < τ := by linarith
      have h1 : (8 : ℤ) ≤ τ := by
        have : (7 : ℝ) < τ := by linarith
        exact_mod_cast (show (7 : ℤ) < τ by exact_mod_cast this)
      exact_mod_cast (show (1 : ℤ) ≤ τ by omega)
    have hτ1 : (1 : ℤ) ≤ τ := by exact_mod_cast this
    have hklo : kloI n p = -2 * (q : ℤ) - 6 := rfl
    rw [hklo, hk, hB]
    have hq0Z : (0 : ℤ) ≤ q := by positivity
    have hq'0Z : (0 : ℤ) ≤ q' := by positivity
    generalize (q : ℤ) = Q at *
    generalize (q' : ℤ) = Q' at *
    omega
  have hk2 : k ≤ ktopI n p := by
    have hτle : (τ : ℝ) ≤ 10 * (q : ℝ) + 24 - 12 * q' + 1 / 2 := by linarith
    have : τ ≤ 10 * (q : ℤ) + 24 - 12 * (q' : ℤ) := by
      have : (τ : ℝ) < 10 * (q : ℝ) + 24 - 12 * q' + 1 := by linarith
      have : (τ : ℝ) < ((10 * (q : ℤ) + 24 - 12 * (q' : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
      have := (Int.cast_lt (R := ℝ)).mp this
      omega
    have hktop : ktopI n p = 8 * (q : ℤ) + 20 := rfl
    rw [hktop, hk, hB]
    have hq0Z : (0 : ℤ) ≤ q := by positivity
    generalize (q : ℤ) = Q at *
    generalize (q' : ℤ) = Q' at *
    omega
  have main := inner_Lp_le hn hodd hp7 hsmall hin hsq hdeg k hk1 hk2
  -- the class sum
  set φ : ℕ → ℝ := fun c => 6 * (aCnt p v' c : ℝ) - aCnt p v c with hφ
  have hIn_le : ∀ c, hIn n p k (aCnt p v c) (aCnt p v' c) ≤ ((τ : ℝ) - φ c) ^ 2 / 8 :=
    fun c => hIn_le_sq n p k τ (by rw [hk, hB]) _ _
  have hcard : ((Icc 1 m).card : ℝ) = m := by rw [Nat.card_Icc]; simp
  have hSphi : ∑ c ∈ Icc 1 m, φ c = SR := by
    rw [hφ, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e1 := sum_aCnt hodd hvp
    have e2 := sum_aCnt hodd hv'p
    have e1' : ∑ c ∈ Icc 1 m, (aCnt p v c : ℝ) = v := by exact_mod_cast e1
    have e2' : ∑ c ∈ Icc 1 m, (aCnt p v' c : ℝ) = v' := by exact_mod_cast e2
    rw [e1', e2']
  have hpop : ∑ c ∈ Icc 1 m, φ c ^ 2 ≤ SR ^ 2 / m + 49 * m / 4 := by
    have hm1 : 0 < (Icc 1 m).card := by rw [Nat.card_Icc]; omega
    have := popoviciu (Icc 1 m) φ
      (6 * (if m < v' then (1 : ℝ) else 0) - (if m < v then (1 : ℝ) else 0) - 1)
      (fun c hc => phi_bounds hodd hvp hv'p (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2) hm1
    rw [hcard, hSphi] at this
    exact this
  have hsq : ∑ c ∈ Icc 1 m, ((τ : ℝ) - φ c) ^ 2 =
      (m : ℝ) * (τ : ℝ) ^ 2 - 2 * τ * SR + ∑ c ∈ Icc 1 m, φ c ^ 2 := by
    have : ∑ c ∈ Icc 1 m, ((τ : ℝ) - φ c) ^ 2 =
        ∑ c ∈ Icc 1 m, ((τ : ℝ) ^ 2 - 2 * τ * φ c + φ c ^ 2) := by
      refine Finset.sum_congr rfl fun c _ => ?_; ring
    rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, hSphi, hcard]
  have hclass : 2 * ∑ c ∈ Icc 1 m, hIn n p k (aCnt p v c) (aCnt p v' c) ≤
      ((m : ℝ) * (τ : ℝ) ^ 2 - 2 * τ * SR + SR ^ 2 / m + 49 * m / 4) / 4 := by
    have := Finset.sum_le_sum fun c (_ : c ∈ Icc 1 m) => hIn_le c
    rw [← Finset.sum_div, hsq] at this
    linarith
  have hpR0 : (0 : ℝ) < p := by linarith
  have hu500 : ((37 * n : ℕ) : ℝ) / p ≤ 500 := by
    rw [div_le_iff₀ hpR0]
    have : (40 * n : ℝ) < 400 * p := by
      unfold Mcut at hsmall; rw [not_le] at hsmall
      exact_mod_cast (show 40 * n < 400 * p by linarith)
    push_cast; linarith
  have hlay := layer_le hp0 (37 * n) hu500
  have e37 : ((37 * n : ℕ) : ℝ) = hR := by rw [hhR]; push_cast; ring
  rw [e37] at hlay
  have hquad := quad_le (hR := hR) (SR := SR) (τ := (τ : ℝ)) hm0 hδ1 hδ2
  have hdiff := diff_le (hR := hR) (SR := SR) (p := (p : ℝ)) (by linarith) (by rw [hhR]; positivity)
    (by rw [hhR, hSR]; linarith)
  rw [← hmR] at hdiff
  -- the target
  have hfK : Int.fract ((40 * n / p : ℝ)) = (v : ℝ) / p := by
    have := Int.fract_div_natCast_eq_div_natCast_mod (k := ℝ) (m := 40 * n) (n := p)
    push_cast at this; exact this
  have hfN : Int.fract ((3 : ℝ) / 40 * (40 * n / p)) = (v' : ℝ) / p := by
    have := Int.fract_div_natCast_eq_div_natCast_mod (k := ℝ) (m := 3 * n) (n := p)
    have e : (3 : ℝ) / 40 * (40 * n / p) = ((3 * n : ℕ) : ℝ) / (p : ℕ) := by push_cast; ring
    rw [e]; exact this
  have hT : (p : ℝ) * ((40 * n / p : ℝ) * Ftail (40 * n / p) + 27 / 16) =
      4 * hR - 2 * hR * SR / p + 27 * p / 16 := by
    unfold Ftail; rw [hfK, hfN, hSR, hhR]; field_simp; ring
  have hE : ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) ≤ ((ktopI n p - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast (show k - kloI n p ≤ ktopI n p - kloI n p by omega)
  have hkR : (k : ℝ) = τ + 12 * (q' : ℝ) - 2 * q - 5 := by rw [hk, hB]; push_cast; ring
  have hCt : Ctail n p = 4 * hR / p + ((ktopI n p - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) +
      2 * Bmax n p + 1 := by unfold Ctail; rw [hhR]
  have h4 : 0 ≤ 4 * hR / p := by positivity
  rw [hT, hCt]
  have hmain := main
  rw [hkR, e37] at hmain
  simp only [← hq, ← hq', ← hmdef, ← hv, ← hv'] at hmain
  have hmR16 : (m : ℝ) / 16 + 49 * m / 16 = 25 * (p : ℝ) / 16 - 25 / 16 := by rw [hmR]; ring
  have s1 : -(Lp n p : ℝ) ≤ 2 * layer p 1000 hR - hR * τ + 5 * hR +
      2 * ∑ x ∈ Icc 1 m, hIn n p k (aCnt p v x) (aCnt p v' x) +
      ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1 := by
    have : -2 * hR * (q : ℝ) + 12 * hR * q' - hR * ((τ : ℝ) + 12 * q' - 2 * q - 5) =
      -hR * τ + 5 * hR := by ring
    linarith
  have s2 : -(Lp n p : ℝ) ≤ 2 * layer p 1000 hR + 5 * hR +
      (-hR * SR / m - hR ^ 2 / m + m / 16) + 49 * m / 16 +
      ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1 := by
    have : ((m : ℝ) * (τ : ℝ) ^ 2 - 2 * τ * SR + SR ^ 2 / m + 49 * m / 4) / 4 =
      ((m : ℝ) * (τ : ℝ) ^ 2 - 2 * τ * SR + SR ^ 2 / m) / 4 + 49 * m / 16 := by ring
    linarith
  have s3 : -(Lp n p : ℝ) ≤ 2 * hR ^ 2 / p + 4 * hR + p / 8 - hR * SR / m - hR ^ 2 / m +
      (25 * (p : ℝ) / 16 - 25 / 16) + ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1 := by
    have : -hR * SR / m = -(hR * SR / m) := by ring
    linarith
  have s4 : -(Lp n p : ℝ) ≤ 4 * hR - 2 * hR * SR / p + 27 * p / 16 +
      ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) + 2 * Bmax n p + 1 := by
    linarith
  linarith

end

end TailPrime

section Summation

lemma theta_eq_sum_cPrime (t : ℝ) : Chebyshev.theta t = ∑ k ∈ Icc 0 ⌊t⌋₊, cPrime k := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

lemma sum_cPrime_le_theta (M : ℕ) : ∑ k ∈ Ioc 0 M, cPrime k ≤ Chebyshev.theta M := by
  rw [theta_eq_sum_cPrime, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega
  · intro k _ _; unfold cPrime; split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_refl _

lemma cPrime_nonneg' (k : ℕ) : 0 ≤ cPrime k := by
  unfold cPrime; split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_refl _


lemma floor_Kr_div (n d : ℕ) (hd : 0 < d) : ⌊Kr n / d⌋₊ = 40 * n / d := by
  rw [show Kr n / d = ((40 * n : ℕ) : ℝ) / (d : ℕ) by simp [Kr]]
  exact Nat.floor_div_eq_div _ _

lemma Bmax_le {n p Q : ℕ} (hq : 40 * n / p ≤ Q) : Bmax n p ≤ (5 * (Q : ℝ) + 10) * (3 * Q + 6) := by
  unfold Bmax ktopI
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  have hQ : ((40 * n / p : ℕ) : ℝ) ≤ Q := by exact_mod_cast hq
  have h0' : (0 : ℝ) ≤ ((3 * n / p : ℕ) : ℝ) := by positivity
  generalize ((40 * n / p : ℕ) : ℝ) = qR at hQ ⊢
  generalize ((3 * n / p : ℕ) : ℝ) = qR' at h0' ⊢
  set D := max 0 ((8 * qR + 20) / 2 - ((5 + 12 * qR' - 2 * qR) - 4) / 2) with hD
  have hD0 : 0 ≤ D := le_max_left _ _
  have hD1 : D ≤ 5 * (Q : ℝ) + 10 := max_le (by positivity) (by linarith)
  nlinarith

lemma ktop_sub_klo (n p : ℕ) : ((ktopI n p - kloI n p : ℤ) : ℝ) = 10 * ((40 * n / p : ℕ) : ℝ) + 26 := by
  unfold ktopI kloI
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_neg]
  ring

lemma Ctail_le {n p : ℕ} (hp : 0 < p) (hq : 40 * n / p < 400) (hn : (n : ℝ) ≤ 10 * p) :
    Ctail n p ≤ 10 ^ 7 := by
  unfold Ctail
  rw [ktop_sub_klo]
  unfold L0I
  have hB := Bmax_le (n := n) (p := p) (Q := 399) (by omega)
  have hQ : ((40 * n / p : ℕ) : ℝ) ≤ 399 := by exact_mod_cast (show 40 * n / p ≤ 399 by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : 4 * (37 * (n : ℝ)) / p ≤ 1480 := by rw [div_le_iff₀ hpR]; linarith
  have h0 : (0 : ℝ) ≤ ((40 * n / p : ℕ) : ℝ) := by positivity
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  generalize ((40 * n / p : ℕ) : ℝ) = qR at hQ h0 ⊢
  norm_num at hB
  nlinarith


lemma range_sum_le {a b : ℕ} (F : ℕ → ℝ) (f : ℝ → ℝ) (K C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k ∈ Ioc a b, k.Prime → F k ≤ k * f (K / k) + C) :
    ∑ k ∈ Ioc a b, cPrime k * F k ≤
      ∑ k ∈ Ioc a b, (k : ℝ) * cPrime k * f (K / k) + C * Chebyshev.theta b := by
  have hθ : ∑ k ∈ Ioc a b, cPrime k ≤ Chebyshev.theta b := by
    refine le_trans ?_ (sum_cPrime_le_theta b)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; simp only [Finset.mem_Ioc] at hk ⊢; omega
    · intro k _ _; exact cPrime_nonneg' k
  have hterm : ∀ k ∈ Ioc a b, cPrime k * F k ≤ (k : ℝ) * cPrime k * f (K / k) + C * cPrime k := by
    intro k hk
    by_cases hp : k.Prime
    · have := h k hk hp
      have hc := cPrime_nonneg' k
      nlinarith [mul_le_mul_of_nonneg_left this hc]
    · simp [cPrime, hp]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hθ hC]

lemma big_prime_facts {n k : ℕ} (hn : 10400 ≤ n) (hk : n / 10 < k) (hp : k.Prime) :
    7 ≤ k ∧ 2 * (k / 2) + 1 = k ∧ ¬ k * Mcut ≤ 40 * n ∧ 2 * (40 * n) < k ^ 2 ∧
      5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < k ^ 2 ∧ (n : ℝ) ≤ 10 * k := by
  have h10 : n + 1 ≤ 10 * k := by omega
  have hsq : 10400 * n + 700 ≤ k ^ 2 * 100 := by nlinarith
  have hodd' : 2 * (k / 2) + 1 = k := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      have : 2 ∣ k := ⟨j, by omega⟩
      rcases hp.eq_one_or_self_of_dvd 2 this with h | h
      · omega
      · omega
    · omega
  refine ⟨by omega, hodd', by unfold Mcut; omega, by omega, by omega, ?_⟩
  exact_mod_cast (show n ≤ 10 * k by omega)

lemma range2_le {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (n / 10) (2 * n), cPrime k * (-(Lp n k : ℝ)) ≤
      psum (fun x => x * Ftail x + 27 / 16) 20 400 (Kr n) + 10 ^ 7 * Chebyshev.theta (2 * n : ℕ) := by
  have hps : psum (fun x => x * Ftail x + 27 / 16) 20 400 (Kr n) =
      ∑ k ∈ Ioc (n / 10) (2 * n), (k : ℝ) * cPrime k * ((fun x => x * Ftail x + 27 / 16) (Kr n / k)) := by
    unfold psum
    rw [show (400 : ℝ) = ((400 : ℕ) : ℝ) by norm_num, show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num,
      floor_Kr_div n 400 (by norm_num), floor_Kr_div n 20 (by norm_num),
      show 40 * n / 400 = n / 10 by omega, show 40 * n / 20 = 2 * n by omega]
  rw [hps]
  refine range_sum_le (fun k => -(Lp n k : ℝ)) (fun x => x * Ftail x + 27 / 16) (Kr n) (10 ^ 7)
    (by norm_num) fun k hk hp => ?_
  have hk' := Finset.mem_Ioc.mp hk
  obtain ⟨hp7, hodd, hsmall, hsq, hdeg, hn10⟩ := big_prime_facts hn hk'.1 hp
  have := Fact.mk hp
  have h := tail_Lp_le (p := k) (n := n) (by omega) hodd hp7 hsmall (by omega) hsq hdeg
  have hC := Ctail_le (n := n) (p := k) hp.pos (by
    unfold Mcut at hsmall; rw [not_le] at hsmall
    exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by linarith)) hn10
  have e : Kr n / k = 40 * n / k := by simp [Kr]
  simp only [e]
  linarith

end Summation

end Apery

end Port0


open Finset in
/-- The platform target `Apery.range2_le`, restated at top level as `solution`. -/
theorem solution {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (n / 10) (2 * n), Apery.cPrime k * (-(Apery.Lp n k : ℝ)) ≤
      Apery.psum (fun x => x * Apery.Ftail x + 27 / 16) 20 400 (Apery.Kr n) +
        10 ^ 7 * Chebyshev.theta (2 * n : ℕ) :=
  Apery.range2_le hn
