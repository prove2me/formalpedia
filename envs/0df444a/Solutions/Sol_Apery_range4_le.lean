-- Prove2me | solution 1 for Apery.range4_le
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T16:38:05.537984+00:00
-- url     : https://prove2.me/submissions/f4c1cdf9-42d3-4985-beb1-54bac11795e9

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The outer prime range (source `Apery/Growth/Assembly3.lean`)

This file proves the platform theorem `Apery.range4_le`: for $n \ge 10400$,

$$\sum_{K/3 < p \le 2h} c(k)\,\bigl(-L_k\bigr) \;\le\;
\operatorname{psum} E_{\mathrm{out}}\,\frac{20}{37}\,3\,K \;+\; 10^5\,\theta(2h),
\qquad K = 40n,\ h = 37n,$$

where $c(k) = \log k$ for primes and $0$ otherwise, $L_k$ is the local exponent of the
normaliser, $E_{\mathrm{out}}$ the continuous outer profile and $\operatorname{psum}$ the
weighted prime sum. A faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: the class-counting framework
(`Apery/Arith/{Pullback,DirectBound,ClassFrame,ClassCount,OuterBasis}.lean`), the parameters
of Section 4.1 and the $p$-adic valuation of $S_K$ (`Apery/Normalization.lean`,
`Apery/Legendre.lean`), the class-sum approximation (`Apery/Growth/{ClassSum,ClassData}.lean`),
the valuation defect bound `neg_vSK_le` (`Apery/Growth/InnerPrime.lean`) with `layer_eq`
(`Apery/Growth/TailPrime.lean`), the additive-constant bounds
(`Apery/Growth/Constants.lean`), the outer per-prime bound `outer_Lp_le` and `Cout`
(`Apery/Growth/OuterPrime.lean`), and the final summation
(`Apery/Growth/Assembly2.lean`, `Apery/Growth/Assembly3.lean`).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourcePrimeSum
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceGrowth
import Definitions.Def_Zeta5_SourceGrowthTables

set_option autoImplicit false

section Port0
/-!
# The outer prime range `K/3 < p ≤ 2h` (source `Apery/Growth/Assembly3.lean`)

This file proves the platform theorem `Apery.range4_le`:

`∑_{K/3 < p ≤ 2h} c(k)(-L_k) ≤ psum Eout (20/37) 3 K + 10^5 θ(2h)` for `n ≥ 10400`.

A faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: the class-counting framework
(`Apery/Arith/ClassFrame.lean`, `Apery/Arith/ClassCount.lean`), the parameters of Section 4.1
and the `p`-adic valuation (`Apery/Normalization.lean`, `Apery/Legendre.lean`), the class-sum
approximation (`Apery/Growth/ClassSum.lean`, `Apery/Growth/ClassData.lean`), the valuation
defect bound `neg_vSK_le` (`Apery/Growth/InnerPrime.lean`) and `layer_eq`
(`Apery/Growth/TailPrime.lean`), the outer per-prime bound `outer_Lp_le` and its error
`Cout_le` (`Apery/Growth/OuterPrime.lean`, `Apery/Growth/Assembly2.lean`), and the final
summation (`Apery/Growth/Assembly3.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Finset

namespace Apery

/-! ## The class-counting framework (`Apery/Arith/Pullback.lean`, `DirectBound.lean`,
`ClassFrame.lean`, `ClassCount.lean`) -/

section Counting

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

section JcZero

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-- `jc hm j = 0` iff the prime divides `j` (source `Apery/Arith/OuterEntryMain.lean`). -/
lemma jc_eq_zero_iff (hm : 2 * m + 1 = p) (j : ℕ) : jc hm j = 0 ↔ (p : ℤ) ∣ (j : ℤ) := by
  unfold jc
  rw [ccls_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

end JcZero


variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

lemma ccls_self (hm : 2 * m + 1 = p) (c : Fin (m + 1)) : ccls hm ((((c : ℕ) : ℤ) : ZMod p)) = c :=
  (ccls_unique hm _ c (Or.inl rfl)).symm

end Counting



/-! ## Parameters of Section 4.1 and the valuation of `S_K` -/

section Params

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

end Params



/-! ## The class sum and the layer (`Apery/Growth/ClassSum.lean`, `ClassData.lean`) -/

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

end ClassSum



/-! ## Valuation defect and layer (`Apery/Growth/InnerPrime.lean`, `TailPrime.lean`) -/

section ValDefect

variable {p : ℕ} [hp : Fact p.Prime]

lemma sum_erase_zero_eq_Icc {m : ℕ} (F : ℕ → ℚ) :
    ∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, F c = ∑ c ∈ Icc 1 m, F c := by
  have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun c => F c) (Finset.mem_univ 0)
  rw [Fin.sum_univ_eq_sum_range (fun c => F c), Finset.sum_range_eq_add_Ico _ (by omega)] at h1
  simp only [Fin.val_zero] at h1
  have h2 : Ico 1 (m + 1) = Icc 1 m := by ext c; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [h2] at h1
  linarith

variable {p : ℕ} [hp : Fact p.Prime]

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

lemma layer_eq {p : ℕ} (hp : 0 < p) (h : ℕ) :
    layer p 1000 h = (p : ℝ) * Jc ((h : ℝ) / p) := by
  unfold layer Jc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [mul_max_of_nonneg _ _ hpR.le, mul_zero, mul_sub, mul_div_cancel₀ _ hpR.ne']
  congr 1; ring


lemma lrow_lt {k β : ℤ} {i : ℕ} (hi : i < lrow k β) : 2 * (i : ℚ) + β < k := by
  unfold lrow at hi
  have : 2 * (i : ℤ) + β < k := by omega
  exact_mod_cast this

end ValDefect



/-! ## The outer per-prime bound (`Apery/Growth/Constants.lean`, `OuterPrime.lean`) -/

section OuterPrime

/-!
# Uniform bounds for the additive constants of the per-prime bounds
-/

open Finset


lemma abs_bcoef_le (h : ℕ → ℝ) {M : ℝ} (hM : ∀ a ≤ 2, |h a| ≤ M) (i : Fin 3) : |bcoef h i| ≤ 2 * M := by
  have h0 := hM 0 (by norm_num); have h1 := hM 1 (by norm_num); have h2 := hM 2 (by norm_num)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans h0
  fin_cases i <;> simp only [bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · linarith
  · exact (abs_sub _ _).trans (by linarith)
  · exact (abs_sub _ _).trans (by linarith)

lemma abs_bcoef2_le (h : ℕ → ℕ → ℝ) {M : ℝ} (hM : ∀ a ≤ 2, ∀ b ≤ 2, |h a b| ≤ M) (i j : Fin 3) :
    |bcoef (fun a => bcoef (fun b => h a b) j) i| ≤ 4 * M := by
  have := abs_bcoef_le (fun a => bcoef (fun b => h a b) j) (M := 2 * M)
    (fun a ha => abs_bcoef_le (fun b => h a b) (fun b hb => hM a ha b hb) j) i
  linarith

lemma psiR_nonneg (k β : ℤ) : 0 ≤ psiR k β := by
  unfold psiR
  refine Finset.sum_nonneg fun i hi => ?_
  have := lrow_lt (Finset.mem_range.mp hi)
  linarith

lemma abs_psiR_le (k β : ℤ) : |(psiR k β : ℝ)| ≤ ((k - β + 1 : ℤ) : ℝ) ^ 2 := by
  have h1 := psiR_nonneg k β
  have h2 := psiR_le k β
  rw [abs_of_nonneg (by exact_mod_cast h1)]
  have : (psiR k β : ℝ) ≤ ((k - β + 1 : ℤ) : ℝ) ^ 2 / 8 := by exact_mod_cast h2
  nlinarith [sq_nonneg ((k - β + 1 : ℤ) : ℝ)]

/-- The inner coefficients. -/
lemma sum_abs_bIn_le {q q' : ℕ} (hq' : q' ≤ q) {k : ℤ} (hk1 : -2 * (q : ℤ) - 6 ≤ k)
    (hk2 : k ≤ 8 * (q : ℤ) + 20) :
    ∑ i, ∑ j, |bIn q q' k i j| ≤ 36 * (22 * (q : ℝ) + 30) ^ 2 := by
  have hM : ∀ a : ℕ, a ≤ 2 → ∀ b : ℕ, b ≤ 2 →
      |(psiR k (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) : ℝ)| ≤ (22 * (q : ℝ) + 30) ^ 2 := by
    intro a ha b hb
    refine (abs_psiR_le _ _).trans ?_
    have hb' : (b : ℤ) ≤ 2 := by exact_mod_cast hb
    have ha' : (a : ℤ) ≤ 2 := by exact_mod_cast ha
    have hq'' : (q' : ℤ) ≤ q := by exact_mod_cast hq'
    have hb0 : (0 : ℤ) ≤ b := by positivity
    have ha0 : (0 : ℤ) ≤ a := by positivity
    have hq0 : (0 : ℤ) ≤ q' := by positivity
    have hbd : |k - (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) + 1| ≤ 22 * (q : ℤ) + 30 := by
      rw [abs_le]; constructor <;> linarith
    have hbdR : |((k - (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) + 1 : ℤ) : ℝ)| ≤
        22 * (q : ℝ) + 30 := by exact_mod_cast hbd
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hbdR 2
  have hb := fun i j => abs_bcoef2_le _ hM i j
  calc ∑ i, ∑ j, |bIn q q' k i j| ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 4 * (22 * (q : ℝ) + 30) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = 36 * (22 * (q : ℝ) + 30) ^ 2 := by simp; ring

/-- The outer coefficients. -/
lemma abs_GO_le (q a d : ℕ) :
    |(GO q a d : ℝ)| ≤ (2 * (q : ℝ) + a) * ((q : ℝ) + a + 3) := by
  unfold GO
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ range (2 * q + a - 2), |min 0 ((i : ℝ) + 3 * d - (2 * (q : ℝ) + a + 4) / 2)|
      ≤ ∑ _i ∈ range (2 * q + a - 2), ((q : ℝ) + a + 3) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_le]
        have : (0 : ℝ) ≤ i := by positivity
        have : (0 : ℝ) ≤ d := by positivity
        have ha : (0 : ℝ) ≤ a := by positivity
        push_cast
        constructor
        · have := min_le_right (0 : ℝ) ((i : ℝ) + 3 * d - ((2 * q + a : ℝ) + 4) / 2)
          have hq0 : (0 : ℝ) ≤ q := by positivity
          have := le_min (show -((q : ℝ) + a + 3) ≤ 0 by linarith) (show -((q : ℝ) + a + 3) ≤
            (i : ℝ) + 3 * d - ((2 * q + a : ℝ) + 4) / 2 by linarith)
          exact this
        · have := min_le_left (0 : ℝ) ((i : ℝ) + 3 * d - ((2 * q + a : ℝ) + 4) / 2)
          linarith [show (0 : ℝ) ≤ (q : ℝ) + a + 3 by positivity]
    _ = ((2 * q + a - 2 : ℕ) : ℝ) * ((q : ℝ) + a + 3) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 * (q : ℝ) + a) * ((q : ℝ) + a + 3) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : 2 * q + a - 2 ≤ 2 * q + a := Nat.sub_le _ _
        exact_mod_cast this

lemma sum_abs_bGO_le {q : ℕ} (hq : q ≤ 2) : ∑ i, ∑ j, |bGO q i j| ≤ 36 * 70 := by
  have hM : ∀ a : ℕ, a ≤ 2 → ∀ b : ℕ, b ≤ 2 → |(GO q a b : ℝ)| ≤ 70 := by
    intro a ha b _
    refine (abs_GO_le q a b).trans ?_
    have hq' : (q : ℝ) ≤ 2 := by exact_mod_cast hq
    have ha' : (a : ℝ) ≤ 2 := by exact_mod_cast ha
    have : (0 : ℝ) ≤ q := by positivity
    have : (0 : ℝ) ≤ a := by positivity
    nlinarith
  have hb := fun i j => abs_bcoef2_le _ hM i j
  calc ∑ i, ∑ j, |bGO q i j| ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 4 * (70 : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ ≤ 36 * 70 := by simp; norm_num


/-!
# The outer range: class counts

For a nonzero class `c`, the number of class members in `(X, Y]` is `SX p Y c - SX p X c`.
-/

open Finset


variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

lemma jc_eq_iff (hm : 2 * m + 1 = p) (j : ℕ) (c : Fin (m + 1)) :
    jc hm j = c ↔ ((j : ℤ) : ZMod p) = (((c : ℕ) : ℤ) : ZMod p) ∨
      ((j : ℤ) : ZMod p) = -(((c : ℕ) : ℤ) : ZMod p) := by
  unfold jc
  constructor
  · intro h
    rcases ccls_spec hm ((j : ℤ) : ZMod p) with h1 | h1 <;> rw [h] at h1
    · left; exact h1.symm
    · right; rw [h1]; ring
  · intro h
    refine (ccls_unique hm _ c ?_).symm
    rcases h with h | h
    · left; exact h.symm
    · right; rw [h]; ring

lemma neg_ne_self_zmod (hm : 2 * m + 1 = p) {x : ZMod p} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  have h2 : (2 : ZMod p) * x = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero_zmod hm h3
  · exact hx h3

lemma card_class (hm : 2 * m + 1 = p) {c : Fin (m + 1)} (hc : c ≠ 0) (X : ℕ) :
    ((Icc 1 X).filter fun j => jc hm j = c).card = SX p X (((c : ℕ) : ℤ) : ZMod p) := by
  have hc0 : (((c : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    intro h
    apply hc
    have := (ccls_eq_zero_iff hm _).mpr h
    rw [ccls_self hm c] at this
    exact this
  unfold SX
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_union, jc_eq_iff hm]
    tauto
  · rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact neg_ne_self_zmod hm hc0 (h1.2.symm.trans h2.2)

lemma card_class_Ioc (hm : 2 * m + 1 = p) {c : Fin (m + 1)} (hc : c ≠ 0) {X Y : ℕ} (hXY : X ≤ Y) :
    ((Icc (X + 1) Y).filter fun j => jc hm j = c).card =
      SX p Y (((c : ℕ) : ℤ) : ZMod p) - SX p X (((c : ℕ) : ℤ) : ZMod p) := by
  rw [← card_class hm hc, ← card_class hm hc]
  have hsplit : (Icc 1 Y).filter (fun j => jc hm j = c) =
      (Icc 1 X).filter (fun j => jc hm j = c) ∪ (Icc (X + 1) Y).filter (fun j => jc hm j = c) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint ((Icc 1 X).filter (fun j => jc hm j = c))
      ((Icc (X + 1) Y).filter (fun j => jc hm j = c)) := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  omega

section
variable (hm : 2 * m + 1 = p) {n : ℕ} (hn : 1 ≤ n) (hout : 40 * n < 3 * p)

include hm hn hout in
lemma three_n_le_m : 3 * n ≤ m := by omega

include hm in
lemma SX_small {X : ℕ} (hX : X < p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ m) :
    SX p X (((c : ℕ) : ℤ) : ZMod p) = aCnt p X c := by
  rw [SX_class hm hc1 hcm, Nat.div_eq_of_lt hX, Nat.mod_eq_of_lt hX]; ring

include hn hout in
lemma class_data {c : Fin (m + 1)} (hc : c ≠ 0) :
    LoC hm n c = 2 * (40 * n / p) + aCnt p (40 * n % p) c - aCnt p (3 * n) c ∧
      nbC hm n c = 2 * (40 * n / p) + aCnt p (40 * n % p) c - 2 ∧
      ellC hm n c = 2 * (40 * n / p) + aCnt p (40 * n % p) c ∧
      delC n c = aCnt p (3 * n) c := by
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc
    · exact h
  have hcm := Nat.lt_succ_iff.mp c.isLt
  have h3m := three_n_le_m hm hn hout
  have hN : 3 * n < p := by omega
  have hK := SX_class hm hc1 hcm (40 * n)
  have hNs := SX_small hm hN hc1 hcm
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold LoC tailC tailO
    rw [card_class_Ioc hm hc (by omega), hK, hNs]
  · unfold nbC bigC tailC tailO
    rw [Finset.filter_filter]
    rcases le_or_gt p (40 * n) with hpK | hpK
    · have e : (Icc (3 * n + 1) (40 * n)).filter (fun j => jc hm j = c ∧ p < j) =
          (Icc (p + 1) (40 * n)).filter (fun j => jc hm j = c) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [e, card_class_Ioc hm hc hpK, hK, SX_class hm hc1 hcm p, Nat.div_self (by omega),
        Nat.mod_self]
      unfold aCnt; split_ifs <;> omega
    · have e : (Icc (3 * n + 1) (40 * n)).filter (fun j => jc hm j = c ∧ p < j) = ∅ := by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [e, Finset.card_empty, Nat.div_eq_of_lt hpK]
      unfold aCnt; split_ifs <;> omega
  · unfold ellC; rw [card_class hm hc, hK]
  · unfold delC aCnt; split_ifs <;> omega

include hn hout in
lemma sum_wO_class {c : Fin (m + 1)} (hc : c ≠ 0) :
    ∑ i ∈ range (LoC hm n c), wO hm n c i =
      GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) := by
  obtain ⟨hL, hnb, hl, hd⟩ := class_data hm hn hout hc
  have hδ : aCnt p (3 * n) c ≤ 1 := by
    have := three_n_le_m hm hn hout
    have hcm := Nat.lt_succ_iff.mp c.isLt
    unfold aCnt; split_ifs <;> omega
  have hsub : nbC hm n c ≤ LoC hm n c := by rw [hL, hnb]; omega
  rw [← Finset.sum_range_add_sum_Ico _ hsub]
  have h0 : ∑ i ∈ Ico (nbC hm n c) (LoC hm n c), wO hm n c i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    unfold wO; rw [if_neg hc, if_neg (by have := (Finset.mem_Ico.mp hi).1; omega)]
  rw [h0, add_zero, hnb]
  unfold GO
  refine Finset.sum_congr rfl fun i hi => ?_
  unfold wO
  rw [if_neg hc, if_pos (by rw [hnb]; exact Finset.mem_range.mp hi), hl, hd]

include hn hout in
lemma sum_wO_zero : -4 ≤ ∑ i ∈ range (LoC hm n 0), wO hm n 0 i := by
  have hL : LoC hm n 0 ≤ 2 := by
    unfold LoC tailC tailO
    have hsub : (Icc (3 * n + 1) (40 * n)).filter (fun j => jc hm j = 0) ⊆ {p, 2 * p} := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
      have hdvd : p ∣ j := by exact_mod_cast (jc_eq_zero_iff hm j).mp hj2
      obtain ⟨t, rfl⟩ := hdvd
      have := Finset.mem_Icc.mp hj1
      have ht1 : 1 ≤ t := by rcases Nat.eq_zero_or_pos t with h | h
                             · subst h; omega
                             · exact h
      have ht3 : t < 3 := by
        by_contra h; rw [not_lt] at h
        have : p * 3 ≤ p * t := Nat.mul_le_mul_left _ h
        omega
      interval_cases t <;> simp [mul_comm]
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  have : ∀ i, -2 ≤ wO hm n 0 i := by
    intro i; unfold wO; rw [if_pos rfl]; split_ifs <;> norm_num
  calc (-4 : ℚ) ≤ ∑ _i ∈ range (LoC hm n 0), (-2 : ℚ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : (LoC hm n 0 : ℚ) ≤ 2 := by exact_mod_cast hL
        linarith
    _ ≤ _ := Finset.sum_le_sum fun i _ => this i

end

/-- The additive error of the outer bound. -/
noncomputable def Cout (n p : ℕ) : ℝ := 5 * ∑ i, ∑ j, |bGO (40 * n / p) i j| + 11

section
variable {n : ℕ} (hn : 33 ≤ n) (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p)
  (hout : 40 * n < 3 * p) (hle : p ≤ 2 * (37 * n)) (hsq : 2 * (40 * n) < p ^ 2)

set_option maxHeartbeats 1000000 in
include hn hodd hp7 hout hle hsq in
/-- **The outer per-prime bound.** -/
theorem outer_Lp_le : -(Lp n p : ℝ) ≤ (p : ℝ) * Eout (40 * n / p) + Cout n p := by
  have hp0 : 0 < p := by omega
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp0
  have hN : 3 * n < p := by omega
  have hOK : OuterOK n p := ⟨hodd, hp7, hout, hsq, hN⟩
  have hLp : Lp n p = vSK n p + ⌊WO n p⌋ := by
    unfold Lp Mcut; rw [if_neg (by omega), if_neg (by omega), if_pos hOK]
  set m := p / 2 with hmdef
  have hWO : WO n p = 2 * ∑ c, ∑ i ∈ range (LoC hodd n c), wO hodd n c i -
      ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ) := by
    unfold WO; rw [dif_pos hp.out, dif_pos hodd]
  -- the class sum
  have hsplit : ∑ c, ∑ i ∈ range (LoC hodd n c), wO hodd n c i =
      ∑ i ∈ range (LoC hodd n 0), wO hodd n 0 i +
        ∑ c ∈ Icc 1 m, GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
    congr 1
    rw [Finset.sum_congr rfl fun c hc => sum_wO_class hodd (by omega) hout (Finset.mem_erase.mp hc).1]
    exact sum_erase_zero_eq_Icc (fun c => GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c))
  have hZ := sum_wO_zero hodd (n := n) (by omega) hout
  -- the continuous class sum
  have hcs := class_sum_approx hodd (Nat.mod_lt (40 * n) hp0) (Nat.mod_lt (3 * n) hp0)
    (fun a b => (GO (40 * n / p) a b : ℝ))
  rw [Nat.mod_eq_of_lt hN] at hcs
  rw [abs_le] at hcs
  have hcsQ : ((∑ c ∈ Icc 1 m, GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) : ℚ) : ℝ) =
      ∑ c ∈ Icc 1 m, (GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) : ℝ) := by
    push_cast; rfl
  -- the rank loss
  have hr : ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℝ) ≤
      (p : ℝ) * max (0 : ℝ) (13 / 10 * (40 * (n : ℝ) / (p : ℝ)) - 2) + 2 := by
    have e : (p : ℝ) * max (0 : ℝ) (13 / 10 * (40 * (n : ℝ) / (p : ℝ)) - 2) =
        max 0 (52 * (n : ℝ) - 2 * p) := by
      rw [mul_max_of_nonneg _ _ hpR0.le, mul_zero]; congr 1; field_simp; ring
    rw [e]
    have hm0 := le_max_left (0 : ℝ) (52 * n - 2 * p)
    have hm1 := le_max_right (0 : ℝ) (52 * n - 2 * p)
    rcases Nat.lt_or_ge (37 * n) (((2 * p + 22 * n - 3) - (37 * n - 1))) with h | h
    · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith
    · have hR : 37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) ≤ 52 * n + 2 - 2 * p := by omega
      rcases le_or_gt (52 * n + 2) (2 * p) with h5 | h5
      · have : 37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) = 0 := by omega
        rw [this]; push_cast; linarith
      · have h2 := (Nat.cast_le (α := ℝ)).mpr hR
        have h6 : ((52 * n + 2 - 2 * p : ℕ) : ℝ) = 52 * (n : ℝ) + 2 - 2 * p := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [h6] at h2
        linarith
  -- `v_p(S_K)`
  have hv := neg_vSK_le (p := p) (n := n) (by omega) (by omega) (by nlinarith) (by nlinarith) 1000
    (by omega)
  rw [Nat.div_eq_of_lt hN] at hv
  rw [layer_eq hp0] at hv
  -- the target
  have hx : (40 * n / p : ℝ) = ((40 * n : ℕ) : ℝ) / (p : ℕ) := by push_cast; ring
  have hfl : ⌊(40 * n / p : ℝ)⌋₊ = 40 * n / p := by rw [hx, Nat.floor_div_eq_div]
  have hfK : Int.fract ((40 * n / p : ℝ)) = ((40 * n % p : ℕ) : ℝ) / p := by
    rw [hx]; exact Int.fract_div_natCast_eq_div_natCast_mod
  have hfN : Int.fract ((3 : ℝ) / 40 * (40 * n / p)) = ((3 * n : ℕ) : ℝ) / p := by
    rw [show (3 : ℝ) / 40 * (40 * n / p) = ((3 * n : ℕ) : ℝ) / (p : ℕ) by push_cast; ring,
      Int.fract_div_natCast_eq_div_natCast_mod, Nat.mod_eq_of_lt hN]
  have hu : ((37 * n : ℕ) : ℝ) / p = 37 / 40 * (40 * n / p) := by push_cast; ring
  rw [hu] at hv
  have e1 : ((37 * n : ℕ) : ℝ) = (p : ℝ) * (37 / 40 * (40 * n / p)) := by push_cast; field_simp
  rw [e1] at hv
  have hfl2 : ((40 * n / p : ℕ) : ℝ) = (⌊(40 * n / p : ℝ)⌋₊ : ℝ) := by rw [hfl]
  unfold Eout Cout
  rw [hfl, hfK, hfN]
  have hflo := Int.lt_floor_add_one (WO n p)
  have hfloR : ((WO n p : ℚ) : ℝ) < ((⌊WO n p⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast hflo
  have hWOR : ((WO n p : ℚ) : ℝ) = 2 * (((∑ i ∈ range (LoC hodd n 0), wO hodd n 0 i : ℚ) : ℝ) +
      ∑ c ∈ Icc 1 m, (GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) : ℝ)) -
      ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℝ) := by
    rw [hWO, hsplit]; push_cast; ring
  push_cast at hWOR
  rw [hLp]
  push_cast
  have hZR : (-4 : ℝ) ≤ ((∑ i ∈ range (LoC hodd n 0), wO hodd n 0 i : ℚ) : ℝ) := by exact_mod_cast hZ
  push_cast at hZR
  have hb : ∀ i j, bcoef (fun a => bcoef (fun b => (GO (40 * n / p) a b : ℝ)) j) i =
      bGO (40 * n / p) i j := fun i j => rfl
  simp only [hb] at hcs
  push_cast at hcs
  linarith [hcs.1]

end

end OuterPrime



/-! ## Summation over the outer range (`Apery/Growth/Assembly2.lean`, `Assembly3.lean`) -/

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

lemma floor_Kr_outer (n : ℕ) : ⌊Kr n / (20 / 37)⌋₊ = 74 * n := by
  rw [show Kr n / (20 / 37) = ((74 * n : ℕ) : ℝ) by simp [Kr]; ring]
  exact Nat.floor_natCast _

lemma Cout_le {n p : ℕ} (hq : 40 * n / p ≤ 2) : Cout n p ≤ 10 ^ 5 := by
  unfold Cout
  have := sum_abs_bGO_le hq
  linarith


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

lemma range4_le {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (40 * n / 3) (2 * (37 * n)), cPrime k * (-(Lp n k : ℝ)) ≤
      psum Eout (20 / 37) 3 (Kr n) + 10 ^ 5 * Chebyshev.theta (2 * (37 * n) : ℕ) := by
  have hps : psum Eout (20 / 37) 3 (Kr n) =
      ∑ k ∈ Ioc (40 * n / 3) (2 * (37 * n)), (k : ℝ) * cPrime k * Eout (Kr n / k) := by
    unfold psum
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, floor_Kr_div n 3 (by norm_num), floor_Kr_outer,
      show 74 * n = 2 * (37 * n) by ring]
  rw [hps]
  refine range_sum_le (fun k => -(Lp n k : ℝ)) Eout (Kr n) (10 ^ 5) (by norm_num) fun k hk hp => ?_
  have hk' := Finset.mem_Ioc.mp hk
  obtain ⟨hp7, hodd, _, hsq, _, _⟩ := big_prime_facts hn (by omega) hp
  have := Fact.mk hp
  have hout : 40 * n < 3 * k := by
    have := Nat.lt_div_mul_add (a := 40 * n) (show 0 < 3 by norm_num); omega
  have h := outer_Lp_le (p := k) (n := n) (by omega) hodd hp7 hout hk'.2 hsq
  have hq2 : 40 * n / k ≤ 2 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))
  have hC := Cout_le (n := n) (p := k) hq2
  have e : Kr n / k = 40 * n / k := by simp [Kr]
  rw [e]
  linarith

end Summation



end Apery
end Port0


open Finset in
/-- The platform target `Apery.range4_le`, restated at top level as `solution`. -/
theorem solution {n : ℕ} (hn : 10400 ≤ n) :
    ∑ k ∈ Ioc (40 * n / 3) (2 * (37 * n)), Apery.cPrime k * (-(Apery.Lp n k : ℝ)) ≤
      Apery.psum Apery.Eout (20 / 37) 3 (Apery.Kr n) +
        10 ^ 5 * Chebyshev.theta (2 * (37 * n) : ℕ) :=
  Apery.range4_le hn
