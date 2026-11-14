-- Prove2me | Definitions.Def_RPLib_S3_HypParG
-- name    : RPLib_S3_HypParG
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:29:53.268697+00:00
-- url     : https://prove2.me/theorems/730cfccb-7d1d-47e8-b290-4130241186e1
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part G: averaged level counts of triangular matrices
-- statement:
--   For integers $D, a, d$: $\sum_{b \bmod M} \#\{v \text{ of exact order } M : \begin{pmatrix} a & b \\ 0 & d \end{pmatrix} v = D v\} = M \sum_{h \mid M} [h \mid D - a,\ M/h \mid D - d]\, \varphi(h)\varphi(M/h)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977

import Mathlib
import Definitions.Def_RPLib_S3_HypParF
import Definitions.Def_RPLib_S3_HypParI

/-!
# S3-HypParTerms, part G (O8, step G1): the level count of upper-triangular matrices, averaged over `b`

For integers `D a d`,
`Σ_{b mod M} levelCount M D [[a, b], [0, d]] = M Σ_{h ∣ M} [h ∣ D - a ∧ M/h ∣ D - d] φ(h) φ(M/h)`
(`sum_levelCount_ut`). Proof: swap the `b`- and `v`-sums; for `v = (v₀, v₁)` of exact order `M` put
`h = gcd(M, v₁)`; then `d v₁ = D v₁ ↔ M/h ∣ D - d`, the equation `b v₁ = (D - a) v₀` has `h` solutions if
`h ∣ D - a` and none otherwise (`v₀` is prime to `h`), `#{v₀ : gcd(v₀, h) = 1} = (M/h) φ(h)` and
`#{v₁ : gcd(M, v₁) = h} = φ(M/h)`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

section CountG

variable {M : ℕ} [NeZero M]

/-- Counting a predicate of `x.val` over `ZMod M` is counting it on `[0, M)`. -/
lemma card_filter_val (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun x : ZMod M => P x.val).card = ((range M).filter P).card := by
  refine Finset.card_nbij' (fun x : ZMod M => x.val) (fun n : ℕ => (n : ZMod M)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨ZMod.val_lt x, hx⟩
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn.1]
    exact hn.2
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hn.1]

/-- A `K`-periodic predicate on `[0, qK)` is counted `q` times its count on `[0, K)`. -/
lemma card_filter_range_periodic (P : ℕ → Prop) [DecidablePred P] (K : ℕ)
    (hP : ∀ n, P (n + K) ↔ P n) (q : ℕ) :
    ((range (q * K)).filter P).card = q * ((range K).filter P).card := by
  have hper : ∀ j k, P (j * K + k) ↔ P k := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      rw [show (j + 1) * K + k = (j * K + k) + K by ring, hP, ih]
  have hshift : ∀ j, Nat.count (fun k => P (j * K + k)) K = Nat.count P K := by
    intro j
    simp only [Nat.count_eq_card_filter_range]
    exact congrArg Finset.card (Finset.filter_congr fun k _ => hper j k)
  have key : ∀ j, Nat.count P (j * K) = j * Nat.count P K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show (j + 1) * K = j * K + K by ring, Nat.count_add, ih, hshift j]
      ring
  simpa only [Nat.count_eq_card_filter_range] using key q

/-- `#{x : ZMod M | gcd(x, h) = 1} = (M/h) φ(h)` for `h ∣ M`. -/
lemma card_coprime_val {h : ℕ} (hh : h ∣ M) :
    (univ.filter fun x : ZMod M => Nat.Coprime x.val h).card = M / h * Nat.totient h := by
  rw [card_filter_val (fun n => Nat.Coprime n h)]
  have e : range M = range (M / h * h) := by rw [Nat.div_mul_cancel hh]
  rw [e, card_filter_range_periodic (fun n => Nat.Coprime n h) h
    (fun n => Nat.coprime_add_self_left) (M / h), Nat.totient_eq_card_coprime]
  congr 1
  exact congrArg Finset.card (Finset.filter_congr fun n _ => Nat.coprime_comm)

/-- `#{x : ZMod M | gcd(M, x) = h} = φ(M/h)` for `h ∣ M`. -/
lemma card_gcd_val {h : ℕ} (hh : h ∣ M) :
    (univ.filter fun x : ZMod M => Nat.gcd M x.val = h).card = Nat.totient (M / h) := by
  rw [card_filter_val (fun n => Nat.gcd M n = h), Nat.totient_div_of_dvd hh]

/-- `c x = 0` in `ZMod M` iff `M / gcd(M, x) ∣ c`. -/
lemma intCast_mul_eq_zero_iff (c : ℤ) (x : ZMod M) :
    (c : ZMod M) * x = 0 ↔ ((M / Nat.gcd M x.val : ℕ) : ℤ) ∣ c := by
  have hg : 0 < Nat.gcd M x.val := Nat.gcd_pos_of_pos_left _ (NeZero.pos M)
  have hcop := Nat.coprime_div_gcd_div_gcd hg
  have eM : (M : ℤ) = (Nat.gcd M x.val : ℤ) * ((M / Nat.gcd M x.val : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
  have ex : (x.val : ℤ) = (Nat.gcd M x.val : ℤ) * ((x.val / Nat.gcd M x.val : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
  have key : (c : ZMod M) * x = ((c * (x.val : ℤ) : ℤ) : ZMod M) := by
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [key, ZMod.intCast_zmod_eq_zero_iff_dvd, eM, ex,
    show c * ((Nat.gcd M x.val : ℤ) * ((x.val / Nat.gcd M x.val : ℕ) : ℤ)) =
      (Nat.gcd M x.val : ℤ) * (c * ((x.val / Nat.gcd M x.val : ℕ) : ℤ)) by ring,
    mul_dvd_mul_iff_left (by exact_mod_cast hg.ne')]
  constructor
  · intro h
    exact (Nat.isCoprime_iff_coprime.2 hcop).dvd_of_dvd_mul_right h
  · intro h
    exact h.mul_right _

/-- `#{b : b x = 0} = gcd(M, x)`. -/
lemma card_mul_eq_zero (x : ZMod M) :
    (univ.filter fun b : ZMod M => b * x = 0).card = Nat.gcd M x.val := by
  have hgpos : 0 < Nat.gcd M x.val := Nat.gcd_pos_of_pos_left _ (NeZero.pos M)
  have hK : 0 < M / Nat.gcd M x.val :=
    Nat.div_pos (Nat.gcd_le_left _ (NeZero.pos M)) hgpos
  have e1 : (univ.filter fun b : ZMod M => b * x = 0) =
      univ.filter fun b : ZMod M => M / Nat.gcd M x.val ∣ b.val := by
    apply Finset.filter_congr
    intro b _
    have h := intCast_mul_eq_zero_iff (b.val : ℤ) x
    rw [Int.cast_natCast, ZMod.natCast_zmod_val] at h
    rw [h, Int.natCast_dvd_natCast]
  rw [e1, card_filter_val (fun n => M / Nat.gcd M x.val ∣ n)]
  have e2 : range M = range (Nat.gcd M x.val * (M / Nat.gcd M x.val)) := by
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
  rw [e2, card_filter_range_periodic (fun n => M / Nat.gcd M x.val ∣ n) (M / Nat.gcd M x.val)
    (fun n => Nat.dvd_add_self_right) (Nat.gcd M x.val)]
  have e3 : (range (M / Nat.gcd M x.val)).filter (fun n => M / Nat.gcd M x.val ∣ n) = {0} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact Nat.eq_zero_of_dvd_of_lt h2 h1
    · rintro rfl
      exact ⟨hK, dvd_zero _⟩
  rw [e3, Finset.card_singleton, mul_one]

/-- `#{b : b x = e v₀} = [gcd(M, x) ∣ e] gcd(M, x)` when `v₀` is prime to `gcd(M, x)`. -/
lemma card_mul_eq (x v0 : ZMod M) (e : ℤ) (hc : Nat.Coprime v0.val (Nat.gcd M x.val)) :
    (univ.filter fun b : ZMod M => b * x = (e : ZMod M) * v0).card =
      if ((Nat.gcd M x.val : ℕ) : ℤ) ∣ e then Nat.gcd M x.val else 0 := by
  split_ifs with he
  · obtain ⟨r, hr⟩ := he
    have hb : ((Nat.gcd M x.val : ℕ) : ZMod M) = x * (Nat.gcdB M x.val : ZMod M) := by
      have h2 := congrArg (Int.cast : ℤ → ZMod M) (Nat.gcd_eq_gcd_ab M x.val)
      simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, zero_add,
        ZMod.natCast_zmod_val] at h2
      exact h2
    have hb0 : ((Nat.gcdB M x.val : ZMod M) * (r : ZMod M) * v0) * x = (e : ZMod M) * v0 := by
      rw [hr, Int.cast_mul, Int.cast_natCast, hb]
      ring
    refine Eq.trans ?_ (card_mul_eq_zero x)
    refine Finset.card_nbij' (fun b => b - (Nat.gcdB M x.val : ZMod M) * (r : ZMod M) * v0)
      (fun b => b + (Nat.gcdB M x.val : ZMod M) * (r : ZMod M) * v0) ?_ ?_ ?_ ?_
    · intro b hb'
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb' ⊢
      rw [sub_mul, hb', hb0, sub_self]
    · intro b hb'
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb' ⊢
      rw [add_mul, hb', hb0, zero_add]
    · intro b _
      simp
    · intro b _
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b _ hbx
    apply he
    have h1 : (((b.val : ℤ) * (x.val : ℤ) : ℤ) : ZMod M) = ((e * (v0.val : ℤ) : ℤ) : ZMod M) := by
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
      exact hbx
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have hgM : ((Nat.gcd M x.val : ℕ) : ℤ) ∣ (M : ℤ) :=
      Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
    have hgx : ((Nat.gcd M x.val : ℕ) : ℤ) ∣ (b.val : ℤ) * (x.val : ℤ) :=
      (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).mul_left _
    have h3 : ((Nat.gcd M x.val : ℕ) : ℤ) ∣ e * (v0.val : ℤ) := by
      have h4 := dvd_add (hgM.trans h1) hgx
      rwa [sub_add_cancel] at h4
    exact (Nat.isCoprime_iff_coprime.2 hc.symm).dvd_of_dvd_mul_right h3

/-- `levelCount` of `[[a, b], [0, d]]`, written with `v₀`, `v₁`. -/
lemma levelCount_ut_eq (D a d : ℤ) (b : ZMod M) :
    S3.levelCount M (D : ZMod M) (ut a (b.val : ℤ) d) =
      (univ.filter fun v : Fin 2 → ZMod M =>
        Nat.Coprime (v 0).val (Nat.gcd M (v 1).val) ∧ ((D - d : ℤ) : ZMod M) * v 1 = 0 ∧
          b * v 1 = ((D - a : ℤ) : ZMod M) * v 0).card := by
  unfold S3.levelCount
  congr 1
  apply Finset.filter_congr
  intro v _
  have hg : Nat.Coprime (Nat.gcd (v 0).val (v 1).val) M ↔ Nat.Coprime (v 0).val (Nat.gcd M (v 1).val) := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, Nat.gcd_assoc, Nat.gcd_comm (v 1).val M]
  have h1 : (a : ZMod M) * v 0 + (((b.val : ℕ) : ℤ) : ZMod M) * v 1 = (D : ZMod M) * v 0 ↔
      b * v 1 = ((D - a : ℤ) : ZMod M) * v 0 := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_sub]
    constructor <;> intro h <;> linear_combination h
  have h2 : (d : ZMod M) * v 1 = (D : ZMod M) * v 1 ↔ ((D - d : ℤ) : ZMod M) * v 1 = 0 := by
    rw [Int.cast_sub]
    constructor <;> intro h <;> linear_combination -h
  rw [show (∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0) ↔ _ from isExact_iff_coprime v, eig_ut_iff, h1, h2, hg]
  exact ⟨fun ⟨x, y, z⟩ => ⟨x, z, y⟩, fun ⟨x, z, y⟩ => ⟨x, y, z⟩⟩

/-- The weight `[h ∣ D - a ∧ M/h ∣ D - d] h`. -/
def cntG (M : ℕ) (D a d : ℤ) (h : ℕ) : ℕ :=
  if (h : ℤ) ∣ D - a ∧ ((M / h : ℕ) : ℤ) ∣ D - d then h else 0

lemma inner_b (D a d : ℤ) (v : Fin 2 → ZMod M) :
    (∑ b : ZMod M, if (Nat.Coprime (v 0).val (Nat.gcd M (v 1).val) ∧ ((D - d : ℤ) : ZMod M) * v 1 = 0 ∧
        b * v 1 = ((D - a : ℤ) : ZMod M) * v 0) then 1 else 0) =
      (if Nat.Coprime (v 0).val (Nat.gcd M (v 1).val) then 1 else 0) * cntG M D a d (Nat.gcd M (v 1).val) := by
  by_cases hc : Nat.Coprime (v 0).val (Nat.gcd M (v 1).val)
  · rw [if_pos hc, one_mul]
    unfold cntG
    by_cases hd : ((M / Nat.gcd M (v 1).val : ℕ) : ℤ) ∣ D - d
    · simp only [intCast_mul_eq_zero_iff, hd, true_and, and_true]
      rw [← Finset.card_filter]
      have hf : (univ.filter fun b : ZMod M => Nat.Coprime (v 0).val (Nat.gcd M (v 1).val) ∧
          b * v 1 = ((D - a : ℤ) : ZMod M) * v 0) =
          univ.filter fun b : ZMod M => b * v 1 = ((D - a : ℤ) : ZMod M) * v 0 :=
        Finset.filter_congr fun b _ => and_iff_right hc
      rw [hf, card_mul_eq _ _ _ hc]
    · simp only [intCast_mul_eq_zero_iff, hd, false_and, and_false, ↓reduceIte,
        Finset.sum_const_zero]
  · simp only [hc, false_and, ↓reduceIte, Finset.sum_const_zero, zero_mul]

/-- **G1.** `Σ_{b mod M} levelCount M D [[a, b], [0, d]] = M Σ_{h ∣ M} [h ∣ D - a ∧ M/h ∣ D - d] φ(h) φ(M/h)`. -/
theorem sum_levelCount_ut (D a d : ℤ) :
    ∑ b : ZMod M, S3.levelCount M (D : ZMod M) (ut a (b.val : ℤ) d) =
      M * ∑ h ∈ M.divisors,
        (if (h : ℤ) ∣ D - a ∧ ((M / h : ℕ) : ℤ) ∣ D - d then Nat.totient h * Nat.totient (M / h) else 0) := by
  calc ∑ b : ZMod M, S3.levelCount M (D : ZMod M) (ut a (b.val : ℤ) d)
      = ∑ v : Fin 2 → ZMod M, (if Nat.Coprime (v 0).val (Nat.gcd M (v 1).val) then 1 else 0) *
          cntG M D a d (Nat.gcd M (v 1).val) := by
        simp_rw [levelCount_ut_eq, Finset.card_filter]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun v _ => inner_b D a d v
    _ = ∑ p : ZMod M × ZMod M, (if Nat.Coprime p.1.val (Nat.gcd M p.2.val) then 1 else 0) *
          cntG M D a d (Nat.gcd M p.2.val) :=
        Fintype.sum_equiv (finTwoArrowEquiv (ZMod M)) _ _ (fun _ => by rfl)
    _ = ∑ x1 : ZMod M, ∑ x0 : ZMod M, (if Nat.Coprime x0.val (Nat.gcd M x1.val) then 1 else 0) *
          cntG M D a d (Nat.gcd M x1.val) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ x1 : ZMod M, (M / Nat.gcd M x1.val * Nat.totient (Nat.gcd M x1.val)) *
          cntG M D a d (Nat.gcd M x1.val) := by
        refine Finset.sum_congr rfl fun x1 _ => ?_
        rw [← Finset.sum_mul, ← Finset.card_filter, card_coprime_val (Nat.gcd_dvd_left _ _)]
    _ = ∑ h ∈ M.divisors, ∑ x1 ∈ univ.filter (fun x1 : ZMod M => Nat.gcd M x1.val = h),
          (M / h * Nat.totient h) * cntG M D a d h :=
        (Finset.sum_fiberwise_of_maps_to' (s := univ) (t := M.divisors)
          (g := fun x1 : ZMod M => Nat.gcd M x1.val)
          (fun x1 _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, NeZero.ne M⟩)
          (fun h => (M / h * Nat.totient h) * cntG M D a d h)).symm
    _ = ∑ h ∈ M.divisors, Nat.totient (M / h) * ((M / h * Nat.totient h) * cntG M D a d h) := by
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [Finset.sum_const, smul_eq_mul, card_gcd_val (Nat.dvd_of_mem_divisors hh)]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h hh => ?_
        have e : M / h * h = M := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hh)
        unfold cntG
        split_ifs
        · calc Nat.totient (M / h) * ((M / h * Nat.totient h) * h)
              = (M / h * h) * (Nat.totient h * Nat.totient (M / h)) := by ring
            _ = M * (Nat.totient h * Nat.totient (M / h)) := by rw [e]
        · simp

end CountG

end RamanujanPetersson.HypPar


