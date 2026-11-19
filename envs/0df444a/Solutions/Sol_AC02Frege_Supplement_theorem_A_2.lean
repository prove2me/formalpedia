-- Prove2me | solution 1 for AC02Frege.Supplement.theorem_A_2
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T06:11:41.215883+00:00
-- url     : https://prove2.me/submissions/c167c3f4-ec11-4702-9eca-a9b084aa5a21

import Definitions.Def_AC02Frege_Supplement_admissible
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_AC02Frege_PC
import Definitions.Def_SemAC02_Ble
import Mathlib
import Definitions.Def_AC02Frege_rankCounts
import Theorems.Thm_AC02Frege_theorem_A_5_pang_matrix_lemma

section
-- Inlined Solutions.BooleanAlgebra

open MvPolynomial AC02Frege
namespace AC02Frege.BooleanAlgebra

theorem ml_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl]
  rw [h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem ml_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (ML p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial]
    intro t ht v
    have ht' : t = sqfree s := (Finset.mem_singleton.mp (support_monomial_subset ht))
    subst t
    simp [sqfree, Finsupp.mapRange_apply]
  | add p q hp hq =>
    rw [map_add]
    intro s hs v
    rcases Finset.mem_union.mp (support_add hs) with hs | hs
    · exact hp s hs v
    · exact hq s hs v


theorem sqfree_support {V : Type*} (s : V →₀ ℕ) : (sqfree s).support = s.support := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, sqfree, Finsupp.mapRange_apply]
  omega

theorem sqfree_eq_self {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) : sqfree s = s := by
  ext i
  simp only [sqfree, Finsupp.mapRange_apply, min_eq_left (hs i)]

theorem ml_of_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : ML p = p := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [sqfree_eq_self s (hp s hs)]

theorem ml_idempotent {V : Type*} (p : MvPolynomial V (ZMod 2)) : ML (ML p) = ML p :=
  ml_of_multilinear _ (ml_multilinear p)

theorem eval_ml {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (ML p) = eval x p := by
  classical
  have hpow (a : ZMod 2) (k : ℕ) : a ^ min k 1 = a ^ k := by
    fin_cases a
    · change (0 : ZMod 2) ^ min k 1 = (0 : ZMod 2) ^ k
      cases k <;> simp
    · change (1 : ZMod 2) ^ min k 1 = (1 : ZMod 2) ^ k
      simp
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial, eval_monomial, eval_monomial]
    congr 1
    simp only [Finsupp.prod, sqfree_support]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [sqfree, Finsupp.mapRange_apply] using hpow (x i) (s i)
  | add p q hp hq => simp only [map_add, hp, hq]

theorem multilinear_ext {V : Type} [Finite V]
    {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (h : ∀ x : V → ZMod 2, eval x p = eval x q) : p = q := by
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero V (ZMod 2) (p - q)
  · intro x; simp only [map_sub, h x, sub_self]
  · have hp' : p ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V p 1).mpr hp
    have hq' : q ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V q 1).mpr hq
    simpa only [ZMod.card, Nat.reduceSub] using (restrictDegree V (ZMod 2) 1).sub_mem hp' hq'

theorem ml_mul_left {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (ML p * q) = ML (p * q) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [eval_ml, map_mul]

theorem ml_mul_right {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (p * ML q) = ML (p * q) := by
  rw [mul_comm p (ML q), ml_mul_left, mul_comm]

theorem xMon_eq_monomial {V : Type*} (S : Finset V) :
    xMon S = monomial (Finsupp.indicator S (fun _ _ => 1)) (1 : ZMod 2) := by
  classical
  simpa only [xMon, pow_one] using (prod_X_pow (R := ZMod 2) (fun _ : V => 1) S)

theorem indicator_support {V : Type*} (S : Finset V) :
    (Finsupp.indicator S (fun _ _ => (1 : ℕ))).support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, Finsupp.indicator_apply]
  split_ifs <;> simp_all

theorem xMon_multilinear {V : Type*} (S : Finset V) : IsMultilinear (xMon S) := by
  classical
  rw [xMon_eq_monomial]
  intro s hs i
  have heq := Finset.mem_singleton.mp (support_monomial_subset hs)
  subst s
  simp only [Finsupp.indicator_apply]
  split_ifs <;> omega

theorem xMon_eval {V : Type*} (S : Finset V) (x : V → ZMod 2) :
    eval x (xMon S) = ∏ i ∈ S, x i := by
  simp only [xMon, map_prod, eval_X]

theorem xMon_totalDegree {V : Type*} (S : Finset V) : (xMon S).totalDegree = S.card := by
  classical
  rw [xMon_eq_monomial, totalDegree_monomial _ (one_ne_zero : (1 : ZMod 2) ≠ 0)]
  simp only [Finsupp.sum, indicator_support]
  have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finsupp.indicator_apply, hi]
  rw [heq]
  simp

theorem xMon_linearIndependent {V : Type*} :
    LinearIndependent (ZMod 2) (fun S : Finset V => xMon S) := by
  classical
  have hinj : Function.Injective (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) := by
    intro S T h
    have := congrArg Finsupp.support h
    simpa only [indicator_support] using this
  have h := (basisMonomials V (ZMod 2)).linearIndependent.comp
    (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) hinj
  simpa only [Function.comp_def, coe_basisMonomials, xMon_eq_monomial] using h

end AC02Frege.BooleanAlgebra
end

section
-- Inlined Solutions.MajorityFoundation

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace AC02Frege.MajorityFoundation

open Classical

noncomputable def pointPoly {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) : MvPolynomial V (ZMod 2) :=
  ∏ i : V, if i ∈ S then X i else 1 + X i

theorem pointPoly_indicator {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = MvPolynomial.indicator (fun i : V => if i ∈ S then (1 : ZMod 2) else 0) := by
  classical
  unfold pointPoly MvPolynomial.indicator
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp only [hi, ↓reduceIte, ZMod.card, Nat.reduceSub, pow_one]
  · simp only [map_one, CharTwo.sub_eq_add]
    calc
      X i = X i + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + (X i + 1) := by abel
  · simp [CharTwo.sub_eq_add]

theorem pointPoly_multilinear {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    IsMultilinear (pointPoly S) := by
  rw [pointPoly_indicator]
  apply (mem_restrictDegree V _ 1).mp
  simpa only [ZMod.card, Nat.reduceSub] using indicator_mem_restrictDegree
    (fun i : V => if i ∈ S then (1 : ZMod 2) else 0)

theorem pointPoly_eval {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (x : V → ZMod 2) :
    eval x (pointPoly S) =
      if x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) then 1 else 0 := by
  classical
  rw [pointPoly_indicator]
  split_ifs with h
  · subst x; exact eval_indicator_apply_eq_one _
  · exact eval_indicator_apply_eq_zero _ _ h

theorem multilinear_sum {V ι : Type} (S : Finset ι) (f : ι → MvPolynomial V (ZMod 2))
    (hf : ∀ i ∈ S, IsMultilinear (f i)) : IsMultilinear (∑ i ∈ S, f i) := by
  apply (mem_restrictDegree V _ 1).mp
  exact Submodule.sum_mem _ (fun i hi => (mem_restrictDegree V (f i) 1).mpr (hf i hi))

theorem majOne_multilinear (ℓ : ℕ) : IsMultilinear (majOne ℓ) := by
  unfold majOne
  apply multilinear_sum
  intro S _
  simpa only [pointPoly] using pointPoly_multilinear S

theorem eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem point_of_ones {V : Type} [Fintype V] [DecidableEq V] (x : V → ZMod 2) :
    (fun i => if i ∈ Finset.univ.filter (fun i => x i = 1) then (1 : ZMod 2) else 0) = x := by
  classical
  funext i
  rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]

theorem ones_of_point {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    Finset.univ.filter (fun i => (if i ∈ S then (1 : ZMod 2) else 0) = 1) = S := by
  classical
  ext i
  simp

theorem majOne_eval (ℓ : ℕ) (x : Fin ℓ → ZMod 2) :
    eval x (majOne ℓ) = if ℓ / 2 < (Finset.univ.filter (fun i => x i = 1)).card
      then 1 else 0 := by
  classical
  unfold majOne
  simp only [map_sum]
  have hev (S : Finset (Fin ℓ)) := pointPoly_eval S x
  simp only [pointPoly] at hev
  simp only [hev]
  have heq (S : Finset (Fin ℓ)) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro hx; rw [hx, ones_of_point]
    · intro hS; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp

theorem heavy_monomial_absorbs_majority (ℓ : ℕ) (S : Finset (Fin ℓ))
    (hS : ℓ / 2 < S.card) : ML (xMon S * majOne ℓ) = xMon S := by
  apply multilinear_ext (ml_multilinear _) (xMon_multilinear S)
  intro x
  simp only [eval_ml, map_mul]
  by_cases hx : eval x (xMon S) = 0
  · rw [hx, zero_mul]
  · have hsub : S ⊆ Finset.univ.filter (fun i => x i = 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxi : x i ≠ 0 := by
        intro hz
        apply hx
        rw [xMon_eval]
        exact Finset.prod_eq_zero hi hz
      rcases eq_zero_or_one (x i) with hz | ho
      · exact False.elim (hxi hz)
      · exact ho
    have hcard := Finset.card_le_card hsub
    rw [majOne_eval, if_pos (by omega), mul_one]

theorem pointPoly_factor {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = xMon S * ∏ i ∈ Finset.univ.filter (fun i : V => i ∉ S),
      (1 + X i : MvPolynomial V (ZMod 2)) := by
  simp only [pointPoly, Finset.prod_ite]
  congr 1
  rw [xMon]
  apply Finset.prod_congr
  · ext i; simp
  · intro i _; rfl

theorem support_mul_xMon_degree {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (p : MvPolynomial V (ZMod 2))
    (s : V →₀ ℕ) (hs : s ∈ (xMon S * p).support) : S.card ≤ s.sum (fun _ e => e) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul (xMon S) p hs)
  have haeq : a = Finsupp.indicator S (fun _ _ => (1 : ℕ)) := by
    rw [xMon_eq_monomial] at ha
    exact Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  have hsum : (Finsupp.indicator S (fun _ _ => (1 : ℕ))).sum (fun _ e => e) = S.card := by
    simp only [Finsupp.sum, indicator_support]
    have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finsupp.indicator_apply, hi]
    rw [heq]; simp
  rw [← hab]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hsum]
  omega

theorem majOne_support_heavy (ℓ : ℕ) (s : Fin ℓ →₀ ℕ)
    (hs : s ∈ (majOne ℓ).support) : ℓ / 2 < s.sum (fun _ e => e) := by
  classical
  unfold majOne at hs
  obtain ⟨S, hS, hsS⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have hheavy := (Finset.mem_filter.mp hS).2
  change s ∈ (pointPoly S).support at hsS
  rw [pointPoly_factor] at hsS
  exact lt_of_lt_of_le hheavy (support_mul_xMon_degree S _ s hsS)

end AC02Frege.MajorityFoundation
end

section
-- Inlined Solutions.BooleanBasis

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation

namespace AC02Frege.BooleanBasis

theorem squarefree_eq_indicator {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s = Finsupp.indicator s.support (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i ∈ s.support
  · simp only [Finsupp.indicator_apply, dif_pos hi]
    have hpos := Finsupp.mem_support_iff.mp hi
    exact Nat.le_antisymm (hs i) (by omega)
  · simpa only [Finsupp.indicator_apply, dif_neg hi] using (by simpa only [Finsupp.mem_support_iff, not_not] using hi : s i = 0)

theorem squarefree_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2)
    (hs : ∀ i, s i ≤ 1) : monomial s c = c • xMon s.support := by
  rw [xMon_eq_monomial, smul_monomial, smul_eq_mul, mul_one,
    ← squarefree_eq_indicator s hs]

theorem squarefree_sum {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s.sum (fun _ e => e) = s.support.card := by
  have heq := squarefree_monomial s (1 : ZMod 2) hs
  have hd := congrArg MvPolynomial.totalDegree heq
  simpa only [totalDegree_monomial _ one_ne_zero, one_smul, xMon_totalDegree] using hd

noncomputable def monomialSpan {V : Type*} (P : Finset V → Prop) :
    Submodule (ZMod 2) (MvPolynomial V (ZMod 2)) :=
  Submodule.span (ZMod 2) {p | ∃ S : Finset V, P S ∧ p = xMon S}

theorem mem_monomialSpan_iff {V : Type*} (P : Finset V → Prop)
    (p : MvPolynomial V (ZMod 2)) : p ∈ monomialSpan P ↔
      IsMultilinear p ∧ ∀ s ∈ p.support, P s.support := by
  classical
  let M := restrictSupport (ZMod 2) {s : V →₀ ℕ | (∀ i, s i ≤ 1) ∧ P s.support}
  have heq : monomialSpan P = M := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro q ⟨S, hS, rfl⟩
      rw [xMon_eq_monomial]
      apply (monomial_mem_restrictSupport (ZMod 2)).mpr
      left
      refine ⟨?_, ?_⟩
      · intro i
        simp only [Finsupp.indicator_apply]
        split_ifs <;> omega
      · simpa only [indicator_support] using hS
    · intro q hq
      have hq' : ∀ s ∈ q.support, (∀ i, s i ≤ 1) ∧ P s.support := hq
      rw [q.as_sum]
      apply Submodule.sum_mem
      intro s hs
      obtain ⟨hml, hP⟩ := hq' s hs
      rw [squarefree_monomial s _ hml]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s.support, hP, rfl⟩)
  rw [heq, mem_restrictSupport_iff (ZMod 2)]
  constructor
  · intro hp
    exact ⟨fun s hs i => (hp hs).1 i, fun s hs => (hp hs).2⟩
  · rintro ⟨hml, hP⟩ s hs
    exact ⟨hml s hs, hP s hs⟩

theorem mem_light_iff {V : Type*} (m : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ monomialSpan (fun S : Finset V => S.card ≤ m) ↔
      IsMultilinear p ∧ p.totalDegree ≤ m := by
  rw [mem_monomialSpan_iff]
  constructor
  · rintro ⟨hp, hP⟩
    refine ⟨hp, Finset.sup_le fun s hs => ?_⟩
    rw [squarefree_sum s (hp s hs)]
    exact hP s hs
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun s hs => ?_⟩
    rw [← squarefree_sum s (hp s hs)]
    exact (le_totalDegree hs).trans hd

theorem point_interpolation {V : Type} [Fintype V] [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) :
    p = ∑ S : Finset V, eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p • pointPoly S := by
  apply multilinear_ext hp
    (multilinear_sum _ _ (fun S _ =>
      (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).smul_mem _
        ((mem_restrictDegree V _ 1).mpr (pointPoly_multilinear S)))))
  intro x
  simp only [map_sum, smul_eval, pointPoly_eval]
  have heq (S : Finset V) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro h; rw [h, ones_of_point]
    · intro h; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp
  have hx : (fun i => if x i = 1 then (1 : ZMod 2) else 0) = x := by
    funext i
    rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]
  rw [hx]

end AC02Frege.BooleanBasis
end

section
-- Inlined Solutions.BooleanFlip

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation AC02Frege.BooleanBasis

namespace AC02Frege.BooleanFlip

theorem ml_totalDegree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (ML p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_monomial_le _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  simp only [Finsupp.sum, sqfree_support]
  apply Finset.sum_le_sum
  intro i _
  simp only [sqfree, Finsupp.mapRange_apply]
  exact min_le_left _ _

theorem bind_linear_totalDegree_le {V W : Type*} (f : V → MvPolynomial W (ZMod 2))
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial V (ZMod 2)) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, bind₁_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

noncomputable def flip {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    MvPolynomial V (ZMod 2) := ML (bind₁ (fun i => 1 + X i) p)

theorem flip_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (flip p) := ml_multilinear _

theorem flip_degree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (flip p).totalDegree ≤ p.totalDegree := by
  apply (ml_totalDegree_le _).trans
  apply bind_linear_totalDegree_le
  intro i
  exact (totalDegree_add _ _).trans (by simp)

theorem flip_eval {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (flip p) = eval (fun i => 1 + x i) p := by
  rw [flip, eval_ml]
  simp only [eval, eval₂Hom_bind₁, map_add, map_one, eval₂Hom_X']

theorem flip_involution {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : flip (flip p) = p := by
  apply multilinear_ext (flip_multilinear _) hp
  intro x
  simp only [flip_eval, CharTwo.add_cancel_left]

end AC02Frege.BooleanFlip
end

section
-- Inlined Solutions.BooleanRestrictions

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip

namespace AC02Frege.BooleanRestrictions

theorem xMon_eval_point {V : Type*} [DecidableEq V] (S T : Finset V) :
    eval (fun i => if i ∈ T then (1 : ZMod 2) else 0) (xMon S) =
      if S ⊆ T then 1 else 0 := by
  classical
  rw [xMon_eval]
  by_cases h : S ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by simp [hit])

theorem multilinear_exponent_ext {V : Type*} (s t : V →₀ ℕ)
    (hs : ∀ i, s i ≤ 1) (ht : ∀ i, t i ≤ 1) (hst : s.support = t.support) : s = t := by
  rw [squarefree_eq_indicator s hs, squarefree_eq_indicator t ht, hst]

theorem eq_zero_of_support_point_eval_zero {V : Type} [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (hv : ∀ s ∈ p.support,
      eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  classical
  by_contra hne
  obtain ⟨s, hs, hmin⟩ := p.support.exists_min_image
    (fun t => t.support.card) (support_nonempty.mpr hne)
  have heval : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = p.coeff s := by
    have hsum : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p =
        ∑ t ∈ p.support, p.coeff t * (if t.support ⊆ s.support then (1 : ZMod 2) else 0) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [squarefree_monomial t _ (hp t ht), smul_eval, xMon_eval_point]
    rw [hsum, Finset.sum_eq_single s]
    · simp
    · intro t ht hts
      have hnot : ¬ t.support ⊆ s.support := by
        intro hsub
        have heq : t.support = s.support := Finset.eq_of_subset_of_card_le hsub (hmin t ht)
        exact hts (multilinear_exponent_ext t s (hp t ht) (hp s hs) heq)
      rw [if_neg hnot, mul_zero]
    · intro hnot
      exact False.elim (hnot hs)
  have hz := hv s hs
  rw [heval] at hz
  exact (mem_support_iff.mp hs) hz

theorem eval_injective_on_monomialSpan {V : Type} [DecidableEq V]
    (P : Finset V → Prop) (p : MvPolynomial V (ZMod 2))
    (hp : p ∈ monomialSpan P)
    (hv : ∀ S : Finset V, P S →
      eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  obtain ⟨hml, hP⟩ := (mem_monomialSpan_iff P p).mp hp
  exact eq_zero_of_support_point_eval_zero p hml (fun s hs => hv s.support (hP s hs))

theorem ml_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (ML p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨s, hs, his⟩ := (mem_vars_iff_mem_support i).mp hi
  have hexp : ML p = ∑ t ∈ p.support, monomial (sqfree t) (p.coeff t) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, ml_monomial]
  rw [hexp] at hs
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have heq := Finset.mem_singleton.mp (support_monomial_subset hst)
  subst s
  rw [sqfree_support] at his
  exact (mem_vars_iff_mem_support i).mpr ⟨t, ht, his⟩

theorem flip_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (BooleanFlip.flip p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp
    (vars_bind₁ (fun j => 1 + X j) p (ml_vars_subset _ hi))
  have hsub : (1 + X j : MvPolynomial V (ZMod 2)).vars ⊆ {j} := by
    simpa using vars_add_subset (1 : MvPolynomial V (ZMod 2)) (X j)
  have heq := Finset.mem_singleton.mp (hsub hij)
  simpa only [heq] using hj

noncomputable def complementMap {V : Type} :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) where
  toFun := BooleanFlip.flip
  map_add' p q := by simp only [BooleanFlip.flip, map_add]
  map_smul' c p := by simp only [BooleanFlip.flip, map_smul, RingHom.id_apply]

theorem flip_mem_monomialSpan {V : Type} (P : Finset V → Prop)
    (hP : ∀ S T, T ⊆ S → P S → P T)
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ monomialSpan P) :
    BooleanFlip.flip p ∈ monomialSpan P := by
  classical
  have hle : monomialSpan P ≤ (monomialSpan P).comap complementMap := by
    apply Submodule.span_le.mpr
    rintro q ⟨S, hS, rfl⟩
    apply (mem_monomialSpan_iff P _).mpr
    refine ⟨flip_multilinear _, ?_⟩
    intro s hs
    have hsub : s.support ⊆ S := by
      apply (support_subset_vars_of_mem_support hs).trans
      apply (flip_vars_subset _).trans
      rw [xMon_eq_monomial, vars_monomial one_ne_zero, indicator_support]
    exact hP S s.support hsub hS
  exact hle hp

theorem monomialSpan_span_range {V : Type} (P : Finset V → Prop) :
    monomialSpan P = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset V // P S} => xMon S.1)) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨⟨S, hS⟩, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S.1, S.2, rfl⟩

end AC02Frege.BooleanRestrictions
end

section
-- Inlined Solutions.BooleanCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis AC02Frege.BooleanRestrictions

namespace ProofComplexity.BooleanCoordinates

theorem all_monomials_span (V : Type) :
    Submodule.span (ZMod 2) (Set.range (fun S : Finset V => xMon S)) =
      restrictDegree V (ZMod 2) 1 := by
  have heq : monomialSpan (fun _S : Finset V => True) = restrictDegree V (ZMod 2) 1 := by
    ext p
    simp only [mem_monomialSpan_iff, mem_restrictDegree]
    simp only [and_true, implies_true]
    rfl
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨S, rfl⟩
    exact (mem_restrictDegree V _ 1).mpr (xMon_multilinear S)
  · rw [← heq]
    apply Submodule.span_le.mpr
    rintro p ⟨S, _, rfl⟩
    exact Submodule.subset_span ⟨S, rfl⟩

noncomputable def booleanBasis (V : Type) :
    Basis (Finset V) (ZMod 2) (restrictDegree V (ZMod 2) 1) :=
  (Basis.span xMon_linearIndependent).map (LinearEquiv.ofEq _ _ (all_monomials_span V))

@[simp] theorem booleanBasis_coe (V : Type) (S : Finset V) :
    ((booleanBasis V S : restrictDegree V (ZMod 2) 1) : MvPolynomial V (ZMod 2)) = xMon S := by
  simp only [booleanBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  exact Basis.coe_span_apply _ _

noncomputable def monoPoly {V : Type} [Fintype V] (c : Finset V → ZMod 2) :
    MvPolynomial V (ZMod 2) :=
  ((booleanBasis V).equivFun.symm c).1

noncomputable def monoCoeffs {V : Type} [Fintype V] (p : MvPolynomial V (ZMod 2)) :
    Finset V → ZMod 2 :=
  (booleanBasis V).equivFun ⟨ML p, (mem_restrictDegree V _ 1).mpr (ml_multilinear p)⟩

theorem monoPoly_multilinear {V : Type} [Fintype V] (c : Finset V → ZMod 2) :
    IsMultilinear (monoPoly c) :=
  (mem_restrictDegree V _ 1).mp ((booleanBasis V).equivFun.symm c).2

theorem monoPoly_coeffs {V : Type} [Fintype V] (p : MvPolynomial V (ZMod 2)) :
    monoPoly (monoCoeffs p) = ML p := by
  exact congrArg Subtype.val ((booleanBasis V).equivFun.symm_apply_apply _)

theorem monoCoeffs_poly {V : Type} [Fintype V] (c : Finset V → ZMod 2) :
    monoCoeffs (monoPoly c) = c := by
  have hsub : (⟨ML (monoPoly c), (mem_restrictDegree V _ 1).mpr
      (ml_multilinear (monoPoly c))⟩ : restrictDegree V (ZMod 2) 1) =
      (booleanBasis V).equivFun.symm c := by
    apply Subtype.ext
    exact ml_of_multilinear _ (monoPoly_multilinear c)
  exact (congrArg (booleanBasis V).equivFun hsub).trans
    ((booleanBasis V).equivFun.apply_symm_apply c)

theorem monoPoly_sum {V : Type} [Fintype V] (c : Finset V → ZMod 2) :
    monoPoly c = ∑ S : Finset V, c S • xMon S := by
  classical
  have h := (booleanBasis V).equivFun_symm_apply c
  have hv := congrArg (fun p : restrictDegree V (ZMod 2) 1 => (p : MvPolynomial V (ZMod 2))) h
  simpa only [monoPoly, Submodule.coe_sum, Submodule.coe_smul, booleanBasis_coe] using hv

theorem monoCoeffs_sum {V : Type} [Fintype V] (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : p = ∑ S : Finset V, monoCoeffs p S • xMon S := by
  rw [← monoPoly_sum, monoPoly_coeffs, ml_of_multilinear p hp]

end ProofComplexity.BooleanCoordinates
end

section
-- Inlined Solutions.PCOperations

open MvPolynomial

namespace AC02Frege.Support

theorem derivation_append {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K))
    {π ρ : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π)
    (hρ : PCNonBool.IsDerivation red P ρ) :
    PCNonBool.IsDerivation red P (π ++ ρ) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left
      simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    have hk' : k < ρ.length := by simp only [List.length_append] at hk; omega
    have hget (t : ℕ) (ht : t < ρ.length) :
        (π ++ ρ)[π.length + t]'(by simp only [List.length_append]; omega) = ρ[t] := by
      rw [List.getElem_append_right (Nat.le_add_right π.length t)]
      simp only [Nat.add_sub_cancel_left]
    rcases hρ k hk' with ha | hc | hm
    · left
      obtain ⟨a, ha, c, hac⟩ := ha
      exact ⟨a, ha, c, (hget k hk').trans hac⟩
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨π.length + i, π.length + j, by omega, by omega, a, b, ?_⟩
      rw [hget k hk', hget i (hi.trans hk'), hget j (hj.trans hk')]
      exact hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨π.length + i, by omega, v, ?_⟩
      rw [hget k hk', hget i (hi.trans hk')]
      exact hiv

theorem derivation_snoc {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K)) {π : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π) (p : MvPolynomial σ K)
    (hp :
      (∃ a ∈ P, ∃ c : K, p = c • red a) ∨
      (∃ (i j : ℕ) (hi : i < π.length) (hj : j < π.length) (a b : K),
        p = a • π[i] + b • π[j]) ∨
      (∃ (i : ℕ) (hi : i < π.length) (v : σ), p = red (X v * π[i]))) :
    PCNonBool.IsDerivation red P (π ++ [p]) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left; simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · have heq : k = π.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    have hlast : (π ++ [p])[π.length] = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    rcases hp with ha | hc | hm
    · left; simpa only [hlast] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [hlast, List.getElem_append_left hi, List.getElem_append_left hj] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [hlast, List.getElem_append_left hi] using hiv

theorem pc_zero {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    PCDerivable F D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {F : LiftSAParity.CNF (Fin n)} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) (c : ZMod 2) :
    PCDerivable F D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero F D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : PCDerivable F D p) (hq : PCDerivable F D q) :
    PCDerivable F D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show PCDerivable F D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (p * X v) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [zero_mul]; exact pc_zero F D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [p * X v], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by simp only [hpi, LinearMap.id_apply, mul_comm]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = p * X v := List.mem_singleton.mp hq
      subst q
      exact (totalDegree_mul p (X v)).trans (by simpa only [totalDegree_X] using hdeg)

theorem pc_axiom {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ pcAxioms F)
    (hdeg : p.totalDegree ≤ D) : PCDerivable F D p := by
  refine Or.inr ⟨[p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

end AC02Frege.Support
end

section
-- Inlined Solutions.BooleanPC

open MvPolynomial AC02Frege
open AC02Frege.Support AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.BooleanPC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q.totalDegree ≤ D) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Derivable P D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) (c : ZMod 2) :
    Derivable P D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero P D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : Derivable P D p) (hq : Derivable P D q) :
    Derivable P D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show Derivable P D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    Derivable P D (ML (X v * p)) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [mul_zero, map_zero]; exact pc_zero P D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = ML (X v * p) := List.mem_singleton.mp hq
      subst q
      exact (ml_totalDegree_le _).trans ((totalDegree_mul (X v) p).trans (by simpa only [totalDegree_X, Nat.add_comm] using hdeg))

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P)
    (hdeg : (ML p).totalDegree ≤ D) : Derivable P D (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

theorem pc_mono {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D E : ℕ}
    (hDE : D ≤ E) {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) :
    Derivable P E p := by
  rcases hp with h | ⟨π, hπ, hdeg, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨π, hπ, fun q hq => (hdeg q hq).trans hDE, hp⟩

noncomputable def consequenceSpace {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := {p | Derivable P D p}
  zero_mem' := pc_zero P D
  add_mem' := pc_add P D
  smul_mem' := fun a _ hp => pc_smul P D hp a

end SemAC02.BooleanPC
end

section
-- Inlined Solutions.RelativePC

open MvPolynomial AC02Frege SemAC02
open AC02Frege.Support AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.RelativePC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
    Derivable P U (c • p) := by
  rcases hp with rfl | ⟨π,hπ,hmem,hp⟩
  · simp only [smul_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; left
    exact ⟨i,i,hi,hi,c,0,by simp only [hpi,zero_smul,add_zero]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmem q hq
    · have he : q = c • p := List.mem_singleton.mp hq
      rw [he]
      exact U.smul_mem c (hmem p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p q : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
    Derivable P U (p+q) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ,hρ,hρmem,hq⟩
  · simpa only [add_zero] using (show Derivable P U p from Or.inr ⟨π,hπ,hπmem,hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j,hj,hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p+q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i,j,hi,hj,1,1,by simp only [hpi,hqj,one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπmem r hr
      · exact hρmem r hr
    · have he : r = p+q := List.mem_singleton.mp hr
      rw [he]
      exact U.add_mem (hπmem p hp) (hρmem q hq)

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (v : Fin n)
    (hmem : ML (X v * p) ∈ U) : Derivable P U (ML (X v * p)) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simp only [mul_zero,map_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i,hi,v,by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπmem q hq
    · rwa [List.mem_singleton.mp hq]

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.RelativePC
end

section
-- Inlined Solutions.RelativePCPolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.RelativePC

theorem pc_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : Derivable P U u) (huml : IsMultilinear u)
    (hmem : ∀ w : MvPolynomial (Fin n) (ZMod 2), w.totalDegree ≤ v.totalDegree → ML (u*w) ∈ U) :
    Derivable P U (ML (u*v)) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    have he : u * C c = c • u := by rw [smul_eq_C_mul, mul_comm]
    rw [he, map_smul, ml_of_multilinear u huml]
    exact pc_smul P U hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add, map_add]
    exact pc_add P U (ihm (fun w hw => hmem w (hw.trans hdm)))
      (ihp (fun w hw => hmem w (hw.trans hdp)))
  | mul_X p i ih =>
    have hle : p.totalDegree ≤ (p * X i).totalDegree := by
      by_cases hp : p = 0
      · simp [hp]
      · rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
    have hi := ih (fun w hw => hmem w (hw.trans hle))
    have he : ML (u * (p * X i)) = ML (X i * ML (u*p)) := by
      rw [ml_mul_right]
      congr 1
      ring
    rw [he]
    apply pc_mul_X P U hi i
    rw [← he]
    exact hmem _ le_rfl

end SemAC02.RelativePC
end

section
-- Inlined Solutions.BooleanLocality

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis

namespace SemAC02.BooleanLocality

theorem multilinear_degree_le_card {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) : p.totalDegree ≤ Fintype.card V := by
  classical
  apply Finset.sup_le
  intro s hs
  rw [squarefree_sum s (hp s hs)]
  exact Finset.card_le_univ _

noncomputable def extendAssignment {V : Type} (J : Finset V) (x : J → ZMod 2) : V → Bool := by
  classical
  exact fun i => if hi : i ∈ J then decide (x ⟨i, hi⟩ = 1) else false

theorem represents_local_function {V : Type} [Fintype V] (J : Finset V)
    (f : (V → Bool) → ZMod 2)
    (hf : ∀ z z' : V → Bool, (∀ i ∈ J, z i = z' i) → f z = f z') :
    ∃ r : MvPolynomial V (ZMod 2), r.totalDegree ≤ J.card ∧
      ∀ z : V → Bool, eval (toF2 z) r = f z := by
  classical
  let η : (J → ZMod 2) → ZMod 2 := fun x => f (extendAssignment J x)
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ J (ZMod 2)) η
  let p' : restrictDegree J (ZMod 2) (Fintype.card (ZMod 2) - 1) := p
  have hml : IsMultilinear p'.1 := by
    apply (mem_restrictDegree J _ 1).mp
    simpa only [ZMod.card, Nat.reduceSub] using p'.2
  refine ⟨rename Subtype.val p'.1, ?_, ?_⟩
  · apply (totalDegree_rename_le _ _).trans
    simpa only [Fintype.card_coe] using multilinear_degree_le_card p'.1 hml
  · intro z
    rw [eval_rename]
    have he := congrFun hp (fun j : J => toF2 z j.1)
    change eval (fun j : J => toF2 z j.1) p'.1 = f (extendAssignment J (fun j : J => toF2 z j.1)) at he
    change eval (fun j : J => toF2 z j.1) p'.1 = f z
    rw [he]
    apply hf
    intro i hi
    simp only [extendAssignment, dif_pos hi]
    cases h : z i <;> simp [toF2, h]

end SemAC02.BooleanLocality
end

section
-- Inlined Solutions.CommonBasis

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip AC02Frege.BooleanRestrictions

namespace SemAC02.CommonBasis

def ones {m : ℕ} (X : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => X i = true)

theorem indicator_ones {m : ℕ} (X : Fin m → Bool) : indicatorVec (ones X) = X := by
  funext i
  cases h : X i <;> simp [indicatorVec, ones, h]

theorem ones_indicator {m : ℕ} (S : Finset (Fin m)) : ones (indicatorVec S) = S := by
  ext i
  simp [indicatorVec, ones]

theorem toF2_indicator {m : ℕ} (S : Finset (Fin m)) :
    toF2 (indicatorVec S) = fun i => if i ∈ S then (1 : ZMod 2) else 0 := by
  funext i
  simp [toF2, indicatorVec]

theorem flip_eval_bool {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2)) (X : Fin m → Bool) :
    eval (toF2 X) (BooleanFlip.flip p) = eval (toF2 (fun i => !X i)) p := by
  rw [flip_eval]
  have heq : (fun i => 1 + toF2 X i) = toF2 (fun i => !X i) := by
    funext i
    cases h : X i <;> simp [toF2, h, CharTwo.add_self_eq_zero]
  rw [heq]

noncomputable def supportEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {S : Finset (Fin m) // g (indicatorVec S) = true} ≃
      {X : Fin m → Bool // g X = true} where
  toFun S := ⟨indicatorVec S.1, S.2⟩
  invFun X := ⟨ones X.1, by simpa only [indicator_ones] using X.2⟩
  left_inv S := Subtype.ext (ones_indicator S.1)
  right_inv X := Subtype.ext (indicator_ones X.1)

def complementEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {X : Fin m → Bool // g X = true} ≃
      {X : Fin m → Bool // g (fun i => !X i) = true} where
  toFun X := ⟨fun i => !X.1 i, by simpa only [Bool.not_not] using X.2⟩
  invFun X := ⟨fun i => !X.1 i, X.2⟩
  left_inv X := Subtype.ext (by funext i; simp)
  right_inv X := Subtype.ext (by funext i; simp)

noncomputable def restriction {m : ℕ} (Ω : Set (Fin m → Bool)) :
    MvPolynomial (Fin m) (ZMod 2) →ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun p X := eval (toF2 X.1) p
  map_add' p q := by ext X; simp
  map_smul' c p := by ext X; simp

theorem downclosed {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) :
    ∀ S T : Finset (Fin m), T ⊆ S → g (indicatorVec S) = true →
      g (indicatorVec T) = true := by
  intro S T hTS hS
  have hle : indicatorVec T ≤ indicatorVec S := by
    intro i
    by_cases hi : i ∈ T
    · simp [indicatorVec, hi, hTS hi]
    · simp [indicatorVec, hi]
  have h := hg hle
  rw [hS] at h
  exact Bool.eq_true_of_true_le h

theorem restriction_zero (m : ℕ) (g : (Fin m → Bool) → Bool)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g X = true} p = 0) : p = 0 := by
  apply eval_injective_on_monomialSpan _ p hp
  intro S hS
  have h := congrFun hv ⟨indicatorVec S, hS⟩
  change eval (toF2 (indicatorVec S)) p = 0 at h
  simpa only [toF2_indicator] using h

theorem restriction_complement_zero (m : ℕ) (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g (fun i => !X i) = true} p = 0) : p = 0 := by
  have hf : BooleanFlip.flip p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true) :=
    flip_mem_monomialSpan _ (downclosed g hg) p hp
  have hvan : restriction {X : Fin m → Bool | g X = true} (BooleanFlip.flip p) = 0 := by
    funext X
    change eval (toF2 X.1) (BooleanFlip.flip p) = 0
    rw [flip_eval_bool]
    have h := congrFun hv ⟨fun i => !X.1 i, by simpa only [Set.mem_ofPred_eq, Bool.not_not] using X.2⟩
    exact h
  have hz := restriction_zero m g _ hf hvan
  have hml := ((mem_monomialSpan_iff _ _).mp hp).1
  calc
    p = BooleanFlip.flip (BooleanFlip.flip p) := (flip_involution p hml).symm
    _ = BooleanFlip.flip 0 := congrArg (BooleanFlip.flip (V := Fin m)) hz
    _ = 0 := by simp [BooleanFlip.flip]

theorem restriction_independent (m : ℕ) (P : Finset (Fin m) → Prop) (Ω : Set (Fin m → Bool))
    (hinj : ∀ p : MvPolynomial (Fin m) (ZMod 2), p ∈ monomialSpan P → restriction Ω p = 0 → p = 0) :
    LinearIndependent (ZMod 2) (fun S : {S : Finset (Fin m) // P S} => restriction Ω (xMon S.1)) := by
  apply (xMon_linearIndependent.comp Subtype.val Subtype.val_injective).map_injOn
  intro v hv w hw heq
  have hv' : v ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  have hw' : w ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  apply sub_eq_zero.mp
  apply hinj (v - w) (Submodule.sub_mem _ hv' hw')
  rw [map_sub, heq, sub_self]

end SemAC02.CommonBasis
end

section
-- Inlined Theorems.Thm_SemAC02_lemma_8_5_common_basis


open MvPolynomial AC02Frege SemAC02 SemAC02.CommonBasis


/-- **Lemma 8.5 (Common monomial basis)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.5, p.64): with
`L = {S ⊆ [m] : g₀(1_S) = 1}`, `Ω₀ = {X : g₀(X) = 1}` and `Ω₁ = {X : g₁(X) = 1}`,
`g₁(X) = g₀(X̄)`, the monomials `x_S = ∏_{j∈S} x_j`, `S ∈ L`, give a basis of both `𝔽₂^{Ω₀}`
and `𝔽₂^{Ω₁}`.

**Formalization Note** Stated for every antitone Boolean function `g₀` on `{0,1}^m` (the
paper's `g₀ = g` from §8.1 is one). "Basis" is linear independence of the restrictions of the
`x_S` to `Ω_b` together with spanning all functions `Ω_b → 𝔽₂`. -/
theorem SemAC02.lemma_8_5_common_basis {m : ℕ} (g₀ : (Fin m → Bool) → Bool) (hg₀ : Antitone g₀) :
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) ∧
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) := by
  classical
  let P : Finset (Fin m) → Prop := fun S => g₀ (indicatorVec S) = true
  let Ω₀ : Set (Fin m → Bool) := {X | g₀ X = true}
  let Ω₁ : Set (Fin m → Bool) := {X | g₀ (fun i => !X i) = true}
  have hli0 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₀ (xMon S.1)) :=
    restriction_independent m P Ω₀ (restriction_zero m g₀)
  have hli1 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₁ (xMon S.1)) :=
    restriction_independent m P Ω₁ (restriction_complement_zero m g₀ hg₀)
  have hspan0 := hli0.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr (supportEquiv m g₀))
  have hspan1 := hli1.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr ((supportEquiv m g₀).trans (complementEquiv m g₀)))
  exact ⟨⟨hli0, hspan0⟩, ⟨hli1, hspan1⟩⟩

end

section
-- Inlined Solutions.ProductFunctionBasis

open Module
open scoped TensorProduct

namespace ProofComplexity

open PiTensorProduct

noncomputable def functionTensorEquiv
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] :
    (⨂[R] i, (X i → R)) ≃ₗ[R] (((i : ι) → X i) → R) := by
  classical
  exact (PiTensorProduct.congr (fun i => (Finsupp.linearEquivFunOnFinite R R (X i)).symm)) ≪≫ₗ
    (PiTensorProduct.ofFinsuppEquiv' (R := R) (κ := X)) ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R R ((i : ι) → X i)

@[simp] theorem functionTensorEquiv_tprod
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] (f : (i : ι) → X i → R) (x : (i : ι) → X i) :
    functionTensorEquiv X (⨂ₜ[R] i, f i) x = ∏ i, f i (x i) := by
  classical
  simp [functionTensorEquiv]

noncomputable def productFunctionBasis
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) :
    Basis ((i : ι) → κ i) R (((i : ι) → X i) → R) :=
  (Basis.piTensorProduct b).map (functionTensorEquiv X)

@[simp] theorem productFunctionBasis_apply
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (k : (i : ι) → κ i) (x : (i : ι) → X i) :
    productFunctionBasis b k x = ∏ i, b i (k i) (x i) := by
  classical
  simp [productFunctionBasis]

theorem productFunctionBasis_repr
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (f : (i : ι) → X i → R)
    (k : (i : ι) → κ i) :
    (productFunctionBasis b).repr (fun x => ∏ i, f i (x i)) k =
      ∏ i, (b i).repr (f i) (k i) := by
  classical
  have hfun : (fun x => ∏ i, f i (x i)) = functionTensorEquiv X (⨂ₜ[R] i, f i) := by
    funext x
    exact (functionTensorEquiv_tprod X f x).symm
  rw [hfun]
  change (Basis.piTensorProduct b).repr
    ((functionTensorEquiv X).symm (functionTensorEquiv X (⨂ₜ[R] i, f i))) k = _
  rw [LinearEquiv.symm_apply_apply]
  exact Basis.piTensorProduct_repr_tprod_apply b f k

end ProofComplexity
end

section
-- Inlined Solutions.SemanticFibreBasis

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace SemAC02.FibreBasis

abbrev BlockIndex {m : ℕ} (g : (Fin m → Bool) → Bool) :=
  {S : Finset (Fin m) // g (indicatorVec S) = true}

abbrev BlockFibre {m : ℕ} (g : (Fin m → Bool) → Bool) (b : Bool) :=
  {X : Fin m → Bool // if b then g (fun j => !X j) = true else g X = true}

noncomputable def blockBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) (b : Bool) :
    Basis (BlockIndex g) (ZMod 2) (BlockFibre g b → ZMod 2) := by
  have h := lemma_8_5_common_basis g hg
  cases b with
  | false => exact Basis.mk h.1.1 h.1.2.ge
  | true => exact Basis.mk h.2.1 h.2.2.ge

@[simp] theorem blockBasis_apply {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (b : Bool) (S : BlockIndex g) (X : BlockFibre g b) :
    blockBasis g hg b S X = eval (toF2 X.1) (xMon S.1) := by
  cases b <;> simp [blockBasis, Basis.mk_apply]

abbrev GlobalIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n : ℕ) :=
  {A : Finset (Fin n × Fin m) // IsLnSupport g A}

def assemble {n m : ℕ} {g : (Fin m → Bool) → Bool} (S : Fin n → BlockIndex g) :
    Finset (Fin n × Fin m) := Finset.univ.filter (fun v => v.2 ∈ (S v.1).1)

@[simp] theorem section_assemble {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (S : Fin n → BlockIndex g) (i : Fin n) : blockSection (assemble S) i = (S i).1 := by
  ext j
  simp [blockSection, assemble]

def sections {n m : ℕ} {g : (Fin m → Bool) → Bool} (A : GlobalIndex g n) (i : Fin n) :
    BlockIndex g := ⟨blockSection A.1 i, A.2 i⟩

@[simp] theorem assemble_sections {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (A : GlobalIndex g n) : assemble (sections A) = A.1 := by
  ext v
  simp [assemble, sections, blockSection]

def indexEquiv (n : ℕ) {m : ℕ} (g : (Fin m → Bool) → Bool) :
    (Fin n → BlockIndex g) ≃ GlobalIndex g n where
  toFun S := ⟨assemble S, by
    intro i
    rw [section_assemble]
    exact (S i).2⟩
  invFun A := sections A
  left_inv S := by funext i; apply Subtype.ext; exact section_assemble S i
  right_inv A := Subtype.ext (assemble_sections A)

abbrev Fibre {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :=
  {X : Fin n × Fin m → Bool // InFiber g z X}

def curryEquiv {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :
    Fibre g z ≃ ((i : Fin n) → BlockFibre g (z i)) where
  toFun X i := ⟨fun j => X.1 (i, j), X.2 i⟩
  invFun X := ⟨fun v => (X v.1).1 v.2, fun i => (X i).2⟩
  left_inv X := Subtype.ext (by funext v; rfl)
  right_inv X := by funext i; apply Subtype.ext; rfl

noncomputable def fibreBasis {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) : Basis (GlobalIndex g n) (ZMod 2) (Fibre g z → ZMod 2) :=
  ((ProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).reindex
    (indexEquiv n g)).map (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))

theorem xMon_eval_blocks {n m : ℕ} (A : Finset (Fin n × Fin m))
    (X : Fin n × Fin m → Bool) : eval (toF2 X) (xMon A) =
      ∏ i : Fin n, eval (toF2 (fun j => X (i, j))) (xMon (blockSection A i)) := by
  classical
  simp only [xMon_eval, blockSection, Finset.prod_filter, toF2]
  rw [← Finset.prod_product']
  simp only [Finset.univ_product_univ]
  rw [← Finset.prod_filter]
  simp

@[simp] theorem fibreBasis_apply {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) (A : GlobalIndex g n) (X : Fibre g z) :
    fibreBasis g hg z A X = eval (toF2 X.1) (xMon A.1) := by
  classical
  rw [fibreBasis, Basis.map_apply, Basis.reindex_apply]
  change ProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))
    (sections A) (curryEquiv g z X) = _
  rw [ProofComplexity.productFunctionBasis_apply, xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [blockBasis_apply]
  rfl

end SemAC02.FibreBasis
end

section
-- Inlined Solutions.SemanticFibreCoordinates

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.FibreBasis

namespace SemAC02.FibreCoordinates

noncomputable def coordinates {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) : ZMod 2 :=
  (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) p) S

theorem coordinates_expansion {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) (X : Fibre g z) :
    eval (toF2 X.1) p = ∑ S : GlobalIndex g n, coordinates g hg p S z *
      eval (toF2 X.1) (xMon S.1) := by
  classical
  have h := congrFun ((fibreBasis g hg z).equivFun.symm_apply_apply (fun X => eval (toF2 X.1) p)) X
  rw [Basis.equivFun_symm_apply] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply, coordinates] using h.symm

theorem coordinates_unique {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (c : GlobalIndex g n → (Fin n → Bool) → ZMod 2)
    (hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin m → Bool), InFiber g z X →
      eval (toF2 X) p = ∑ S, c S z * eval (toF2 X) (xMon S.1)) :
    ∀ S z, c S z = coordinates g hg p S z := by
  classical
  intro S z
  have he : (fun X : Fibre g z => eval (toF2 X.1) p) =
      (fibreBasis g hg z).equivFun.symm (fun S => c S z) := by
    rw [Basis.equivFun_symm_apply]
    funext X
    rw [hc z X.1 X.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply]
  have h := congrArg (fibreBasis g hg z).equivFun he
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrFun h S).symm

theorem coordinates_add {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p q : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p + q) S z = coordinates g hg p S z + coordinates g hg q S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p + q)) =
      (fun X => eval (toF2 X.1) p) + (fun X => eval (toF2 X.1) q) := by
    funext X
    exact map_add _ _ _
  unfold coordinates
  rw [he, map_add]
  rfl

theorem coordinates_smul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (a : ZMod 2) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (a • p) S z = a * coordinates g hg p S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (a • p)) =
      a • (fun X => eval (toF2 X.1) p) := by
    funext X
    simp only [smul_eval, Pi.smul_apply, smul_eq_mul]
  unfold coordinates
  rw [he, map_smul]
  rfl

end SemAC02.FibreCoordinates
end

section
-- Inlined Solutions.SemanticProductCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates

namespace SemAC02.ProductCoordinates

noncomputable def blockCoefficient {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (U : Finset (Fin m)) (b : Bool) : ZMod 2 :=
  (blockBasis g hg b).repr (fun X => eval (toF2 X.1) (xMon T.1 * xMon U)) S

theorem blockCoefficient_empty {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (b : Bool) :
    blockCoefficient g hg S T ∅ b = if S = T then 1 else 0 := by
  classical
  have he : (fun X : BlockFibre g b => eval (toF2 X.1) (xMon T.1 * xMon ∅)) =
      blockBasis g hg b T := by
    funext X
    simp only [xMon, Finset.prod_empty, mul_one, blockBasis_apply]
  unfold blockCoefficient
  rw [he, Basis.repr_self]
  by_cases hST : S = T
  · subst S
    rw [Finsupp.single_eq_same, if_pos rfl]
  · rw [Finsupp.single_eq_of_ne hST, if_neg hST]

theorem coordinates_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) (z : Fin n → Bool) :
    coordinates g hg (xMon T.1 * xMon U) S z =
      ∏ i : Fin n, blockCoefficient g hg (sections S i) (sections T i) (blockSection U i) (z i) := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon U)) =
      (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))
        (fun X : (i : Fin n) → BlockFibre g (z i) =>
          ∏ i : Fin n, eval (toF2 (X i).1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) := by
    funext X
    change eval (toF2 X.1) (xMon T.1 * xMon U) =
      ∏ i : Fin n, eval (toF2 (fun j => X.1 (i, j)))
        (xMon (blockSection T.1 i) * xMon (blockSection U i))
    simp only [map_mul, xMon_eval_blocks, Finset.prod_mul_distrib]
  unfold coordinates
  rw [he]
  change (ProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).repr
    ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)).symm
      ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)) _)) ((indexEquiv n g).symm S) = _
  rw [LinearEquiv.symm_apply_apply]
  exact ProofComplexity.productFunctionBasis_repr (fun i : Fin n => blockBasis g hg (z i))
    (fun i X => eval (toF2 X.1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) (sections S)

theorem blockSection_empty {n m : ℕ} (U : Finset (Fin n × Fin m)) (i : Fin n)
    (hi : i ∉ U.image Prod.fst) : blockSection U i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply hi
  have hij : (i, j) ∈ U := (Finset.mem_filter.mp hj).2
  exact Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩

theorem coordinates_product_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m))
    (z z' : Fin n → Bool) (hz : ∀ i ∈ U.image Prod.fst, z i = z' i) :
    coordinates g hg (xMon T.1 * xMon U) S z = coordinates g hg (xMon T.1 * xMon U) S z' := by
  classical
  rw [coordinates_product, coordinates_product]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U.image Prod.fst
  · rw [hz i hi]
  · rw [blockSection_empty U i hi, blockCoefficient_empty, blockCoefficient_empty]

end SemAC02.ProductCoordinates
end

section
-- Inlined Solutions.SemanticCoordinateSpaces

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates

namespace SemAC02.CoordinateSpaces

noncomputable def booleanEvaluation (n : ℕ) :
    MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p z := eval (toF2 z) p
  map_add' p q := by funext z; exact map_add _ _ _
  map_smul' a p := by funext z; simp only [smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

noncomputable def degreeSpace (n D : ℕ) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) :=
  (restrictTotalDegree (Fin n) (ZMod 2) D).map (booleanEvaluation n)

theorem mem_degreeSpace {n D : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    u ∈ degreeSpace n D ↔ ∃ r : MvPolynomial (Fin n) (ZMod 2), r.totalDegree ≤ D ∧
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  constructor
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mp hr, fun z => congrFun heq z⟩
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mpr hr, funext heq⟩

def localSpace {n : ℕ} (J : Finset (Fin n)) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) where
  carrier := {u | ∀ z z', (∀ i ∈ J, z i = z' i) → u z = u z'}
  zero_mem' := by intro z z' hz; rfl
  add_mem' := by intro f h hf hh z z' hz; exact congrArg₂ (· + ·) (hf z z' hz) (hh z z' hz)
  smul_mem' := by intro a f hf z z' hz; exact congrArg (fun x => a • x) (hf z z' hz)

theorem localSpace_mono {n : ℕ} {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    localSpace I ≤ localSpace J := by
  intro f hf z z' hz
  exact hf z z' (fun i hi => hz i (hIJ hi))

noncomputable def coordinateMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p := coordinates g hg p S
  map_add' p q := by funext z; exact coordinates_add g hg p q S z
  map_smul' a p := by
    funext z
    simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using coordinates_smul g hg a p S z

end SemAC02.CoordinateSpaces
end

section
-- Inlined Solutions.BooleanFunctionPolynomials

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

namespace SemAC02.BooleanFunctionPolynomials

theorem toF2_surjective {V : Type} (x : V → ZMod 2) : ∃ X : V → Bool, toF2 X = x := by
  refine ⟨fun v => decide (x v = 1), ?_⟩
  funext v
  have h : x v = 0 ∨ x v = 1 := by
    have h01 := AC02Frege.MajorityFoundation.eq_zero_or_one (x v)
    exact h01
  rcases h with h | h <;> simp [toF2, h]

theorem multilinear_ext_bool {V : Type} [Finite V] {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (he : ∀ X : V → Bool, eval (toF2 X) p = eval (toF2 X) q) : p = q := by
  apply multilinear_ext hp hq
  intro x
  obtain ⟨X, rfl⟩ := toF2_surjective x
  exact he X

theorem exists_polynomial (n : ℕ) (u : (Fin n → Bool) → ZMod 2) :
    ∃ r : MvPolynomial (Fin n) (ZMod 2),
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  classical
  obtain ⟨r, _, hr⟩ := BooleanLocality.represents_local_function Finset.univ u
    (fun z z' h => congrArg u (funext (fun i => h i (Finset.mem_univ i))))
  exact ⟨r, hr⟩

noncomputable def polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    MvPolynomial (Fin n) (ZMod 2) := ML (Classical.choose (exists_polynomial n u))

theorem polynomial_multilinear {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    IsMultilinear (polynomial u) := ml_multilinear _

@[simp] theorem eval_polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) (z : Fin n → Bool) :
    eval (toF2 z) (polynomial u) = u z := by
  rw [polynomial, eval_ml]
  exact Classical.choose_spec (exists_polynomial n u) z

theorem polynomial_eq {n : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (r : MvPolynomial (Fin n) (ZMod 2))
    (hr : ∀ z : Fin n → Bool, eval (toF2 z) r = u z) : polynomial u = ML r := by
  apply multilinear_ext_bool
    (polynomial_multilinear u) (ml_multilinear r)
  intro z
  rw [eval_polynomial, eval_ml, hr]

noncomputable def polynomialMap (n : ℕ) :
    ((Fin n → Bool) → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) where
  toFun := polynomial
  map_add' u v := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.add_mem _ ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u))
          ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear v)))
    · intro z
      simp only [eval_polynomial, map_add, Pi.add_apply]
  map_smul' a u := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.smul_mem _ a ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u)))
    · intro z
      simp only [eval_polynomial, smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem polynomial_degree {n D : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (hu : u ∈ SemAC02.CoordinateSpaces.degreeSpace n D) : (polynomial u).totalDegree ≤ D := by
  obtain ⟨r, hr, he⟩ := SemAC02.CoordinateSpaces.mem_degreeSpace u |>.mp hu
  rw [polynomial_eq u r he]
  exact (ml_totalDegree_le r).trans hr

end SemAC02.BooleanFunctionPolynomials
end

section
-- Inlined Solutions.SemanticMonomialLocality

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates
open SemAC02.ProductCoordinates SemAC02.CoordinateSpaces SemAC02.BooleanLocality

namespace SemAC02.MonomialLocality

theorem eval_monomial_squarefree {V : Type} (s : V →₀ ℕ) (a : ZMod 2) (x : V → ZMod 2) :
    eval x (monomial s a) = a * eval x (xMon s.support) := by
  calc
    eval x (monomial s a) = eval x (ML (monomial s a)) := (eval_ml _ _).symm
    _ = a * eval x (xMon s.support) := by
      rw [ml_monomial, squarefree_monomial (sqfree s) a (fun i => by simp [sqfree, Finsupp.mapRange_apply]),
        sqfree_support, smul_eval]

theorem coordinate_monomial {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) =
      a • coordinateMap g hg S (xMon T.1 * xMon s.support) := by
  funext z
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * monomial s a)) =
      a • (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon s.support)) := by
    funext X
    simp only [map_mul, eval_monomial_squarefree, Pi.smul_apply, smul_eq_mul]
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (xMon T.1 * monomial s a)) S = _
  rw [he, map_smul]
  rfl

theorem support_card_le_sum {V : Type} (s : V →₀ ℕ) : s.support.card ≤ s.sum (fun _ e => e) := by
  classical
  change s.support.card ≤ ∑ i ∈ s.support, s i
  calc
    s.support.card = ∑ _i ∈ s.support, 1 := by simp
    _ ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem degreeSpace_mono {n D E : ℕ} (hDE : D ≤ E) : degreeSpace n D ≤ degreeSpace n E := by
  intro u hu
  obtain ⟨r, hr, he⟩ := (mem_degreeSpace u).mp hu
  exact (mem_degreeSpace u).mpr ⟨r, hr.trans hDE, he⟩

theorem squarefree_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ localSpace (U.image Prod.fst) := by
  exact coordinates_product_local g hg S T U

theorem squarefree_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ degreeSpace n U.card := by
  have hl := squarefree_local g hg S T U
  obtain ⟨r, hr, he⟩ := represents_local_function (U.image Prod.fst)
    (coordinateMap g hg S (xMon T.1 * xMon U)) hl
  exact (mem_degreeSpace _).mpr ⟨r, hr.trans (Finset.card_image_le), he⟩

theorem monomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ localSpace (s.support.image Prod.fst) := by
  rw [coordinate_monomial]
  exact Submodule.smul_mem _ a (squarefree_local g hg S T s.support)

theorem monomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ degreeSpace n (s.sum (fun _ e => e)) := by
  rw [coordinate_monomial]
  apply Submodule.smul_mem
  exact degreeSpace_mono (support_card_le_sum s) (squarefree_degree g hg S T s.support)

end SemAC02.MonomialLocality
end

section
-- Inlined Solutions.SemanticCoefficientControl

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.FibreBasis SemAC02.FibreCoordinates
open SemAC02.CoordinateSpaces SemAC02.MonomialLocality

namespace SemAC02.CoefficientControl

theorem coordinate_polynomial_sum {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (f p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (f * p) = ∑ s ∈ p.support,
      coordinateMap g hg S (f * monomial s (p.coeff s)) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum, map_sum]

theorem basis_polynomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (xMon T.1 * p) ∈ degreeSpace n p.totalDegree := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  exact degreeSpace_mono (le_totalDegree hs) (monomial_degree g hg S T s (p.coeff s))

theorem basis_polynomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) :
    coordinateMap g hg S (xMon T.1 * p) ∈ localSpace J := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  have hsub : s.support.image Prod.fst ⊆ J := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact hp v ((support_subset_vars_of_mem_support hs) hv)
  exact localSpace_mono hsub (monomial_local g hg S T s (p.coeff s))

theorem coefficient_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ degreeSpace n p.totalDegree := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (degreeSpace n p.totalDegree).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_degree g hg S ⟨T, hT⟩ p
  exact hle hf

theorem coefficient_locality {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ localSpace J := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (localSpace J).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_local g hg S ⟨T, hT⟩ p J hp
  exact hle hf

end SemAC02.CoefficientControl
end

section
-- Inlined Solutions.SemanticCoefficientPolynomials

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip
open SemAC02.FibreBasis SemAC02.FibreCoordinates SemAC02.CoordinateSpaces
open SemAC02.BooleanFunctionPolynomials SemAC02.CoefficientControl

namespace SemAC02.CoefficientPolynomials

noncomputable def coefficientMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  (polynomialMap n).comp (coordinateMap g hg S)

theorem coefficient_multilinear {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    IsMultilinear (coefficientMap g hg S p) := polynomial_multilinear _

@[simp] theorem eval_coefficient {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) :
    eval (toF2 z) (coefficientMap g hg S p) = coordinates g hg p S z := eval_polynomial _ _

theorem coefficient_congr {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p q : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (he : ∀ X : Fin n × Fin m → Bool, eval (toF2 X) p = eval (toF2 X) q) :
    coefficientMap g hg S p = coefficientMap g hg S q := by
  apply multilinear_ext_bool (coefficient_multilinear g hg S p) (coefficient_multilinear g hg S q)
  intro z
  simp only [eval_coefficient, coordinates]
  exact congrArg (fun u => (fibreBasis g hg z).equivFun u S)
    (funext (fun X : Fibre g z => he X.1))

@[simp] theorem coefficient_ml {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coefficientMap g hg S (ML p) = coefficientMap g hg S p :=
  coefficient_congr g hg S _ _ (fun _ => eval_ml _ _)

theorem coefficient_degree_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    (coefficientMap g hg S (f * p)).totalDegree ≤ p.totalDegree :=
  polynomial_degree _ (coefficient_degree g hg f hf p S)

theorem ble_degree {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) (hp : p ∈ Ble V D) :
    p.totalDegree ≤ D := by
  classical
  have hle : Ble V D ≤ restrictTotalDegree V (ZMod 2) D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    exact (mem_restrictTotalDegree V D _).mpr ((xMon_totalDegree A).trans_le hA)
  exact (mem_restrictTotalDegree V D p).mp (hle hp)

theorem coefficient_degree_multSpace {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (D : ℕ) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hp : p ∈ multSpace f D)
    (S : GlobalIndex g n) : (coefficientMap g hg S p).totalDegree ≤ D := by
  obtain ⟨q, hq, rfl⟩ := hp
  change (coefficientMap g hg S (ML (f * q))).totalDegree ≤ D
  rw [coefficient_ml]
  exact (coefficient_degree_product g hg f hf q S).trans (ble_degree D q hq)

theorem coordinates_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p * v) S z = ∑ T : GlobalIndex g n,
      coordinates g hg p T z * coordinates g hg (xMon T.1 * v) S z := by
  classical
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p * v)) =
      ∑ T : GlobalIndex g n, coordinates g hg p T z •
        (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * v)) := by
    funext X
    simp only [map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [coordinates_expansion g hg p z X, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (p * v)) S = _
  rw [he, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinates]

theorem coefficient_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coefficientMap g hg S (p * v) = ∑ T : GlobalIndex g n,
      ML (coefficientMap g hg T p * coefficientMap g hg S (xMon T.1 * v)) := by
  classical
  refine multilinear_ext_bool (coefficient_multilinear g hg S _) ?_ ?_
  · exact (mem_restrictDegree (Fin n) _ 1).mp
      (Submodule.sum_mem _ (fun _ _ => (mem_restrictDegree (Fin n) _ 1).mpr (ml_multilinear _)))
  · intro z
    simp only [eval_coefficient, map_sum, eval_ml, map_mul]
    exact coordinates_mul g hg p v S z

end SemAC02.CoefficientPolynomials
end

section
-- Inlined Solutions.RelativeSpaceAlgebra

open MvPolynomial AC02Frege SemAC02
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip AC02Frege.BooleanBasis

namespace SemAC02.RelativeSpaceAlgebra

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
  rw [he, mem_light_iff]

theorem mem_multSpace_of_degree {V : Type} [Finite V]
    (f Q : MvPolynomial V (ZMod 2)) (D : ℕ) (hQ : Q.totalDegree ≤ D) :
    mulML f Q ∈ multSpace f D := by
  refine ⟨ML Q, (mem_Ble_iff D _).mpr ⟨ml_multilinear _, (ml_totalDegree_le _).trans hQ⟩, ?_⟩
  change ML (f * ML Q) = ML (f * Q)
  exact ml_mul_right f Q

theorem multSpace_multilinear {V : Type} (f p : MvPolynomial V (ZMod 2)) (D : ℕ)
    (hp : p ∈ multSpace f D) : IsMultilinear p := by
  obtain ⟨Q,_,rfl⟩ := hp
  exact ml_multilinear _

theorem multSpace_degree {V : Type} (f p : MvPolynomial V (ZMod 2)) (k D : ℕ)
    (hf : f ∈ Ble V k) (hp : p ∈ multSpace f D) : p.totalDegree ≤ k+D := by
  obtain ⟨Q,hQ,rfl⟩ := hp
  change (ML (f*Q)).totalDegree ≤ k+D
  exact (ml_totalDegree_le _).trans ((totalDegree_mul f Q).trans
    (Nat.add_le_add ((mem_Ble_iff k f).mp hf).2 ((mem_Ble_iff D Q).mp hQ).2))

theorem relative_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (f Q v : MvPolynomial (Fin n) (ZMod 2)) (D : ℕ)
    (hp : RelativePC.Derivable P (multSpace f D) (mulML f Q))
    (hdeg : Q.totalDegree + v.totalDegree ≤ D) :
    RelativePC.Derivable P (multSpace f D) (ML (mulML f Q * v)) := by
  apply RelativePC.pc_polynomial_mul P (multSpace f D) (mulML f Q) v hp (ml_multilinear _)
  intro w hw
  have he : ML (mulML f Q * w) = mulML f (Q*w) := by
    change ML (ML (f*Q) * w) = ML (f*(Q*w))
    rw [ml_mul_left, mul_assoc]
  rw [he]
  apply mem_multSpace_of_degree
  exact (totalDegree_mul Q w).trans (by omega)

end SemAC02.RelativeSpaceAlgebra
end

section
-- Inlined Solutions.BooleanDimension

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra

namespace SemAC02.BooleanDimension

abbrev DegreeIndex (n D : ℕ) := {A : Finset (Fin n) // A.card ≤ D}

theorem span_degree_monomials (n D : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun A : DegreeIndex n D => xMon A.1)) = Ble (Fin n) D := by
  congr 1
  ext p
  constructor
  · rintro ⟨A,rfl⟩
    exact ⟨A.1,A.2,rfl⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨⟨A,hA⟩,rfl⟩

noncomputable def degreeBasis (n D : ℕ) : Basis (DegreeIndex n D) (ZMod 2) (Ble (Fin n) D) :=
  (Basis.span (xMon_linearIndependent.comp (fun A : DegreeIndex n D => A.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree_monomials n D))

instance finite_Ble (n D : ℕ) : Module.Finite (ZMod 2) (Ble (Fin n) D) :=
  Module.Finite.of_basis (degreeBasis n D)

def degreeIndexEquiv (n D : ℕ) : DegreeIndex n D ≃
    (j : Fin (min D n + 1)) × {A : Finset (Fin n) // A.card = j.1} where
  toFun A := ⟨⟨A.1.card, by
    have hcard := Finset.card_le_univ A.1
    simp only [Fintype.card_fin] at hcard
    omega⟩,A.1,rfl⟩
  invFun B := ⟨B.2.1,by have := B.1.2; have := B.2.2; omega⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv B := by
    rcases B with ⟨⟨j,hj⟩,A,hA⟩
    cases hA
    rfl

theorem finrank_Ble (n D : ℕ) : finrank (ZMod 2) (Ble (Fin n) D) = Hn n D := by
  classical
  rw [Module.finrank_eq_card_basis (degreeBasis n D), Fintype.card_congr (degreeIndexEquiv n D), Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range _ _

theorem Hn_pos (n D : ℕ) : 0 < Hn n D := by
  unfold Hn
  apply lt_of_lt_of_le (show 0 < n.choose 0 by simp)
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

end SemAC02.BooleanDimension
end

section
-- Inlined Solutions.MultiplierSupportCount

set_option maxHeartbeats 1000000

open Module MvPolynomial AC02Frege AC02Frege.BooleanAlgebra

namespace SemAC02.MultiplierSupportCount

abbrev MultiplierIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :=
  {S : Finset (Fin n × Fin m) // S.card ≤ k ∧ IsLnSupport g S}

theorem multiplier_span {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun S : MultiplierIndex g n k => xMon S.1)) =
      multiplierSpace g n k := by
  unfold multiplierSpace
  congr 1
  ext p
  constructor
  · rintro ⟨S,rfl⟩
    exact ⟨S.1,S.2,rfl⟩
  · rintro ⟨S,hS,rfl⟩
    exact ⟨⟨S,hS⟩,rfl⟩

noncomputable def multiplierBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Basis (MultiplierIndex g n k) (ZMod 2) (multiplierSpace g n k) :=
  (Basis.span (xMon_linearIndependent.comp (fun S : MultiplierIndex g n k => S.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (multiplier_span g n k))

instance finite_multiplierSpace {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Module.Finite (ZMod 2) (multiplierSpace g n k) := Module.Finite.of_basis (multiplierBasis g n k)

theorem finrank_multiplier {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    finrank (ZMod 2) (multiplierSpace g n k) =
      (Finset.univ.filter (fun S : Finset (Fin n × Fin m) => S.card ≤ k ∧ IsLnSupport g S)).card := by
  rw [Module.finrank_eq_card_basis (multiplierBasis g n k)]
  exact Fintype.card_subtype _

abbrev LowIndex (V : Type) (k : ℕ) := {S : Finset V // S.card ≤ k}

def lowIndexEquiv (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    LowIndex V k ≃ (j : Fin (min k (Fintype.card V)+1)) × {S : Finset V // S.card = j.1} where
  toFun S := ⟨⟨S.1.card,by have := Finset.card_le_univ S.1; omega⟩,S.1,rfl⟩
  invFun T := ⟨T.2.1,by have := T.1.2; have := T.2.2; omega⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv T := by rcases T with ⟨⟨j,hj⟩,S,hS⟩; cases hS; rfl

theorem low_support_card (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).card = Hn (Fintype.card V) k := by
  rw [← Fintype.card_subtype,Fintype.card_congr (lowIndexEquiv V k),Fintype.card_sigma]
  simp only [Fintype.card_finset_len]
  exact Fin.sum_univ_eq_sum_range _ _

end SemAC02.MultiplierSupportCount
end

section
-- Inlined Solutions.BooleanDegreeBasis

open Module MvPolynomial AC02Frege AC02Frege.BooleanAlgebra

namespace SemAC02.BooleanDegreeBasis

abbrev DegreeIndex (V : Type) (K : ℕ) := {T : Finset V // T.card ≤ K}

theorem degree_span (V : Type) (K : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun T : DegreeIndex V K => xMon T.1)) = Ble V K := by
  unfold Ble
  congr 1
  ext p
  constructor
  · rintro ⟨T,rfl⟩; exact ⟨T.1,T.2,rfl⟩
  · rintro ⟨T,hT,rfl⟩; exact ⟨⟨T,hT⟩,rfl⟩

noncomputable def degreeBasis (V : Type) (K : ℕ) : Basis (DegreeIndex V K) (ZMod 2) (Ble V K) :=
  (Basis.span (xMon_linearIndependent.comp (fun T : DegreeIndex V K => T.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (degree_span V K))

instance finite_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) : Module.Finite (ZMod 2) (Ble V K) :=
  Module.Finite.of_basis (degreeBasis V K)

theorem finrank_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) :
    finrank (ZMod 2) (Ble V K) = Hn (Fintype.card V) K := by
  rw [Module.finrank_eq_card_basis (degreeBasis V K)]
  have he : Fintype.card (DegreeIndex V K) =
      (Finset.univ.filter (fun T : Finset V => T.card ≤ K)).card := Fintype.card_subtype _
  rw [he]
  exact MultiplierSupportCount.low_support_card V K

end SemAC02.BooleanDegreeBasis
end

section
-- Inlined Solutions.BooleanDegreeCounts

namespace AC02Frege.BooleanDegreeCounts

open Module

lemma monoCount_eq_Hn (N K : ℕ) : monoCount N K = SemAC02.Hn N K := by
  unfold monoCount SemAC02.Hn
  apply (Finset.sum_subset (show Finset.range (min K N+1) ⊆ Finset.range (K+1) by
    apply Finset.range_mono; omega) ?_).symm
  intro i hi hnot
  have hiK : i ≤ K := by have := Finset.mem_range.mp hi; omega
  have hiN : N < i := by
    simp only [Finset.mem_range] at hnot
    omega
  exact Nat.choose_eq_zero_of_lt hiN

lemma finrank_Ble {V : Type} [Fintype V] [DecidableEq V] (K : ℕ) :
    finrank (ZMod 2) (SemAC02.Ble V K) = monoCount (Fintype.card V) K := by
  rw [SemAC02.BooleanDegreeBasis.finrank_Ble,monoCount_eq_Hn]

lemma monoCount_mono (N : ℕ) {a b : ℕ} (hab : a ≤ b) : monoCount N a ≤ monoCount N b := by
  unfold monoCount
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)

end AC02Frege.BooleanDegreeCounts
end

section
-- Inlined Solutions.BooleanDegreeSpaces

open MvPolynomial AC02Frege AC02Frege.BooleanBasis

namespace SemAC02.BooleanDegreeSpaces

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩; exact ⟨A,hA,rfl⟩
  rw [he,mem_light_iff]

end SemAC02.BooleanDegreeSpaces
end

section
-- Inlined Solutions.LinearMapFactorThrough

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProofComplexity.LinearMapFactorThrough

/-- A map that kills every relation killed by f extends to a linear map on f's codomain. -/
theorem exists_factor {K A W Z : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
    (f : A →ₗ[K] W) (g : A →ₗ[K] Z) (h : f.ker ≤ g.ker) :
    ∃ H : W →ₗ[K] Z, H.comp f = g := by
  let L := (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨H,hH⟩ := LinearMap.exists_extend L
  refine ⟨H,?_⟩
  ext x
  calc
    H (f x) = L (f.rangeRestrict x) := by
      have he : f.range.subtype (f.rangeRestrict x) = f x := rfl
      have hh := LinearMap.congr_fun hH (f.rangeRestrict x)
      rw [LinearMap.comp_apply,he] at hh
      exact hh
    _ = g x := by
      change (f.ker.liftQ g h) (f.quotKerEquivRange.symm ⟨f x,?_⟩) = g x
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      rfl

end ProofComplexity.LinearMapFactorThrough
end

section
-- Inlined Solutions.AdmissibleQuotient

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.Supplement.AdmissibleQuotient

open Module MvPolynomial AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

noncomputable abbrev BoolSpace (n : ℕ) := restrictDegree (Fin n) (ZMod 2) 1

instance finite_BoolSpace (n : ℕ) : Module.Finite (ZMod 2) (BoolSpace n) :=
  Module.Finite.of_basis (ProofComplexity.BooleanCoordinates.booleanBasis (Fin n))

noncomputable def reduce (n : ℕ) : MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] BoolSpace n :=
  ML.codRestrict (BoolSpace n) (fun p => (mem_restrictDegree _ _ _).mpr (ml_multilinear p))

abbrev Quot {n : ℕ} (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) :=
  BoolSpace n ⧸ C.comap (BoolSpace n).subtype

noncomputable def remainder {n : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) :
    MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] Quot C :=
  (C.comap (BoolSpace n).subtype).mkQ.comp (reduce n)

lemma remainder_zero_iff {n : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) : remainder C p = 0 ↔ ML p ∈ C := by
  change (C.comap (BoolSpace n).subtype).mkQ (reduce n p) = 0 ↔ _
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  rfl

lemma remainder_congr {n : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p q : MvPolynomial (Fin n) (ZMod 2)) (h : ML p = ML q) :
    remainder C p = remainder C q := by
  apply congrArg (C.comap (BoolSpace n).subtype).mkQ
  exact Subtype.ext h

@[simp] lemma remainder_ml {n : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) : remainder C (ML p) = remainder C p :=
  remainder_congr C _ _ (ml_idempotent p)

lemma remainder_mul_ml_left {n : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p q : MvPolynomial (Fin n) (ZMod 2)) :
    remainder C (ML p * q) = remainder C (p * q) :=
  remainder_congr C _ _ (ml_mul_left p q)

lemma remainder_mul_ml_right {n : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p q : MvPolynomial (Fin n) (ZMod 2)) :
    remainder C (p * ML q) = remainder C (p * q) :=
  remainder_congr C _ _ (ml_mul_right p q)

lemma ml_square {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2)) : ML (p*p) = ML p := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  rw [eval_ml, eval_ml, map_mul]
  simpa only [ZMod.card, pow_two] using FiniteField.pow_card (eval x p)

lemma remainder_square_mul {n : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p u : MvPolynomial (Fin n) (ZMod 2)) :
    remainder C (p*u*u) = remainder C (p*u) := by
  calc
    _ = remainder C (p*(u*u)) := by congr 1; ring
    _ = remainder C (p*ML (u*u)) := (remainder_mul_ml_right C p (u*u)).symm
    _ = _ := by rw [ml_square, remainder_mul_ml_right]

lemma cast_budget {L r : ℕ} {D : ℕ∞} (h : ((L+r : ℕ) : ℕ∞) ≤ D)
    {a b : ℕ} (ha : a ≤ L) (hb : b ≤ r) : ((a+b : ℕ) : ℕ∞) ≤ D := by
  have hh : ((a+b : ℕ) : ℕ∞) ≤ ((L+r : ℕ) : ℕ∞) := by
    exact_mod_cast (Nat.add_le_add ha hb)
  exact hh.trans h

/-- Admissibility makes multiplication well-defined on the quotient image of low-degree inputs. -/
theorem exists_multiplier {n L r : ℕ} {D : ℕ∞}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) (hC : IsAdmissible D C)
    (u : MvPolynomial (Fin n) (ZMod 2)) (hu : IsMultilinear u) (hdu : u.totalDegree ≤ r)
    (hD : ((L+r : ℕ) : ℕ∞) ≤ D) :
    ∃ H : Quot C →ₗ[ZMod 2] Quot C,
      ∀ p ∈ SemAC02.Ble (Fin n) L, H (remainder C p) = remainder C (p*u) := by
  classical
  let A := SemAC02.Ble (Fin n) L
  let f := (remainder C).domRestrict A
  let g := ((remainder C).comp (LinearMap.mulRight (ZMod 2) u)).domRestrict A
  have hker : f.ker ≤ g.ker := by
    intro p hp
    have hpC := (remainder_zero_iff C p.1).mp hp
    have hpm := (SemAC02.BooleanDegreeSpaces.mem_Ble_iff L p.1).mp p.2
    rw [ml_of_multilinear p.1 hpm.1] at hpC
    exact (remainder_zero_iff C _).mpr (hC.2 _ hpC u hu (cast_budget hD hpm.2 hdu))
  obtain ⟨H,hH⟩ := ProofComplexity.LinearMapFactorThrough.exists_factor f g hker
  exact ⟨H, fun p hp => LinearMap.congr_fun hH ⟨p,hp⟩⟩

noncomputable def errorMap {n : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P u : MvPolynomial (Fin n) (ZMod 2))
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) :
    X →ₗ[ZMod 2] Quot C :=
  ((remainder C).comp (LinearMap.mulRight (ZMod 2) (P*u))).domRestrict X

theorem exists_certificate {n s K r : ℕ} {D : ℕ∞}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) (hC : IsAdmissible D C)
    (P : MvPolynomial (Fin n) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (hD : ((P.totalDegree+K+2*r : ℕ) : ℕ∞) ≤ D) :
    ∃ H : Fin s → Quot C →ₗ[ZMod 2] Quot C,
      (∀ i, (H i).comp (errorMap C P (u i) (SemAC02.Ble (Fin n) (K-r))) =
        errorMap C P (u i) (SemAC02.Ble (Fin n) (K-r))) ∧
      ∀ i j, (H i).comp (errorMap C P (u j) (SemAC02.Ble (Fin n) (K-r))) =
        (H j).comp (errorMap C P (u i) (SemAC02.Ble (Fin n) (K-r))) := by
  classical
  let L := K-r+P.totalDegree+r
  have hbudget' : ((L+r : ℕ) : ℕ∞) ≤ ((P.totalDegree+K+2*r : ℕ) : ℕ∞) := by
    exact_mod_cast (show L+r ≤ P.totalDegree+K+2*r by dsimp [L]; omega)
  have hbudget : ((L+r : ℕ) : ℕ∞) ≤ D := hbudget'.trans hD
  choose H hH using (fun i => exists_multiplier C hC (u i) (hu i).1 (hu i).2 hbudget)
  have hlow (j : Fin s) (x : SemAC02.Ble (Fin n) (K-r)) :
      ML (x.1*(P*u j)) ∈ SemAC02.Ble (Fin n) L := by
    apply (SemAC02.BooleanDegreeSpaces.mem_Ble_iff L _).mpr
    refine ⟨ml_multilinear _, ?_⟩
    have hx := ((SemAC02.BooleanDegreeSpaces.mem_Ble_iff (K-r) x.1).mp x.2).2
    exact (ml_totalDegree_le _).trans ((totalDegree_mul _ _).trans
      ((Nat.add_le_add hx ((totalDegree_mul _ _).trans (Nat.add_le_add_left (hu j).2 _))).trans
        (by dsimp [L]; omega)))
  have haction (i j : Fin s) (x : SemAC02.Ble (Fin n) (K-r)) :
      H i (errorMap C P (u j) (SemAC02.Ble (Fin n) (K-r)) x) =
        remainder C (x.1*(P*u j)*u i) := by
    change H i (remainder C (x.1*(P*u j))) = _
    calc
      _ = H i (remainder C (ML (x.1*(P*u j)))) := by rw [remainder_ml]
      _ = remainder C (ML (x.1*(P*u j))*u i) := hH i _ (hlow j x)
      _ = _ := remainder_mul_ml_left C _ _
  refine ⟨H, ?_, ?_⟩
  · intro i
    ext x
    rw [LinearMap.comp_apply, haction]
    calc
      _ = remainder C ((x.1*P)*u i*u i) := by congr 1; ring
      _ = remainder C ((x.1*P)*u i) := remainder_square_mul C _ _
      _ = _ := by change _ = remainder C (x.1*(P*u i)); congr 1; ring
  · intro i j
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, haction, haction]
    congr 1
    ring

end AC02Frege.Supplement.AdmissibleQuotient
end

section
-- Inlined Solutions.AdmissibleErrorSpaces

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.Supplement.AdmissibleErrorSpaces

open Module MvPolynomial BooleanAlgebra AdmissibleQuotient

noncomputable def lineSpace {n s : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) :=
  BoolSpace n ⊓ ⨅ i, ((remainder C).comp (LinearMap.mulRight (ZMod 2) (P*u i))).ker

lemma mem_lineSpace {n s : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (f : MvPolynomial (Fin n) (ZMod 2)) :
    f ∈ lineSpace C P u ↔ IsMultilinear f ∧ ∀ i, ML (f*P*u i) ∈ C := by
  simp only [lineSpace, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.comp_apply, LinearMap.mulRight_apply, remainder_zero_iff, mul_assoc]
  rw [show f ∈ BoolSpace n ↔ IsMultilinear f from mem_restrictDegree _ _ _]

lemma zsol_eq {n s j : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) :
    ZsolC C u P j = (↑(SemAC02.Ble (Fin n) j ⊓ lineSpace C P u) :
      Set (MvPolynomial (Fin n) (ZMod 2))) := by
  ext f
  change f ∈ ZsolC C u P j ↔ f ∈ SemAC02.Ble (Fin n) j ∧ f ∈ lineSpace C P u
  simp only [ZsolC, Vdeg, Set.mem_setOf_eq, SemAC02.BooleanDegreeSpaces.mem_Ble_iff,
    mem_lineSpace]
  tauto

lemma solution_dim {n s j : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) :
    dimSpan (ZsolC C u P j) = finrank (ZMod 2) ↥(SemAC02.Ble (Fin n) j ⊓ lineSpace C P u) := by
  unfold dimSpan
  rw [zsol_eq, Submodule.span_eq]

lemma error_rank_nullity {n s j : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) :
    cErrC C u P j + finrank (ZMod 2) ↥(SemAC02.Ble (Fin n) j ⊓ lineSpace C P u) =
      finrank (ZMod 2) (SemAC02.Ble (Fin n) j) := by
  have hB : finrank (ZMod 2) (SemAC02.Ble (Fin n) j) = monoCount n j := by
    simpa only [Fintype.card_fin] using BooleanDegreeCounts.finrank_Ble (V := Fin n) j
  have hle : finrank (ZMod 2) ↥(SemAC02.Ble (Fin n) j ⊓ lineSpace C P u) ≤
      finrank (ZMod 2) (SemAC02.Ble (Fin n) j) := Submodule.finrank_mono inf_le_left
  unfold cErrC
  rw [solution_dim, ← hB]
  omega

lemma common_kernel_map {n s j : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) :
    (⨅ i, (errorMap C P (u i) (SemAC02.Ble (Fin n) j)).ker).map
      (SemAC02.Ble (Fin n) j).subtype = SemAC02.Ble (Fin n) j ⊓ lineSpace C P u := by
  ext f
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.2, (mem_lineSpace C P u x.1).mpr
      ⟨((SemAC02.BooleanDegreeSpaces.mem_Ble_iff j x.1).mp x.2).1, ?_⟩⟩
    intro i
    have hh := (Submodule.mem_iInf _).mp hx i
    have hz : remainder C (x.1*(P*u i)) = 0 := hh
    simpa only [mul_assoc] using (remainder_zero_iff C _).mp hz
  · intro hf
    refine ⟨⟨f,hf.1⟩, ?_, rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro i
    have hh := ((mem_lineSpace C P u f).mp hf.2).2 i
    change remainder C (f*(P*u i)) = 0
    exact (remainder_zero_iff C _).mpr (by simpa only [mul_assoc] using hh)

lemma common_rank {n s j : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) :
    cErrC C u P j = finrank (ZMod 2) (SemAC02.Ble (Fin n) j) -
      finrank (ZMod 2) ↥(⨅ i, (errorMap C P (u i) (SemAC02.Ble (Fin n) j)).ker) := by
  have hd : finrank (ZMod 2) ↥(⨅ i, (errorMap C P (u i) (SemAC02.Ble (Fin n) j)).ker) =
      finrank (ZMod 2) ↥(SemAC02.Ble (Fin n) j ⊓ lineSpace C P u) := by
    rw [← common_kernel_map C P u, Submodule.finrank_map_subtype_eq]
  rw [hd]
  have h := error_rank_nullity C P u (j := j)
  omega

lemma lineSpace_congr {n s : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P Q : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (h : ML P = ML Q) : lineSpace C P u = lineSpace C Q u := by
  ext f
  rw [mem_lineSpace, mem_lineSpace]
  have hprod (i : Fin s) : ML (f*P*u i) = ML (f*Q*u i) := by
    apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
    intro x
    have hx := congrArg (eval x) h
    simp only [eval_ml] at hx
    simp only [eval_ml, map_mul, hx]
  simp only [hprod]

@[simp] lemma cErr_ml {n s j : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) :
    cErrC C u (ML P) j = cErrC C u P j := by
  unfold cErrC
  rw [solution_dim, solution_dim, lineSpace_congr C (ML P) P u (ml_idempotent P)]

@[simp] lemma solution_dim_ml {n s j : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2)) (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) :
    dimSpan (ZsolC C u (ML P) j) = dimSpan (ZsolC C u P j) := by
  rw [solution_dim, solution_dim, lineSpace_congr C (ML P) P u (ml_idempotent P)]

end AC02Frege.Supplement.AdmissibleErrorSpaces
end

section
-- Inlined Solutions.AdmissibleOneFactorAlgebra

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.Supplement.AdmissibleOneFactorAlgebra

open Module MvPolynomial AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip
open AdmissibleQuotient AdmissibleErrorSpaces

noncomputable def combination {n s : ℕ} (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (a : Fin s → ZMod 2) : MvPolynomial (Fin n) (ZMod 2) := ∑ i, a i • u i

lemma combination_degree {n s r : ℕ} (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (hu : ∀ i, (u i).totalDegree ≤ r) (a : Fin s → ZMod 2) :
    (combination u a).totalDegree ≤ r := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_smul_le _ _).trans (hu i)

lemma factor_degree {n s r : ℕ} (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (hu : ∀ i, (u i).totalDegree ≤ r) (a : Fin s → ZMod 2) :
    (1+combination u a).totalDegree ≤ r :=
  (totalDegree_add _ _).trans (max_le (by simp) (combination_degree u hu a))

lemma complement_zero {n : ℕ} (t : MvPolynomial (Fin n) (ZMod 2)) : ML (t*(1+t)) = 0 := by
  rw [mul_add, mul_one, map_add, ml_square]
  exact CharTwo.add_self_eq_zero _

lemma remainder_combination {n s : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (f P : MvPolynomial (Fin n) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) (a : Fin s → ZMod 2) :
    remainder C (f*P*combination u a) = ∑ i, a i • remainder C (f*P*u i) := by
  rw [combination, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_smul_comm, map_smul]

noncomputable def candidate {n : ℕ}
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (t : MvPolynomial (Fin n) (ZMod 2)) :
    X →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  ML.comp ((LinearMap.mulRight (ZMod 2) t).domRestrict X)

lemma candidate_in_new {n s K r : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) (hu : ∀ i, (u i).totalDegree ≤ r)
    (a : Fin s → ZMod 2) (hrK : r ≤ K) (x : SemAC02.Ble (Fin n) (K-r)) :
    candidate (SemAC02.Ble (Fin n) (K-r)) (combination u a) x ∈
      SemAC02.Ble (Fin n) K ⊓ lineSpace C (P*(1+combination u a)) u := by
  classical
  let t := combination u a
  change ML (x.1*t) ∈ _
  have hx := (SemAC02.BooleanDegreeSpaces.mem_Ble_iff (K-r) x.1).mp x.2
  have hdeg : (ML (x.1*t)).totalDegree ≤ K :=
    (ml_totalDegree_le _).trans ((totalDegree_mul _ _).trans
      ((Nat.add_le_add hx.2 (combination_degree u hu a)).trans (by omega)))
  refine ⟨(SemAC02.BooleanDegreeSpaces.mem_Ble_iff K _).mpr ⟨ml_multilinear _,hdeg⟩, ?_⟩
  apply (mem_lineSpace C _ u _).mpr
  refine ⟨ml_multilinear _, ?_⟩
  intro i
  apply (remainder_zero_iff C _).mp
  calc
    _ = remainder C (ML (x.1*t)*(P*u i*(1+t))) := by congr 1; ring
    _ = remainder C ((x.1*t)*(P*u i*(1+t))) := remainder_mul_ml_left C _ _
    _ = remainder C ((x.1*P*u i)*(t*(1+t))) := by congr 1; ring
    _ = remainder C ((x.1*P*u i)*ML (t*(1+t))) := (remainder_mul_ml_right C _ _).symm
    _ = 0 := by rw [complement_zero, mul_zero, map_zero]

lemma old_solutions_persist {n s K r : ℕ} {D : ℕ∞}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) (hC : IsAdmissible D C)
    (P : MvPolynomial (Fin n) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) (hu : ∀ i, (u i).totalDegree ≤ r)
    (a : Fin s → ZMod 2) (hD : ((P.totalDegree+K+2*r : ℕ) : ℕ∞) ≤ D)
    (f : MvPolynomial (Fin n) (ZMod 2))
    (hf : f ∈ SemAC02.Ble (Fin n) K ⊓ lineSpace C P u) :
    f ∈ lineSpace C (P*(1+combination u a)) u := by
  have hs := (mem_lineSpace C P u f).mp hf.2
  have hd := ((SemAC02.BooleanDegreeSpaces.mem_Ble_iff K f).mp hf.1).2
  apply (mem_lineSpace C _ u f).mpr
  refine ⟨hs.1, ?_⟩
  intro i
  have hp : (ML (f*P*u i)).totalDegree ≤ K+P.totalDegree+r :=
    (ml_totalDegree_le _).trans ((totalDegree_mul _ _).trans
      ((Nat.add_le_add ((totalDegree_mul _ _).trans (Nat.add_le_add_right hd _)) (hu i))))
  have hq : (ML (1+combination u a)).totalDegree ≤ r :=
    (ml_totalDegree_le _).trans (factor_degree u hu a)
  have hbudget' : (((ML (f*P*u i)).totalDegree + (ML (1+combination u a)).totalDegree : ℕ) : ℕ∞) ≤
      ((P.totalDegree+K+2*r : ℕ) : ℕ∞) := by
    exact_mod_cast (show (ML (f*P*u i)).totalDegree + (ML (1+combination u a)).totalDegree ≤
      P.totalDegree+K+2*r by omega)
  have hc := hC.2 _ (hs.2 i) (ML (1+combination u a)) (ml_multilinear _) (hbudget'.trans hD)
  have he : ML (f*(P*(1+combination u a))*u i) =
      ML (ML (f*P*u i)*ML (1+combination u a)) := by
    rw [ml_mul_left, ml_mul_right]
    congr 1
    ring
  rw [he]
  exact hc

lemma combined_map {n s : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) (a : Fin s → ZMod 2)
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) :
    (∑ i, a i • errorMap C P (u i) X) = errorMap C P (combination u a) X := by
  ext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ i, a i • remainder C (x.1*(P*u i))) = remainder C (x.1*(P*combination u a))
  simpa only [mul_assoc] using (remainder_combination C x.1 P u a).symm

lemma candidate_relation {n s : ℕ}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (P : MvPolynomial (Fin n) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n) (ZMod 2)) (a : Fin s → ZMod 2)
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) (x : X)
    (hx : candidate X (combination u a) x ∈ lineSpace C P u) :
    errorMap C P (combination u a) X x = 0 := by
  classical
  let t := combination u a
  have hs := ((mem_lineSpace C P u _).mp hx).2
  change ∀ i, ML (ML (x.1*t)*P*u i) ∈ C at hs
  have hz : remainder C (ML (x.1*t)*P*t) = 0 := by
    rw [remainder_combination]
    apply Finset.sum_eq_zero
    intro i hi
    rw [(remainder_zero_iff C _).mpr (hs i), smul_zero]
  change remainder C (x.1*(P*t)) = 0
  calc
    _ = remainder C ((x.1*P)*t) := by congr 1; ring
    _ = remainder C ((x.1*P)*t*t) := (remainder_square_mul C _ _).symm
    _ = remainder C ((x.1*t)*(P*t)) := by congr 1; ring
    _ = remainder C (ML (x.1*t)*(P*t)) := (remainder_mul_ml_left C _ _).symm
    _ = _ := by simpa only [mul_assoc] using hz

end AC02Frege.Supplement.AdmissibleOneFactorAlgebra
end

section
-- Inlined Solutions.PangFactorization

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.PangFactorization

open Matrix MvPolynomial

/-- A binary certificate for Pang's Frobenius kernel condition. The auxiliary maps need only
satisfy their identities on the images of the given matrices. -/
theorem pencil_factorization {K ι p q : Type} [Field K] [CharP K 2] [Fintype p]
    (H : ι → Matrix p p K) (M : ι → Matrix p q K)
    (hdiag : ∀ i, H i*M i = M i) (hcross : ∀ i j, H i*M j = H j*M i)
    (θ : ι → K) (S : Finset ι) :
    (∑ i ∈ S, θ i • H i)*(∑ i ∈ S, θ i • M i) = ∑ i ∈ S, (θ i)^2 • M i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]
    have hdiag' : (θ i • H i)*(θ i • M i) = (θ i)^2 • M i := by
      rw [Matrix.smul_mul,Matrix.mul_smul,hdiag]
      simp only [smul_smul,pow_two]
    have hcross' : (θ i • H i)*(∑ j ∈ S, θ j • M j) =
        (∑ j ∈ S, θ j • H j)*(θ i • M i) := by
      rw [Matrix.mul_sum,Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_smul,hcross i j]
      simp only [smul_smul,mul_comm]
    have hz : (θ i • H i)*(∑ j ∈ S, θ j • M j)+
        (∑ j ∈ S, θ j • H j)*(θ i • M i) = 0 := by
      rw [hcross']
      ext r j
      exact CharTwo.add_self_eq_zero _
    calc
      _ = (θ i • H i)*(θ i • M i)+
          ((θ i • H i)*(∑ j ∈ S, θ j • M j)+(∑ j ∈ S, θ j • H j)*(θ i • M i))+
          (∑ j ∈ S, θ j • H j)*(∑ j ∈ S, θ j • M j) := by
        simp only [Matrix.add_mul,Matrix.mul_add]
        abel
      _ = _ := by rw [hdiag',hz,ih,add_zero]

/-- The factorization directly verifies the kernel hypothesis over the formal coefficient field. -/
theorem binary_kernel_condition {s p q : ℕ}
    (H : Fin s → Matrix (Fin p) (Fin p) (ZMod 2))
    (M : Fin s → Matrix (Fin p) (Fin q) (ZMod 2))
    (hdiag : ∀ i, H i*M i = M i) (hcross : ∀ i j, H i*M j = H j*M i) :
    let P := MvPolynomial (Fin s) (ZMod 2)
    let E := FractionRing P
    let f := algebraMap (ZMod 2) E
    let θ := fun i => algebraMap P E (X i)
    ∀ v, (∑ i, θ i • (M i).map f) *ᵥ v = 0 →
      (∑ i, (θ i)^2 • (M i).map f) *ᵥ v = 0 := by
  intro P E f θ v hv
  have hd (i) : (H i).map f*(M i).map f = (M i).map f := by
    rw [← Matrix.map_mul,hdiag]
  have hc (i j) : (H i).map f*(M j).map f = (H j).map f*(M i).map f := by
    rw [← Matrix.map_mul,← Matrix.map_mul,hcross]
  have he := pencil_factorization (fun i => (H i).map f) (fun i => (M i).map f) hd hc θ Finset.univ
  rw [← he,← Matrix.mulVec_mulVec,hv]
  exact Matrix.mulVec_zero _

end AC02Frege.PangFactorization
end

section
-- Inlined Solutions.LinearPang

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.LinearPang

open Module Matrix

lemma matrix_rank {X W : Type} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) X] [Module.Finite (ZMod 2) W]
    (f : X →ₗ[ZMod 2] W) :
    ((LinearMap.toMatrix (finBasis (ZMod 2) X) (finBasis (ZMod 2) W)) f).rank =
      finrank (ZMod 2) f.range := by
  rw [Matrix.rank_eq_finrank_range_toLin _ (finBasis (ZMod 2) W) (finBasis (ZMod 2) X),Matrix.toLin_toMatrix]

/-- The linear-map form of Pang's lemma when the common kernel is zero. -/
theorem half_rank_of_joint_injective {X W : Type} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) X] [Module.Finite (ZMod 2) W]
    (s : ℕ) (M : Fin s → X →ₗ[ZMod 2] W) (H : Fin s → W →ₗ[ZMod 2] W)
    (hdiag : ∀ i, (H i).comp (M i) = M i) (hcross : ∀ i j, (H i).comp (M j) = (H j).comp (M i))
    (hinj : ∀ x : X, (∀ i, M i x = 0) → x = 0) :
    ∃ a : Fin s → ZMod 2, (finrank (ZMod 2) X : ℝ)/2 ≤
      (finrank (ZMod 2) (∑ i, a i • M i).range : ℝ) := by
  classical
  let bX := finBasis (ZMod 2) X
  let bW := finBasis (ZMod 2) W
  let A := fun i => (LinearMap.toMatrix bX bW) (M i)
  let B := fun i => (LinearMap.toMatrix bW bW) (H i)
  have hdiag' (i) : B i*A i = A i := by
    rw [← LinearMap.toMatrix_comp bX bW bW,hdiag]
  have hcross' (i j) : B i*A j = B j*A i := by
    rw [← LinearMap.toMatrix_comp bX bW bW,← LinearMap.toMatrix_comp bX bW bW,hcross]
  let S := Matrix.of (fun (ik : Fin s × Fin (finrank (ZMod 2) W)) (j : Fin (finrank (ZMod 2) X)) => A ik.1 ik.2 j)
  have heval (i) (v : Fin (finrank (ZMod 2) X) → ZMod 2) :
      A i *ᵥ v = bW.equivFun (M i (bX.equivFun.symm v)) := by
    have h := LinearMap.toMatrix_mulVec_repr bX bW (M i) (bX.equivFun.symm v)
    simpa only [← Module.Basis.equivFun_apply,LinearEquiv.apply_symm_apply] using h
  have hSker : S.mulVecLin.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hx : bX.equivFun.symm v = 0 := by
      apply hinj
      intro i
      apply bW.equivFun.injective
      rw [map_zero,← heval]
      funext r
      exact congrFun hv (i,r)
    have hv0 := congrArg bX.equivFun hx
    simpa only [LinearEquiv.apply_symm_apply,map_zero] using hv0
  have hSrank : S.rank = finrank (ZMod 2) X := by
    rw [Matrix.rank,LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hSker),Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
  obtain ⟨_,_,a,ha⟩ := AC02Frege.theorem_A_5_pang_matrix_lemma A
    (PangFactorization.binary_kernel_condition B A hdiag' hcross')
  refine ⟨a,?_⟩
  have hsum : (∑ i, a i • A i) = (LinearMap.toMatrix bX bW) (∑ i, a i • M i) := by
    rw [map_sum]
    simp only [map_smul]
    rfl
  change (S.rank : ℝ)/2 ≤ ((∑ i, a i • A i).rank : ℝ) at ha
  rw [hSrank,hsum,matrix_rank] at ha
  exact ha

/-- The general linear-map form, obtained by restricting the domain to a complement of the
common kernel. The rank of the chosen combination can only increase on the full domain. -/
theorem half_joint_rank {X W : Type} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) X] [Module.Finite (ZMod 2) W]
    (s : ℕ) (M : Fin s → X →ₗ[ZMod 2] W) (H : Fin s → W →ₗ[ZMod 2] W)
    (hdiag : ∀ i, (H i).comp (M i) = M i) (hcross : ∀ i j, (H i).comp (M j) = (H j).comp (M i)) :
    ∃ a : Fin s → ZMod 2,
      ((finrank (ZMod 2) X-finrank (ZMod 2) ↥(⨅ i, (M i).ker) : ℕ) : ℝ)/2 ≤
        (finrank (ZMod 2) (∑ i, a i • M i).range : ℝ) := by
  classical
  let K := ⨅ i, (M i).ker
  obtain ⟨U,hU⟩ := K.exists_isCompl
  let M' := fun i => (M i).comp U.subtype
  have hd (i) : (H i).comp (M' i) = M' i := by
    rw [← LinearMap.comp_assoc,hdiag]
  have hc (i j) : (H i).comp (M' j) = (H j).comp (M' i) := by
    rw [← LinearMap.comp_assoc,← LinearMap.comp_assoc,hcross]
  have hjoint (x : U) (hx : ∀ i, M' i x = 0) : x = 0 := by
    apply Subtype.ext
    apply (Submodule.disjoint_def.mp hU.disjoint)
    · exact (Submodule.mem_iInf _).mpr hx
    · exact x.2
  obtain ⟨a,ha⟩ := half_rank_of_joint_injective s M' H hd hc hjoint
  have hdim : finrank (ZMod 2) U = finrank (ZMod 2) X-finrank (ZMod 2) K := by
    have h := Submodule.finrank_add_eq_of_isCompl hU
    omega
  have hsum : (∑ i, a i • M' i) = (∑ i, a i • M i).comp U.subtype := by
    ext x
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,M']
  have hr : finrank (ZMod 2) (∑ i, a i • M' i).range ≤
      finrank (ZMod 2) (∑ i, a i • M i).range := by
    rw [hsum]
    exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  refine ⟨a,?_⟩
  rw [hdim] at ha
  exact ha.trans (by exact_mod_cast hr)

end AC02Frege.LinearPang
end

section
-- Inlined Solutions.LinearDimensionGain

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace ProofComplexity.LinearDimensionGain

open Module

/-- A map of candidates whose relations modulo U are killed by Phi contributes at least
rank(Phi) new dimensions beyond U in any containing finite-dimensional space. -/
theorem gain_bound {K X V W : Type} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (U Z : Submodule K V) [Module.Finite K Z] (hUZ : U ≤ Z)
    (L : X →ₗ[K] V) (Φ : X →ₗ[K] W) (hL : ∀ x, L x ∈ Z)
    (hkill : ∀ x, L x ∈ U → Φ x = 0) :
    finrank K U+finrank K Φ.range ≤ finrank K Z := by
  let U' := U.comap Z.subtype
  let L' := L.codRestrict Z hL
  let f := U'.mkQ.comp L'
  have hker : f.ker ≤ Φ.ker := by
    intro x hx
    apply hkill x
    have hh : U'.mkQ (L' x) = 0 := hx
    rw [← LinearMap.mem_ker,Submodule.ker_mkQ] at hh
    exact hh
  obtain ⟨H,hH⟩ := LinearMapFactorThrough.exists_factor f Φ hker
  have hrange : Φ.range ≤ H.range := by
    rw [← hH]
    exact LinearMap.range_comp_le_range _ _
  have hr : finrank K Φ.range ≤ finrank K (Z ⧸ U') :=
    (Submodule.finrank_mono hrange).trans H.finrank_range_le
  have hmap : U'.map Z.subtype = U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hUZ hx⟩,hx,rfl⟩
  have hdimU : finrank K U' = finrank K U := by
    rw [← hmap,Submodule.finrank_map_subtype_eq]
  have hdim := Submodule.finrank_quotient_add_finrank U'
  rw [hdimU] at hdim
  omega

end ProofComplexity.LinearDimensionGain
end

section
-- Inlined Solutions.AdmissibleOneFactorGain

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.Supplement.AdmissibleOneFactorGain

open Module MvPolynomial AdmissibleQuotient AdmissibleErrorSpaces AdmissibleOneFactorAlgebra

/-- The one-factor gain needs no special form of the current multilinear approximator. -/
theorem gain {n s K r : ℕ} {D : ℕ∞}
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) (hC : IsAdmissible D C)
    (P : MvPolynomial (Fin n) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r) (hrK : r ≤ K)
    (hD : ((P.totalDegree+K+2*r : ℕ) : ℕ∞) ≤ D) :
    ∃ a : Fin s → ZMod 2,
      (cErrC C u (ML (P*(1+∑ i, a i • u i))) K : ℝ) ≤
        (cErrC C u P K : ℝ) - (cErrC C u P (K-r) : ℝ)/2 ∧
      (dimSpan (ZsolC C u P K) : ℝ) + (cErrC C u P (K-r) : ℝ)/2 ≤
        (dimSpan (ZsolC C u (ML (P*(1+∑ i, a i • u i))) K) : ℝ) := by
  classical
  let B := SemAC02.Ble (Fin n) K
  let X := SemAC02.Ble (Fin n) (K-r)
  let U := B ⊓ lineSpace C P u
  let M := fun i => errorMap C P (u i) X
  obtain ⟨H,hd,hc⟩ := exists_certificate C hC P u hu hD
  obtain ⟨a,ha⟩ := AC02Frege.LinearPang.half_joint_rank s M H hd hc
  let t := combination u a
  let P' := P*(1+t)
  let Z := B ⊓ lineSpace C P' u
  let L := candidate X t
  let Φ := errorMap C P t X
  letI : Module.Finite (ZMod 2) Z := Module.Finite.of_injective
    (Submodule.inclusion (show Z ≤ B from inf_le_left))
    (Submodule.inclusion_injective (show Z ≤ B from inf_le_left))
  have hsum : (∑ i, a i • M i) = Φ := combined_map C P u a X
  rw [hsum] at ha
  have hcommon : cErrC C u P (K-r) =
      finrank (ZMod 2) X-finrank (ZMod 2) ↥(⨅ i, (M i).ker) := common_rank C P u
  rw [← hcommon] at ha
  have hUZ : U ≤ Z := by
    intro f hf
    exact ⟨hf.1, old_solutions_persist C hC P u (fun i => (hu i).2) a hD f hf⟩
  have hL : ∀ x : X, L x ∈ Z := by
    intro x
    exact candidate_in_new C P u (fun i => (hu i).2) a hrK x
  have hkill : ∀ x : X, L x ∈ U → Φ x = 0 := by
    intro x hx
    exact candidate_relation C P u a X x hx.2
  have hgain := ProofComplexity.LinearDimensionGain.gain_bound U Z hUZ L Φ hL hkill
  have hgainR : (finrank (ZMod 2) U : ℝ) + (finrank (ZMod 2) Φ.range : ℝ) ≤
      (finrank (ZMod 2) Z : ℝ) := by exact_mod_cast hgain
  have hdim : (finrank (ZMod 2) U : ℝ) + (cErrC C u P (K-r) : ℝ)/2 ≤
      (finrank (ZMod 2) Z : ℝ) := by linarith
  have hnold := error_rank_nullity C P u (j := K)
  have hnnew := error_rank_nullity C P' u (j := K)
  have hnoldR : (cErrC C u P K : ℝ) + (finrank (ZMod 2) U : ℝ) =
      (finrank (ZMod 2) B : ℝ) := by exact_mod_cast hnold
  have hnnewR : (cErrC C u P' K : ℝ) + (finrank (ZMod 2) Z : ℝ) =
      (finrank (ZMod 2) B : ℝ) := by exact_mod_cast hnnew
  refine ⟨a, ?_, ?_⟩
  · rw [cErr_ml]
    change (cErrC C u P' K : ℝ) ≤ _
    linarith
  · rw [solution_dim_ml, solution_dim, solution_dim]
    exact hdim

theorem theorem_A_2 {n s t : ℕ} (D : ℕ∞)
    (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (hC : IsAdmissible D C) (r K : ℕ) (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (a : Fin t → Fin s → ZMod 2) (hKr : r ≤ K)
    (hdeg : (((approxProd u a).totalDegree+K+2*r : ℕ) : ℕ∞) ≤ D) :
    ∃ ε : Fin s → ZMod 2,
      (cErrC C u (ML (approxProd u a*(1+∑ i, ε i • u i))) K : ℝ) ≤
        (cErrC C u (approxProd u a) K : ℝ) - (cErrC C u (approxProd u a) (K-r) : ℝ)/2 ∧
      (dimSpan (ZsolC C u (approxProd u a) K) : ℝ) +
        (cErrC C u (approxProd u a) (K-r) : ℝ)/2 ≤
        (dimSpan (ZsolC C u (ML (approxProd u a*(1+∑ i, ε i • u i))) K) : ℝ) :=
  gain C hC (approxProd u a) u hu hKr hdeg

end AC02Frege.Supplement.AdmissibleOneFactorGain
end

open AC02Frege AC02Frege.Supplement MvPolynomial

theorem solution {n s t : ℕ} (D : ℕ∞) (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (hC : IsAdmissible D C) (r K : ℕ) (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (a : Fin t → Fin s → ZMod 2) (hKr : r ≤ K)
    (hdeg : (((approxProd u a).totalDegree + K + 2 * r : ℕ) : ℕ∞) ≤ D) :
    ∃ ε : Fin s → ZMod 2,
      ((cErrC C u (ML (approxProd u a * (1 + ∑ i, ε i • u i))) K : ℕ) : ℝ) ≤
          (cErrC C u (approxProd u a) K : ℝ) - (cErrC C u (approxProd u a) (K - r) : ℝ) / 2 ∧
      (AC02Frege.dimSpan (ZsolC C u (approxProd u a) K) : ℝ) +
          (cErrC C u (approxProd u a) (K - r) : ℝ) / 2 ≤
        (AC02Frege.dimSpan (ZsolC C u (ML (approxProd u a * (1 + ∑ i, ε i • u i))) K) : ℝ)  := by
  exact AC02Frege.Supplement.AdmissibleOneFactorGain.theorem_A_2 D C hC r K u hu a hKr hdeg
