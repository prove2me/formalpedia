-- Prove2me | solution 1 for AC02Frege.corollary_5_3_rank_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T05:21:44.121051+00:00
-- url     : https://prove2.me/submissions/d5514f7b-5d3d-4fce-bf60-7f986137885f

import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_multiplierSpace
import Mathlib
import Definitions.Def_AC02Frege_majorityExpansion
import Definitions.Def_AC02Frege_PC
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Definitions.Def_AC02Frege_rankCounts
import Theorems.Thm_AC02Frege_theorem_A_5_pang_matrix_lemma
import Definitions.Def_AC02Frege_approximants

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
-- Inlined Solutions.MajorityIdeal

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip

namespace AC02Frege.MajorityIdeal

noncomputable def majorityMul (ℓ : ℕ) :
    MvPolynomial (Fin ℓ) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin ℓ) (ZMod 2) where
  toFun p := ML (majOne ℓ * p)
  map_add' p q := by rw [mul_add, map_add]
  map_smul' c p := by simp only [mul_smul_comm, map_smul, RingHom.id_apply]

theorem ideal_eq_vanishing (ℓ : ℕ) (p : MvPolynomial (Fin ℓ) (ZMod 2)) :
    p ∈ (majorityMul ℓ).range ↔ IsMultilinear p ∧
      ∀ x : Fin ℓ → ZMod 2, (Finset.univ.filter (fun i => x i = 1)).card ≤ ℓ / 2 →
        eval x p = 0 := by
  classical
  constructor
  · rintro ⟨q, rfl⟩
    change IsMultilinear (ML (majOne ℓ * q)) ∧ _
    refine ⟨ml_multilinear _, ?_⟩
    intro x hx
    change eval x (ML (majOne ℓ * q)) = 0
    rw [eval_ml, map_mul, majOne_eval, if_neg (by omega), zero_mul]
  · rintro ⟨hp, hv⟩
    refine ⟨p, ?_⟩
    change ML (majOne ℓ * p) = p
    apply multilinear_ext (ml_multilinear _) hp
    intro x
    change eval x (ML (majOne ℓ * p)) = eval x p
    rw [eval_ml, map_mul, majOne_eval]
    split_ifs with hx
    · rw [one_mul]
    · rw [zero_mul, hv x (by omega)]

theorem pointPoly_mem_heavy (ℓ : ℕ) (S : Finset (Fin ℓ)) (hS : ℓ / 2 < S.card) :
    pointPoly S ∈ monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card) := by
  apply (mem_monomialSpan_iff _ _).mpr
  refine ⟨pointPoly_multilinear S, ?_⟩
  intro s hs
  have hml := pointPoly_multilinear S s hs
  rw [pointPoly_factor] at hs
  have hd := support_mul_xMon_degree S _ s hs
  rw [squarefree_sum s hml] at hd
  omega

theorem vanishing_mem_heavy (ℓ : ℕ) (p : MvPolynomial (Fin ℓ) (ZMod 2))
    (hp : IsMultilinear p)
    (hv : ∀ x : Fin ℓ → ZMod 2,
      (Finset.univ.filter (fun i => x i = 1)).card ≤ ℓ / 2 → eval x p = 0) :
    p ∈ monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card) := by
  classical
  rw [point_interpolation p hp]
  apply Submodule.sum_mem
  intro S _
  by_cases hS : ℓ / 2 < S.card
  · exact Submodule.smul_mem _ _ (pointPoly_mem_heavy ℓ S hS)
  · have hz := hv (fun i => if i ∈ S then (1 : ZMod 2) else 0)
      (by simpa only [ones_of_point] using Nat.le_of_not_gt hS)
    rw [hz, zero_smul]
    exact Submodule.zero_mem _

theorem ideal_eq_heavy (ℓ : ℕ) :
    (majorityMul ℓ).range = monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨hml, hv⟩ := (ideal_eq_vanishing ℓ p).mp hp
    exact vanishing_mem_heavy ℓ p hml hv
  · apply Submodule.span_le.mpr
    rintro p ⟨S, hS, rfl⟩
    refine ⟨xMon S, ?_⟩
    change ML (majOne ℓ * xMon S) = xMon S
    rw [mul_comm]
    exact heavy_monomial_absorbs_majority ℓ S hS

theorem light_inter_ideal (ℓ : ℕ) (p : MvPolynomial (Fin ℓ) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2))
    (hi : p ∈ (majorityMul ℓ).range) : p = 0 := by
  rw [ideal_eq_heavy] at hi
  obtain ⟨_, hl⟩ := (mem_monomialSpan_iff _ _).mp hp
  obtain ⟨_, hh⟩ := (mem_monomialSpan_iff _ _).mp hi
  apply MvPolynomial.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have := hl s hs
  have := hh s hs
  omega

end AC02Frege.MajorityIdeal
end

section
-- Inlined Solutions.MajorityInjective

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip AC02Frege.MajorityIdeal

namespace AC02Frege.MajorityInjective

theorem flipped_weight (ℓ : ℕ) (x : Fin ℓ → ZMod 2) :
    (Finset.univ.filter (fun i => 1 + x i = 1)).card +
      (Finset.univ.filter (fun i => x i = 1)).card = ℓ := by
  classical
  have heq : Finset.univ.filter (fun i => 1 + x i = 1) =
      (Finset.univ.filter (fun i => x i = 1))ᶜ := by
    ext i
    rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi, CharTwo.add_self_eq_zero]
  rw [heq, Finset.card_compl]
  have hc := Finset.card_le_univ (Finset.univ.filter (fun i => x i = 1))
  simp only [Fintype.card_fin] at *
  omega

theorem vanishing_H1_degree (ℓ : ℕ) (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (hne : p ≠ 0)
    (hv : ∀ x : Fin ℓ → ZMod 2,
      ℓ / 2 < (Finset.univ.filter (fun i => x i = 1)).card → eval x p = 0) :
    ℓ / 2 + 1 ≤ p.totalDegree := by
  classical
  by_contra hd
  have hfdeg : (flip p).totalDegree ≤ ℓ / 2 := (flip_degree_le p).trans (by omega)
  have hfml := flip_multilinear p
  have hflight := (mem_light_iff (ℓ / 2) (flip p)).mpr ⟨hfml, hfdeg⟩
  have hfideal : flip p ∈ (majorityMul ℓ).range := by
    apply (ideal_eq_vanishing ℓ (flip p)).mpr
    refine ⟨hfml, ?_⟩
    intro x hx
    rw [flip_eval]
    apply hv
    have hc := flipped_weight ℓ x
    rcases hℓ with ⟨k, hk⟩
    omega
  have hz := light_inter_ideal ℓ (flip p) hflight hfideal
  apply hne
  calc
    p = flip (flip p) := (flip_involution p hp).symm
    _ = flip 0 := congrArg (BooleanFlip.flip (V := Fin ℓ)) hz
    _ = 0 := by simp [BooleanFlip.flip]

theorem majority_injective_light (ℓ : ℕ) (hℓ : Odd ℓ)
    (v w : MvPolynomial (Fin ℓ) (ZMod 2))
    (hv : IsMultilinear v) (hdv : v.totalDegree ≤ ℓ / 2)
    (hw : IsMultilinear w) (hdw : w.totalDegree ≤ ℓ / 2)
    (heq : majorityMul ℓ v = majorityMul ℓ w) : v = w := by
  classical
  have hsum : IsMultilinear (v + w) :=
    (mem_restrictDegree (Fin ℓ) _ 1).mp ((restrictDegree (Fin ℓ) (ZMod 2) 1).add_mem
      ((mem_restrictDegree (Fin ℓ) _ 1).mpr hv) ((mem_restrictDegree (Fin ℓ) _ 1).mpr hw))
  have hd : (v + w).totalDegree ≤ ℓ / 2 :=
    (totalDegree_add _ _).trans (max_le hdv hdw)
  have hz : v + w = 0 := by
    by_contra hne
    have hl := vanishing_H1_degree ℓ hℓ (v + w) hsum hne ?_
    · omega
    · intro x hx
      have he := congrArg (eval x) heq
      change eval x (ML (majOne ℓ * v)) = eval x (ML (majOne ℓ * w)) at he
      simp only [eval_ml, map_mul, majOne_eval, if_pos hx, one_mul] at he
      rw [map_add, he, CharTwo.add_self_eq_zero]
  have he := congrArg (fun p => p + w) hz
  simpa only [CharTwo.add_cancel_right, zero_add] using he

end AC02Frege.MajorityInjective
end

section
-- Inlined Solutions.MajorityBasis

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip AC02Frege.MajorityIdeal
open AC02Frege.MajorityInjective

namespace AC02Frege.MajorityBasis

theorem monomialSpan_eq_span_range {V : Type*} (P : Finset V → Prop) :
    monomialSpan P = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset V // P S} => xMon S.1)) := by
  have hset : {p : MvPolynomial V (ZMod 2) | ∃ S : Finset V, P S ∧ p = xMon S} =
      Set.range (fun S : {S : Finset V // P S} => xMon S.1) := by
    ext p
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨⟨S, hS⟩, rfl⟩
    · rintro ⟨S, rfl⟩
      exact ⟨S.1, S.2, rfl⟩
  exact congrArg (Submodule.span (ZMod 2)) hset

theorem monomialSpan_linearIndependent {V : Type*} (P : Finset V → Prop) :
    LinearIndependent (ZMod 2) (fun S : {S : Finset V // P S} => xMon S.1) :=
  xMon_linearIndependent.comp Subtype.val Subtype.val_injective

theorem split_light_heavy (ℓ : ℕ) (p : MvPolynomial (Fin ℓ) (ZMod 2))
    (hp : IsMultilinear p) :
    ∃ u ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2),
      ∃ w ∈ (majorityMul ℓ).range, p = u + w := by
  classical
  let L := monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2)
  let H := monomialSpan (fun S : Finset (Fin ℓ) => ℓ / 2 < S.card)
  have hmem : p ∈ L ⊔ H := by
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro s hs
    rw [squarefree_monomial s _ (hp s hs)]
    apply Submodule.smul_mem
    by_cases hd : s.support.card ≤ ℓ / 2
    · exact (show L ≤ L ⊔ H from le_sup_left) (Submodule.subset_span ⟨s.support, hd, rfl⟩)
    · exact (show H ≤ L ⊔ H from le_sup_right)
        (Submodule.subset_span ⟨s.support, by omega, rfl⟩)
  obtain ⟨u, hu, w, hw, heq⟩ := Submodule.mem_sup.mp hmem
  refine ⟨u, hu, w, ?_, heq.symm⟩
  rw [ideal_eq_heavy]
  exact hw

noncomputable def lightHeavyEquiv (ℓ : ℕ) (hℓ : Odd ℓ) :
    {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} ≃
      {T : Finset (Fin ℓ) // ℓ / 2 < T.card} where
  toFun S := ⟨S.1ᶜ, by
    rw [Finset.card_compl]
    have hc := Finset.card_le_univ S.1
    have hS := S.2
    simp only [Fintype.card_fin] at *
    rcases hℓ with ⟨k, hk⟩
    omega⟩
  invFun T := ⟨T.1ᶜ, by
    rw [Finset.card_compl]
    have hc := Finset.card_le_univ T.1
    have hT := T.2
    simp only [Fintype.card_fin] at *
    rcases hℓ with ⟨k, hk⟩
    omega⟩
  left_inv S := Subtype.ext (compl_compl _)
  right_inv T := Subtype.ext (compl_compl _)

theorem majority_basis_independent (ℓ : ℕ) (hℓ : Odd ℓ) :
    LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} => majorityMul ℓ (xMon S.1)) := by
  apply (monomialSpan_linearIndependent (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2)).map_injOn
  intro v hv w hw heq
  have hv' : v ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2) := by
    rwa [monomialSpan_eq_span_range]
  have hw' : w ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2) := by
    rwa [monomialSpan_eq_span_range]
  obtain ⟨hvm, hvd⟩ := (mem_light_iff _ _).mp hv'
  obtain ⟨hwm, hwd⟩ := (mem_light_iff _ _).mp hw'
  exact majority_injective_light ℓ hℓ v w hvm hvd hwm hwd heq

theorem majority_basis_span (ℓ : ℕ) (hℓ : Odd ℓ) :
    (majorityMul ℓ).range = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} => majorityMul ℓ (xMon S.1))) := by
  classical
  let H := monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card)
  let B := Submodule.span (ZMod 2)
    (Set.range (fun S : {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} => majorityMul ℓ (xMon S.1)))
  have hH : H = Submodule.span (ZMod 2)
      (Set.range (fun T : {T : Finset (Fin ℓ) // ℓ / 2 < T.card} => xMon T.1)) :=
    monomialSpan_eq_span_range _
  letI : FiniteDimensional (ZMod 2) H := by
    rw [hH]
    exact FiniteDimensional.span_of_finite (ZMod 2) (Set.finite_range _)
  have hle : B ≤ H := by
    apply Submodule.span_le.mpr
    rintro p ⟨S, rfl⟩
    change majorityMul ℓ (xMon S.1) ∈ monomialSpan (fun T : Finset (Fin ℓ) => ℓ / 2 < T.card)
    rw [← ideal_eq_heavy]
    exact LinearMap.mem_range_self _ _
  have heq : Module.finrank (ZMod 2) B = Module.finrank (ZMod 2) H := by
    rw [show Module.finrank (ZMod 2) B =
      Fintype.card {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} from
        finrank_span_eq_card (majority_basis_independent ℓ hℓ)]
    rw [hH, finrank_span_eq_card (monomialSpan_linearIndependent _)]
    exact Fintype.card_congr (lightHeavyEquiv ℓ hℓ)
  have hBH := Submodule.eq_of_le_of_finrank_eq hle heq
  rw [ideal_eq_heavy]
  exact hBH.symm

theorem ideal_has_light_preimage (ℓ : ℕ) (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin ℓ) (ZMod 2)) (hp : p ∈ (majorityMul ℓ).range) :
    ∃ v, IsMultilinear v ∧ v.totalDegree ≤ ℓ / 2 ∧ majorityMul ℓ v = p := by
  classical
  let L := monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2)
  have heq : L.map (majorityMul ℓ) = (majorityMul ℓ).range := by
    rw [show L = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2} => xMon S.1)) from
        monomialSpan_eq_span_range _]
    rw [Submodule.map_span, ← Set.range_comp, majority_basis_span ℓ hℓ]
    rfl
  rw [← heq] at hp
  obtain ⟨v, hv, rfl⟩ := hp
  obtain ⟨hml, hd⟩ := (mem_light_iff _ _).mp hv
  exact ⟨v, hml, hd, rfl⟩

end AC02Frege.MajorityBasis
end

section
-- Inlined Solutions.MajorityExpansion

open MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation
open AC02Frege.BooleanBasis AC02Frege.BooleanFlip AC02Frege.MajorityIdeal
open AC02Frege.MajorityInjective AC02Frege.MajorityBasis

namespace AC02Frege.MajorityExpansion

theorem unique_expansion (ℓ : ℕ) (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) :
    ∃! uv : MvPolynomial (Fin ℓ) (ZMod 2) × MvPolynomial (Fin ℓ) (ZMod 2),
      IsMultilinear uv.1 ∧ IsMultilinear uv.2 ∧ uv.1.totalDegree ≤ ℓ / 2 ∧
        uv.2.totalDegree ≤ ℓ / 2 ∧ p = uv.1 + majorityMul ℓ uv.2 := by
  classical
  obtain ⟨u, hu, w, hw, heq⟩ := split_light_heavy ℓ p hp
  obtain ⟨hum, hud⟩ := (mem_light_iff _ _).mp hu
  obtain ⟨v, hvm, hvd, hvp⟩ := ideal_has_light_preimage ℓ hℓ w hw
  have hpuv : p = u + majorityMul ℓ v := by rw [hvp]; exact heq
  refine ⟨(u, v), ⟨hum, hvm, hud, hvd, hpuv⟩, ?_⟩
  rintro ⟨u', v'⟩ ⟨hu'm, hv'm, hu'd, hv'd, heq'⟩
  have hrel : u' - u = majorityMul ℓ v - majorityMul ℓ v' := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    exact heq'.symm.trans (hpuv.trans (add_comm _ _))
  have hlight : u' - u ∈ monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2) :=
    Submodule.sub_mem _ ((mem_light_iff _ _).mpr ⟨hu'm, hu'd⟩) hu
  have hideal : u' - u ∈ (majorityMul ℓ).range := by
    rw [hrel]
    exact Submodule.sub_mem _ (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  have hu'eq : u' = u := sub_eq_zero.mp (light_inter_ideal ℓ (u' - u) hlight hideal)
  have hveq : majorityMul ℓ v' = majorityMul ℓ v := by
    apply add_left_cancel (a := u)
    rw [← hpuv, ← hu'eq]
    exact heq'.symm
  exact Prod.ext hu'eq (majority_injective_light ℓ hℓ v' v hv'm hv'd hvm hvd hveq)

end AC02Frege.MajorityExpansion
end

section
-- Inlined Solutions.MajorityFunctionBasis

open MvPolynomial AC02Frege Module
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation AC02Frege.BooleanBasis
open AC02Frege.MajorityIdeal AC02Frege.MajorityInjective AC02Frege.MajorityBasis
open AC02Frege.MajorityExpansion

namespace AC02Frege.MajorityFunctionBasis

abbrev LightIndex (ℓ : ℕ) := {S : Finset (Fin ℓ) // S.card ≤ ℓ / 2}

noncomputable abbrev LightSpace (ℓ : ℕ) :=
  monomialSpan (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2)

noncomputable def lightBasis (ℓ : ℕ) :
    Basis (LightIndex ℓ) (ZMod 2) (LightSpace ℓ) := by
  let b := Basis.span (monomialSpan_linearIndependent (fun S : Finset (Fin ℓ) => S.card ≤ ℓ / 2))
  exact b.map (LinearEquiv.ofEq _ _ (monomialSpan_eq_span_range _).symm)

@[simp] theorem lightBasis_coe (ℓ : ℕ) (S : LightIndex ℓ) :
    ((lightBasis ℓ S : LightSpace ℓ) : MvPolynomial (Fin ℓ) (ZMod 2)) = xMon S.1 := by
  simp only [lightBasis, Basis.map_apply]
  rw [LinearEquiv.coe_ofEq_apply]
  exact Basis.coe_span_apply _ _

noncomputable def pairEvaluation (ℓ : ℕ) :
    LightSpace ℓ × LightSpace ℓ →ₗ[ZMod 2] ((Fin ℓ → ZMod 2) → ZMod 2) where
  toFun uv x := eval x ((uv.1 : MvPolynomial (Fin ℓ) (ZMod 2)) + majorityMul ℓ uv.2)
  map_add' u v := by
    ext x
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, Pi.add_apply]
    abel
  map_smul' c u := by
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul,
      ← smul_add, RingHom.id_apply, Pi.smul_apply]
    rw [smul_eval]
    rfl

theorem pair_polynomial_multilinear (ℓ : ℕ) (uv : LightSpace ℓ × LightSpace ℓ) :
    IsMultilinear ((uv.1 : MvPolynomial (Fin ℓ) (ZMod 2)) + majorityMul ℓ uv.2) := by
  have hu := ((mem_light_iff _ _).mp uv.1.2).1
  have hv : IsMultilinear (majorityMul ℓ uv.2) := by
    change IsMultilinear (ML (majOne ℓ * (uv.2 : MvPolynomial (Fin ℓ) (ZMod 2))))
    exact ml_multilinear _
  exact (mem_restrictDegree (Fin ℓ) _ 1).mp ((restrictDegree (Fin ℓ) (ZMod 2) 1).add_mem
    ((mem_restrictDegree (Fin ℓ) _ 1).mpr hu) ((mem_restrictDegree (Fin ℓ) _ 1).mpr hv))

theorem pairEvaluation_injective (ℓ : ℕ) (hℓ : Odd ℓ) : Function.Injective (pairEvaluation ℓ) := by
  intro u v huv
  have hpoly : (u.1 : MvPolynomial (Fin ℓ) (ZMod 2)) + majorityMul ℓ u.2 =
      (v.1 : MvPolynomial (Fin ℓ) (ZMod 2)) + majorityMul ℓ v.2 := by
    apply multilinear_ext (pair_polynomial_multilinear ℓ u) (pair_polynomial_multilinear ℓ v)
    intro x
    exact congrFun huv x
  obtain ⟨hu1m, hu1d⟩ := (mem_light_iff _ _).mp u.1.2
  obtain ⟨hu2m, hu2d⟩ := (mem_light_iff _ _).mp u.2.2
  obtain ⟨hv1m, hv1d⟩ := (mem_light_iff _ _).mp v.1.2
  obtain ⟨hv2m, hv2d⟩ := (mem_light_iff _ _).mp v.2.2
  have heq := (unique_expansion ℓ hℓ _ (pair_polynomial_multilinear ℓ u)).unique
    (y₁ := ((u.1 : MvPolynomial (Fin ℓ) (ZMod 2)), (u.2 : MvPolynomial (Fin ℓ) (ZMod 2))))
    (y₂ := ((v.1 : MvPolynomial (Fin ℓ) (ZMod 2)), (v.2 : MvPolynomial (Fin ℓ) (ZMod 2))))
    ⟨hu1m, hu2m, hu1d, hu2d, rfl⟩ ⟨hv1m, hv2m, hv1d, hv2d, hpoly⟩
  exact Prod.ext (Subtype.ext (congrArg Prod.fst heq)) (Subtype.ext (congrArg Prod.snd heq))

theorem pairEvaluation_surjective (ℓ : ℕ) (hℓ : Odd ℓ) : Function.Surjective (pairEvaluation ℓ) := by
  intro f
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ (Fin ℓ) (ZMod 2)) f
  let p' : restrictDegree (Fin ℓ) (ZMod 2) (Fintype.card (ZMod 2) - 1) := p
  have hml : IsMultilinear p'.1 := by
    apply (mem_restrictDegree (Fin ℓ) _ 1).mp
    simpa only [ZMod.card, Nat.reduceSub] using p'.2
  obtain ⟨uv, huv, _⟩ := unique_expansion ℓ hℓ p'.1 hml
  obtain ⟨hum, hvm, hud, hvd, heq⟩ := huv
  refine ⟨(⟨uv.1, (mem_light_iff _ _).mpr ⟨hum, hud⟩⟩,
    ⟨uv.2, (mem_light_iff _ _).mpr ⟨hvm, hvd⟩⟩), ?_⟩
  ext x
  change eval x (uv.1 + majorityMul ℓ uv.2) = f x
  rw [← heq]
  exact congrFun hp x

noncomputable def pairEvaluationEquiv (ℓ : ℕ) (hℓ : Odd ℓ) :
    (LightSpace ℓ × LightSpace ℓ) ≃ₗ[ZMod 2] ((Fin ℓ → ZMod 2) → ZMod 2) :=
  LinearEquiv.ofBijective (pairEvaluation ℓ)
    ⟨pairEvaluation_injective ℓ hℓ, pairEvaluation_surjective ℓ hℓ⟩

noncomputable def blockFunctionBasis (ℓ : ℕ) (hℓ : Odd ℓ) :
    Basis (LightIndex ℓ ⊕ LightIndex ℓ) (ZMod 2) ((Fin ℓ → ZMod 2) → ZMod 2) :=
  ((lightBasis ℓ).prod (lightBasis ℓ)).map (pairEvaluationEquiv ℓ hℓ)

@[simp] theorem blockFunctionBasis_inl (ℓ : ℕ) (hℓ : Odd ℓ)
    (S : LightIndex ℓ) (x : Fin ℓ → ZMod 2) :
    blockFunctionBasis ℓ hℓ (Sum.inl S) x = eval x (xMon S.1) := by
  change eval x
    (((((lightBasis ℓ).prod (lightBasis ℓ)) (Sum.inl S)).1 : MvPolynomial (Fin ℓ) (ZMod 2)) +
      majorityMul ℓ ((((lightBasis ℓ).prod (lightBasis ℓ)) (Sum.inl S)).2)) = _
  simp only [Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd, Submodule.coe_zero,
    map_zero, add_zero, lightBasis_coe]

@[simp] theorem blockFunctionBasis_inr (ℓ : ℕ) (hℓ : Odd ℓ)
    (S : LightIndex ℓ) (x : Fin ℓ → ZMod 2) :
    blockFunctionBasis ℓ hℓ (Sum.inr S) x = eval x (majOne ℓ) * eval x (xMon S.1) := by
  change eval x
    (((((lightBasis ℓ).prod (lightBasis ℓ)) (Sum.inr S)).1 : MvPolynomial (Fin ℓ) (ZMod 2)) +
      majorityMul ℓ ((((lightBasis ℓ).prod (lightBasis ℓ)) (Sum.inr S)).2)) = _
  simp only [Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd, Submodule.coe_zero,
    zero_add, lightBasis_coe]
  change eval x (ML (majOne ℓ * xMon S.1)) = _
  rw [eval_ml, map_mul]

noncomputable def allBlockFunctionBasis (n ℓ : ℕ) (hℓ : Odd ℓ) :
    Basis (Fin n → LightIndex ℓ ⊕ LightIndex ℓ) (ZMod 2)
      ((Fin n → Fin ℓ → ZMod 2) → ZMod 2) :=
  ProofComplexity.productFunctionBasis (fun _ : Fin n => blockFunctionBasis ℓ hℓ)

theorem allBlockFunctionBasis_apply (n ℓ : ℕ) (hℓ : Odd ℓ)
    (k : Fin n → LightIndex ℓ ⊕ LightIndex ℓ) (x : Fin n → Fin ℓ → ZMod 2) :
    allBlockFunctionBasis n ℓ hℓ k x = ∏ i, blockFunctionBasis ℓ hℓ (k i) (x i) := by
  exact ProofComplexity.productFunctionBasis_apply _ _ _

end AC02Frege.MajorityFunctionBasis
end

section
-- Inlined Solutions.MajorityTensorIndex

open Module MvPolynomial AC02Frege
open AC02Frege.MajorityFunctionBasis

namespace AC02Frege.MajorityTensorIndex

def tensorSection {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ)) (i : Fin n) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun a => (i, a) ∈ A)

theorem section_image {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ)) (i : Fin n) :
    (tensorSection A i).image (fun a => (i, a)) = blockPart A i := by
  ext v
  rcases v with ⟨j, a⟩
  simp only [Finset.mem_image, tensorSection, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.mk.injEq, blockPart]
  constructor
  · rintro ⟨b, hb, hij, hba⟩
    subst j; subst b
    exact ⟨hb, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl, rfl⟩

theorem section_card {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ)) (i : Fin n) :
    (tensorSection A i).card = (blockPart A i).card := by
  rw [← section_image]
  exact (Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)).symm

abbrev GlobalLight (n ℓ : ℕ) := {A : Finset (Fin n × Fin ℓ) // A ∈ lightSets n ℓ}

def sections {n ℓ : ℕ} (A : GlobalLight n ℓ) (i : Fin n) : LightIndex ℓ :=
  ⟨tensorSection A.1 i, by
    rw [section_card]
    exact (Finset.mem_filter.mp A.2).2 i⟩

def assemble {n ℓ : ℕ} (S : Fin n → LightIndex ℓ) : Finset (Fin n × Fin ℓ) :=
  Finset.univ.filter (fun v => v.2 ∈ (S v.1).1)

@[simp] theorem section_assemble {n ℓ : ℕ} (S : Fin n → LightIndex ℓ) (i : Fin n) :
    tensorSection (assemble S) i = (S i).1 := by
  ext a
  simp [tensorSection, assemble]

@[simp] theorem assemble_sections {n ℓ : ℕ} (A : GlobalLight n ℓ) :
    assemble (sections A) = A.1 := by
  ext v
  simp [assemble, sections, tensorSection]

def lightSetEquiv (n ℓ : ℕ) : (Fin n → LightIndex ℓ) ≃ GlobalLight n ℓ where
  toFun S := ⟨assemble S, by
    simp only [lightSets, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [← section_card, section_assemble]
    exact (S i).2⟩
  invFun A := sections A
  left_inv S := by funext i; apply Subtype.ext; exact section_assemble S i
  right_inv A := Subtype.ext (assemble_sections A)

def pack {n ℓ : ℕ} (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
    Fin n → LightIndex ℓ ⊕ LightIndex ℓ :=
  fun i => if i ∈ J then Sum.inr (sections A i) else Sum.inl (sections A i)

def unpackSupports {n ℓ : ℕ} (k : Fin n → LightIndex ℓ ⊕ LightIndex ℓ) :
    Fin n → LightIndex ℓ := fun i => Sum.elim id id (k i)

def unpackHeavy {n ℓ : ℕ} (k : Fin n → LightIndex ℓ ⊕ LightIndex ℓ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (k i).isRight = true)

def tensorIndexEquiv (n ℓ : ℕ) :
    (Fin n → LightIndex ℓ ⊕ LightIndex ℓ) ≃ GlobalLight n ℓ × Finset (Fin n) where
  toFun k := (lightSetEquiv n ℓ (unpackSupports k), unpackHeavy k)
  invFun AJ := pack AJ.1 AJ.2
  left_inv k := by
    funext i
    change (if i ∈ unpackHeavy k then
      Sum.inr (sections (lightSetEquiv n ℓ (unpackSupports k)) i)
      else Sum.inl (sections (lightSetEquiv n ℓ (unpackSupports k)) i)) = k i
    have hs : sections (lightSetEquiv n ℓ (unpackSupports k)) i = unpackSupports k i := by
      exact congrFun ((lightSetEquiv n ℓ).left_inv (unpackSupports k)) i
    rw [hs]
    cases h : k i <;> simp [unpackHeavy, unpackSupports, h]
  right_inv AJ := by
    rcases AJ with ⟨A, J⟩
    have hs : unpackSupports (pack A J) = sections A := by
      funext i
      simp only [unpackSupports, pack]
      split_ifs <;> rfl
    apply Prod.ext
    · change lightSetEquiv n ℓ (unpackSupports (pack A J)) = A
      rw [hs]
      exact (lightSetEquiv n ℓ).right_inv A
    · ext i
      by_cases hi : i ∈ J <;> simp [unpackHeavy, pack, hi]

end AC02Frege.MajorityTensorIndex
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
-- Inlined Solutions.MajorityCoordinateBasis

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFunctionBasis AC02Frege.MajorityTensorIndex

namespace AC02Frege.MajorityCoordinateBasis

noncomputable def uncurryFunctions (n ℓ : ℕ) :
    ((Fin n → Fin ℓ → ZMod 2) → ZMod 2) ≃ₗ[ZMod 2]
      ((Fin n × Fin ℓ → ZMod 2) → ZMod 2) where
  toFun f x := f (fun i a => x (i, a))
  invFun f x := f (fun v => x v.1 v.2)
  left_inv f := by funext x; rfl
  right_inv f := by funext x; rfl
  map_add' f g := rfl
  map_smul' c f := rfl

noncomputable def coordinateBasis (n ℓ : ℕ) (hℓ : Odd ℓ) :
    Basis (GlobalLight n ℓ × Finset (Fin n)) (ZMod 2)
      ((Fin n × Fin ℓ → ZMod 2) → ZMod 2) :=
  ((allBlockFunctionBasis n ℓ hℓ).reindex (tensorIndexEquiv n ℓ)).map (uncurryFunctions n ℓ)

theorem xMon_eval_blocks {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ))
    (x : Fin n × Fin ℓ → ZMod 2) :
    eval x (xMon A) = ∏ i : Fin n, eval (fun a => x (i, a)) (xMon (tensorSection A i)) := by
  classical
  simp only [xMon_eval, tensorSection, Finset.prod_filter]
  rw [← Finset.prod_product']
  simp only [Finset.univ_product_univ]
  rw [← Finset.prod_filter]
  simp

theorem hBlock_eval {n ℓ : ℕ} (i : Fin n) (x : Fin n × Fin ℓ → ZMod 2) :
    eval x (hBlock i) = eval (fun a => x (i, a)) (majOne ℓ) := by
  exact eval_rename_prod_mk _ _ _

theorem coordinateBasis_apply {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ)
    (J : Finset (Fin n)) (x : Fin n × Fin ℓ → ZMod 2) :
    coordinateBasis n ℓ hℓ (A, J) x =
      eval x (xMon A.1) * ∏ i ∈ J, eval x (hBlock i) := by
  classical
  rw [coordinateBasis, Basis.map_apply, Basis.reindex_apply]
  change allBlockFunctionBasis n ℓ hℓ (pack A J) (fun i a => x (i, a)) = _
  rw [allBlockFunctionBasis_apply]
  have hf (i : Fin n) : blockFunctionBasis ℓ hℓ (pack A J i) (fun a => x (i, a)) =
      eval (fun a => x (i, a)) (xMon (tensorSection A.1 i)) *
        (if i ∈ J then eval x (hBlock i) else 1) := by
    unfold pack
    split_ifs with hi
    · rw [blockFunctionBasis_inr, hBlock_eval]
      exact mul_comm _ _
    · rw [blockFunctionBasis_inl, mul_one]
      rfl
  simp only [hf]
  rw [Finset.prod_mul_distrib, ← xMon_eval_blocks, ← Finset.prod_filter]
  simp

theorem eval_bind_majority {n ℓ : ℕ} (p : MvPolynomial (Fin n) (ZMod 2))
    (x : Fin n × Fin ℓ → ZMod 2) :
    eval x (bind₁ (fun i => hBlock (ℓ := ℓ) i) p) = eval (fun i => eval x (hBlock i)) p := by
  exact eval₂Hom_bind₁ _ _ _ _

theorem coordinateBasis_polynomial {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ)
    (J : Finset (Fin n)) (x : Fin n × Fin ℓ → ZMod 2) :
    coordinateBasis n ℓ hℓ (A, J) x =
      eval x (xMon A.1 * bind₁ (fun i => hBlock (ℓ := ℓ) i) (xMon J)) := by
  rw [map_mul, eval_bind_majority, xMon_eval J, coordinateBasis_apply]

end AC02Frege.MajorityCoordinateBasis
end

section
-- Inlined Solutions.MajorityExpansionCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoordinateBasis
open ProofComplexity.BooleanCoordinates

namespace AC02Frege.MajorityExpansionCoordinates

noncomputable def familyCoeffs {n ℓ : ℕ}
    (q : Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2)) :
    GlobalLight n ℓ × Finset (Fin n) → ZMod 2 :=
  fun AJ => monoCoeffs (q AJ.1.1) AJ.2

noncomputable def coeffFamily {n ℓ : ℕ}
    (c : GlobalLight n ℓ × Finset (Fin n) → ZMod 2) :
    Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2) :=
  fun A => if hA : A ∈ lightSets n ℓ then monoPoly (fun J => c (⟨A, hA⟩, J)) else 0

theorem coeffFamily_multilinear {n ℓ : ℕ}
    (c : GlobalLight n ℓ × Finset (Fin n) → ZMod 2) :
    ∀ A, IsMultilinear (coeffFamily c A) := by
  intro A
  unfold coeffFamily
  split_ifs
  · exact monoPoly_multilinear _
  · simpa only [map_zero] using ml_multilinear (0 : MvPolynomial (Fin n) (ZMod 2))

theorem coeffFamily_off_light {n ℓ : ℕ}
    (c : GlobalLight n ℓ × Finset (Fin n) → ZMod 2) :
    ∀ A ∉ lightSets n ℓ, coeffFamily c A = 0 := by
  intro A hA
  simp only [coeffFamily, dif_neg hA]

theorem familyCoeffs_coeffFamily {n ℓ : ℕ}
    (c : GlobalLight n ℓ × Finset (Fin n) → ZMod 2) :
    familyCoeffs (coeffFamily c) = c := by
  classical
  funext AJ
  rcases AJ with ⟨A, J⟩
  simp only [familyCoeffs, coeffFamily, dif_pos A.2, monoCoeffs_poly]

theorem coeffFamily_familyCoeffs {n ℓ : ℕ}
    (q : Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2))
    (hq : ∀ A, IsMultilinear (q A)) (hz : ∀ A ∉ lightSets n ℓ, q A = 0) :
    coeffFamily (familyCoeffs q) = q := by
  classical
  funext A
  unfold coeffFamily
  split_ifs with hA
  · change monoPoly (monoCoeffs (q A)) = q A
    rw [monoPoly_coeffs, ml_of_multilinear _ (hq A)]
  · exact (hz A hA).symm

theorem eval_as_monoCoeffs {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) (x : V → ZMod 2) :
    eval x p = ∑ S : Finset V, monoCoeffs p S * ∏ i ∈ S, x i := by
  classical
  conv_lhs => rw [monoCoeffs_sum p hp]
  simp only [map_sum, smul_eval, xMon_eval]

theorem eval_expand_as_basis {n ℓ : ℕ} (hℓ : Odd ℓ)
    (q : Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2))
    (hq : ∀ A, IsMultilinear (q A)) :
    (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (expand q)) =
      (coordinateBasis n ℓ hℓ).equivFun.symm (familyCoeffs q) := by
  classical
  rw [Basis.equivFun_symm_apply]
  funext x
  simp only [expand, eval_ml, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort (lightSets n ℓ)]
  apply Finset.sum_congr rfl
  intro A _
  rw [map_mul, eval_bind_majority, eval_as_monoCoeffs _ (hq A.1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [coordinateBasis_apply]
  change eval x (xMon A.1) * (monoCoeffs (q A.1) J * _) =
    monoCoeffs (q A.1) J * (eval x (xMon A.1) * _)
  ring

theorem majority_expansion {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : ∃! q, IsExpansion p q := by
  classical
  let b := coordinateBasis n ℓ hℓ
  let f : (Fin n × Fin ℓ → ZMod 2) → ZMod 2 := fun x => eval x p
  let c := b.equivFun f
  have heval : (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (expand (coeffFamily c))) = f := by
    rw [eval_expand_as_basis hℓ _ (coeffFamily_multilinear c), familyCoeffs_coeffFamily]
    exact b.equivFun.symm_apply_apply f
  refine ⟨coeffFamily c, ⟨coeffFamily_multilinear c, coeffFamily_off_light c, ?_⟩, ?_⟩
  · apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
    intro x
    rw [eval_ml p x]
    exact congrFun heval x
  · intro q hq
    obtain ⟨hml, hz, hexp⟩ := hq
    have hcrepr : familyCoeffs q = c := by
      apply b.equivFun.symm.injective
      rw [← eval_expand_as_basis hℓ q hml]
      change (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (expand q)) = b.equivFun.symm (b.equivFun f)
      rw [b.equivFun.symm_apply_apply]
      funext x
      rw [hexp, eval_ml]
    calc
      q = coeffFamily (familyCoeffs q) := (coeffFamily_familyCoeffs q hml hz).symm
      _ = coeffFamily c := congrArg coeffFamily hcrepr

end AC02Frege.MajorityExpansionCoordinates
end

section
-- Inlined Solutions.MajorityGrading

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis AC02Frege.MajorityFoundation
open AC02Frege.MajorityIdeal AC02Frege.MajorityBasis AC02Frege.MajorityFunctionBasis
open AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoordinateBasis

namespace AC02Frege.MajorityGrading

theorem light_block_repr_inr (ℓ : ℕ) (hℓ : Odd ℓ) (S : Finset (Fin ℓ))
    (hS : S.card ≤ ℓ / 2) (T : LightIndex ℓ) :
    (blockFunctionBasis ℓ hℓ).repr (fun x => eval x (xMon S)) (Sum.inr T) = 0 := by
  have heq : (fun x => eval x (xMon S)) = blockFunctionBasis ℓ hℓ (Sum.inl ⟨S, hS⟩) := by
    funext x
    exact (blockFunctionBasis_inl ℓ hℓ ⟨S, hS⟩ x).symm
  rw [heq, Basis.repr_self]
  simp

theorem heavy_block_repr_inl (ℓ : ℕ) (hℓ : Odd ℓ) (S : Finset (Fin ℓ))
    (hS : ℓ / 2 < S.card) (T : LightIndex ℓ) :
    (blockFunctionBasis ℓ hℓ).repr (fun x => eval x (xMon S)) (Sum.inl T) = 0 := by
  have hideal : xMon S ∈ (majorityMul ℓ).range := by
    rw [ideal_eq_heavy]
    exact Submodule.subset_span ⟨S, hS, rfl⟩
  obtain ⟨v, hvm, hvd, hveq⟩ := ideal_has_light_preimage ℓ hℓ (xMon S) hideal
  let v' : LightSpace ℓ := ⟨v, (mem_light_iff _ _).mpr ⟨hvm, hvd⟩⟩
  have heq : (fun x => eval x (xMon S)) = pairEvaluationEquiv ℓ hℓ (0, v') := by
    funext x
    change eval x (xMon S) = eval x (0 + majorityMul ℓ v)
    rw [zero_add, hveq]
  rw [heq]
  change ((lightBasis ℓ).prod (lightBasis ℓ)).repr
    ((pairEvaluationEquiv ℓ hℓ).symm ((pairEvaluationEquiv ℓ hℓ) (0, v'))) (Sum.inl T) = 0
  rw [LinearEquiv.symm_apply_apply, Basis.prod_repr_inl]
  simp

theorem block_repr_zero_wrong_flag (ℓ : ℕ) (hℓ : Odd ℓ) (S : Finset (Fin ℓ))
    (k : LightIndex ℓ ⊕ LightIndex ℓ)
    (hk : k.isRight ≠ decide (ℓ / 2 < S.card)) :
    (blockFunctionBasis ℓ hℓ).repr (fun x => eval x (xMon S)) k = 0 := by
  classical
  cases k with
  | inl T =>
    have hS : ℓ / 2 < S.card := by simpa using hk
    exact heavy_block_repr_inl ℓ hℓ S hS T
  | inr T =>
    have hS : S.card ≤ ℓ / 2 := by simpa using hk
    exact light_block_repr_inr ℓ hℓ S hS T

theorem scalar_monomial_coordinate {n ℓ : ℕ} (hℓ : Odd ℓ) (T : Finset (Fin n × Fin ℓ))
    (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
    (coordinateBasis n ℓ hℓ).repr (fun x => eval x (xMon T)) (A, J) =
      ∏ i : Fin n, (blockFunctionBasis ℓ hℓ).repr
        (fun x => eval x (xMon (tensorSection T i))) (pack A J i) := by
  have hfun : (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (xMon T)) =
      uncurryFunctions n ℓ (fun x => ∏ i : Fin n, eval (x i) (xMon (tensorSection T i))) := by
    funext x
    exact xMon_eval_blocks T x
  rw [hfun]
  change (allBlockFunctionBasis n ℓ hℓ).repr
    ((uncurryFunctions n ℓ).symm ((uncurryFunctions n ℓ) _)) ((tensorIndexEquiv n ℓ).symm (A, J)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact ProofComplexity.productFunctionBasis_repr
    (fun _ : Fin n => blockFunctionBasis ℓ hℓ)
    (fun i x => eval x (xMon (tensorSection T i))) (pack A J)

theorem scalar_monomial_zero_other_grade {n ℓ : ℕ} (hℓ : Odd ℓ)
    (T : Finset (Fin n × Fin ℓ)) (A : GlobalLight n ℓ) (J : Finset (Fin n))
    (hJ : J ≠ heavyBlocks T) :
    (coordinateBasis n ℓ hℓ).repr (fun x => eval x (xMon T)) (A, J) = 0 := by
  classical
  rw [scalar_monomial_coordinate]
  have hex : ∃ i : Fin n, (pack A J i).isRight ≠ decide (ℓ / 2 < (tensorSection T i).card) := by
    by_contra hn
    push Not at hn
    apply hJ
    ext i
    have hi := hn i
    rw [section_card] at hi
    by_cases hij : i ∈ J <;> simp [pack, hij, heavyBlocks] at hi ⊢
    · exact hi
    · exact hi
  obtain ⟨i, hi⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ i) (block_repr_zero_wrong_flag ℓ hℓ _ _ hi)

end AC02Frege.MajorityGrading
end

section
-- Inlined Solutions.BooleanCoordinateDegree

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis

namespace ProofComplexity.BooleanCoordinates

theorem indicator_injective {V : Type} :
    Function.Injective (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) := by
  intro S T h
  have hs := congrArg Finsupp.support h
  simpa only [indicator_support] using hs

theorem monoCoeffs_eq_coeff {V : Type} [Fintype V] (p : MvPolynomial V (ZMod 2))
    (S : Finset V) : monoCoeffs p S = (ML p).coeff (Finsupp.indicator S (fun _ _ => 1)) := by
  classical
  have h := congrArg (fun q : MvPolynomial V (ZMod 2) =>
    q.coeff (Finsupp.indicator S (fun _ _ => 1))) (monoPoly_coeffs p)
  rw [monoPoly_sum] at h
  simp only [coeff_sum, coeff_smul, xMon_eq_monomial, coeff_monomial,
    indicator_injective.eq_iff] at h
  simpa using h

theorem multilinear_degree_le_iff {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) (Q : ℕ) :
    p.totalDegree ≤ Q ↔ ∀ S : Finset V, monoCoeffs p S ≠ 0 → S.card ≤ Q := by
  classical
  constructor
  · intro hd S hS
    rw [monoCoeffs_eq_coeff, ml_of_multilinear _ hp] at hS
    have hs := le_totalDegree (mem_support_iff.mpr hS)
    have hsq : ∀ i, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i ≤ 1 := by
      intro i
      simp only [Finsupp.indicator_apply]
      split_ifs <;> omega
    rw [squarefree_sum _ hsq, indicator_support] at hs
    omega
  · intro hc
    conv_lhs => rw [monoCoeffs_sum p hp]
    apply totalDegree_finsetSum_le
    intro S _
    by_cases hS : monoCoeffs p S = 0
    · simp only [hS, zero_smul, totalDegree_zero, zero_le]
    · exact (totalDegree_smul_le _ _).trans (by rw [xMon_totalDegree]; exact hc S hS)

theorem monoCoeffs_zero {V : Type} [Fintype V] :
    monoCoeffs (0 : MvPolynomial V (ZMod 2)) = 0 := by
  simp [monoCoeffs]

theorem monoPoly_zero {V : Type} [Fintype V] :
    monoPoly (0 : Finset V → ZMod 2) = 0 := by
  simp [monoPoly]

theorem monoCoeffs_eq_zero_iff {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) : monoCoeffs p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have heq := congrArg monoPoly h
    simpa only [monoPoly_coeffs, ml_of_multilinear _ hp, monoPoly_zero] using heq
  · rintro rfl
    exact monoCoeffs_zero

end ProofComplexity.BooleanCoordinates
end

section
-- Inlined Solutions.MajorityGradeProjection

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoordinateBasis
open AC02Frege.MajorityExpansionCoordinates AC02Frege.MajorityGrading
open ProofComplexity.BooleanCoordinates

namespace AC02Frege.MajorityGradeProjection

noncomputable def coords {n ℓ : ℕ} (hℓ : Odd ℓ) (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    GlobalLight n ℓ × Finset (Fin n) → ZMod 2 :=
  (coordinateBasis n ℓ hℓ).equivFun (fun x => eval x p)

theorem coords_scalar_sum {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p)
    (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
    coords hℓ p (A, J) = ∑ T : Finset (Fin n × Fin ℓ), monoCoeffs p T *
      (coordinateBasis n ℓ hℓ).repr (fun x => eval x (xMon T)) (A, J) := by
  classical
  have heval : (fun x : Fin n × Fin ℓ → ZMod 2 => eval x p) =
      ∑ T : Finset (Fin n × Fin ℓ), monoCoeffs p T • (fun x => eval x (xMon T)) := by
    funext x
    conv_lhs => rw [monoCoeffs_sum p hp]
    simp only [map_sum, smul_eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold coords
  rw [heval, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Basis.equivFun_apply,
    Finsupp.coe_finsetSum, Finsupp.coe_smul]

noncomputable def gradePart {n ℓ : ℕ}
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (H : Finset (Fin n)) :
    MvPolynomial (Fin n × Fin ℓ) (ZMod 2) :=
  monoPoly (fun T => if heavyBlocks T = H then monoCoeffs p T else 0)

theorem gradePart_multilinear {n ℓ : ℕ}
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (H : Finset (Fin n)) :
    IsMultilinear (gradePart p H) := monoPoly_multilinear _

theorem gradePart_coeffs {n ℓ : ℕ}
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (H : Finset (Fin n))
    (T : Finset (Fin n × Fin ℓ)) :
    monoCoeffs (gradePart p H) T = if heavyBlocks T = H then monoCoeffs p T else 0 := by
  exact congrFun (monoCoeffs_poly _) T

theorem coords_gradePart {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p)
    (H : Finset (Fin n)) (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
    coords hℓ (gradePart p H) (A, J) = if J = H then coords hℓ p (A, J) else 0 := by
  classical
  rw [coords_scalar_sum hℓ _ (gradePart_multilinear p H)]
  simp only [gradePart_coeffs]
  by_cases hJ : J = H
  · rw [if_pos hJ, coords_scalar_sum hℓ p hp]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : heavyBlocks T = H
    · rw [if_pos hT]
    · rw [if_neg hT, zero_mul, scalar_monomial_zero_other_grade hℓ T A J (by simpa [hJ] using Ne.symm hT),
        mul_zero]
  · rw [if_neg hJ]
    apply Finset.sum_eq_zero
    intro T _
    by_cases hT : heavyBlocks T = H
    · rw [if_pos hT, scalar_monomial_zero_other_grade hℓ T A J (by simpa [hT] using hJ), mul_zero]
    · rw [if_neg hT, zero_mul]

theorem coords_zero_iff {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) :
    coords hℓ p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have he : (fun x : Fin n × Fin ℓ → ZMod 2 => eval x p) = 0 := by
      exact (coordinateBasis n ℓ hℓ).equivFun.injective (by simpa only [coords, map_zero] using h)
    apply multilinear_ext hp
      (by simpa only [map_zero] using ml_multilinear (0 : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)))
    intro x
    simpa only [map_zero, Pi.zero_apply] using congrFun he x
  · rintro rfl
    have heval : (fun x : Fin n × Fin ℓ → ZMod 2 =>
        eval x (0 : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) = 0 := by
      funext x
      exact map_zero _
    rw [coords, heval, map_zero]

theorem grading_bound_iff {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (Q : ℕ) :
    (∀ A : GlobalLight n ℓ, ∀ J : Finset (Fin n), coords hℓ p (A, J) ≠ 0 → J.card ≤ Q) ↔
      ∀ T : Finset (Fin n × Fin ℓ), monoCoeffs p T ≠ 0 → (heavyBlocks T).card ≤ Q := by
  classical
  constructor
  · intro hc T hT
    by_contra hd
    have hz : coords hℓ (gradePart p (heavyBlocks T)) = 0 := by
      funext AJ
      rcases AJ with ⟨A, J⟩
      rw [coords_gradePart hℓ p hp]
      split_ifs with hJ
      · have hzero : coords hℓ p (A, J) = 0 := by
          by_contra hne
          have := hc A J hne
          rw [hJ] at this
          exact hd this
        exact hzero
      · rfl
    have hpzero := (coords_zero_iff hℓ _ (gradePart_multilinear p _)).mp hz
    have hm := congrArg (fun q => monoCoeffs q T) hpzero
    rw [gradePart_coeffs, if_pos rfl, monoCoeffs_zero] at hm
    exact hT hm
  · intro hm A J hc
    by_contra hd
    apply hc
    rw [coords_scalar_sum hℓ p hp]
    apply Finset.sum_eq_zero
    intro T _
    by_cases hT : heavyBlocks T = J
    · have hzero : monoCoeffs p T = 0 := by
        by_contra hne
        have := hm T hne
        rw [hT] at this
        exact hd this
      rw [hzero, zero_mul]
    · rw [scalar_monomial_zero_other_grade hℓ T A J (Ne.symm hT), mul_zero]

end AC02Frege.MajorityGradeProjection
end

section
-- Inlined Solutions.MajorityCoefficientDegree

open Module MvPolynomial AC02Frege
open AC02Frege.BooleanAlgebra AC02Frege.BooleanBasis AC02Frege.MajorityTensorIndex
open AC02Frege.MajorityCoordinateBasis AC02Frege.MajorityExpansionCoordinates
open AC02Frege.MajorityGradeProjection ProofComplexity.BooleanCoordinates

namespace AC02Frege.MajorityCoefficientDegree

theorem coeffPoly_expansion {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : IsExpansion p (coeffPoly p) := by
  classical
  have he := majority_expansion hℓ p
  unfold coeffPoly
  rw [dif_pos he]
  exact he.choose_spec.1

theorem coeffPoly_coords {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    familyCoeffs (coeffPoly p) = coords hℓ p := by
  obtain ⟨hml, _, hexp⟩ := coeffPoly_expansion hℓ p
  apply (coordinateBasis n ℓ hℓ).equivFun.symm.injective
  rw [← eval_expand_as_basis hℓ _ hml]
  change (fun x : Fin n × Fin ℓ → ZMod 2 => eval x (expand (coeffPoly p))) =
    (coordinateBasis n ℓ hℓ).equivFun.symm
      ((coordinateBasis n ℓ hℓ).equivFun (fun x => eval x p))
  rw [LinearEquiv.symm_apply_apply]
  funext x
  rw [hexp, eval_ml]

theorem sup_poly_degree_le_iff {I V : Type} [Fintype V] (s : Finset I)
    (q : I → MvPolynomial V (ZMod 2)) (Q : ℕ) :
    s.sup (fun A => if q A = 0 then (⊥ : WithBot ℕ) else ((q A).totalDegree : WithBot ℕ)) ≤ (Q : WithBot ℕ) ↔
      ∀ A ∈ s, (q A).totalDegree ≤ Q := by
  classical
  rw [Finset.sup_le_iff]
  constructor
  · intro h A hA
    by_cases hz : q A = 0
    · simp only [hz, totalDegree_zero, zero_le]
    · have hd := h A hA
      rw [if_neg hz] at hd
      exact_mod_cast hd
  · intro h A hA
    by_cases hz : q A = 0
    · simp only [if_pos hz, bot_le]
    · rw [if_neg hz]
      exact_mod_cast h A hA

theorem coeffDeg_le_iff_coords {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (Q : ℕ) :
    coeffDeg p ≤ (Q : WithBot ℕ) ↔
      ∀ A : GlobalLight n ℓ, ∀ J : Finset (Fin n), coords hℓ p (A, J) ≠ 0 → J.card ≤ Q := by
  classical
  have hml := (coeffPoly_expansion hℓ p).1
  have hc (A : GlobalLight n ℓ) (J : Finset (Fin n)) :
      monoCoeffs (coeffPoly p A.1) J = coords hℓ p (A, J) :=
    congrFun (coeffPoly_coords hℓ p) (A, J)
  rw [coeffDeg, Finset.sup_le_iff]
  constructor
  · intro hd A J hJ
    have hdeg : (coeffPoly p A.1).totalDegree ≤ Q := by
      by_cases hz : coeffPoly p A.1 = 0
      · simp only [hz, totalDegree_zero, zero_le]
      · have hb := hd A.1 A.2
        rw [if_neg hz] at hb
        exact_mod_cast hb
    apply (multilinear_degree_le_iff _ (hml A.1) Q).mp hdeg J
    rw [hc]
    exact hJ
  · intro hd A hA
    by_cases hz : coeffPoly p A = 0
    · rw [if_pos hz]
      exact bot_le
    · rw [if_neg hz]
      apply WithBot.coe_le_coe.mpr
      apply (multilinear_degree_le_iff _ (hml A) Q).mpr
      intro J hJ
      exact hd ⟨A, hA⟩ J (by rwa [← hc ⟨A, hA⟩ J])

theorem scalar_coords_bound_iff {n ℓ : ℕ}
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (Q : ℕ) :
    (∀ T : Finset (Fin n × Fin ℓ), monoCoeffs p T ≠ 0 → (heavyBlocks T).card ≤ Q) ↔
      ∀ s ∈ p.support, (heavyBlocks s.support).card ≤ Q := by
  classical
  constructor
  · intro h s hs
    apply h s.support
    rw [monoCoeffs_eq_coeff, ml_of_multilinear _ hp, ← squarefree_eq_indicator s (hp s hs)]
    exact mem_support_iff.mp hs
  · intro h T hT
    rw [monoCoeffs_eq_coeff, ml_of_multilinear _ hp] at hT
    have hs := h _ (mem_support_iff.mpr hT)
    simpa only [indicator_support] using hs

theorem coeffDeg_threshold {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (Q : ℕ) :
    coeffDeg p ≤ (Q : WithBot ℕ) ↔ ∀ s ∈ p.support, (heavyBlocks s.support).card ≤ Q :=
  (coeffDeg_le_iff_coords hℓ p Q).trans
    ((grading_bound_iff hℓ p hp Q).trans (scalar_coords_bound_iff p hp Q))

theorem coeffDeg_ne_bot {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (hne : p ≠ 0) :
    coeffDeg p ≠ ⊥ := by
  classical
  have hcne : coords hℓ p ≠ 0 := by
    intro hz
    exact hne ((coords_zero_iff hℓ p hp).mp hz)
  obtain ⟨⟨A, J⟩, hAJ⟩ := Function.ne_iff.mp hcne
  have hqne : coeffPoly p A.1 ≠ 0 := by
    intro hz
    have hc := congrFun (coeffPoly_coords hℓ p) (A, J)
    change monoCoeffs (coeffPoly p A.1) J = coords hℓ p (A, J) at hc
    rw [hz, monoCoeffs_zero] at hc
    exact hAJ hc.symm
  have hle := Finset.le_sup (s := lightSets n ℓ)
    (f := fun A => if coeffPoly p A = 0 then (⊥ : WithBot ℕ) else (coeffPoly p A).totalDegree) A.2
  rw [if_neg hqne] at hle
  intro hbot
  change ((coeffPoly p A.1).totalDegree : WithBot ℕ) ≤ coeffDeg p at hle
  rw [hbot] at hle
  simpa using hle

theorem coeffDeg_scalar {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : IsMultilinear p) (hne : p ≠ 0) :
    coeffDeg p = ((p.support.sup (fun s => (heavyBlocks s.support).card) : ℕ) : WithBot ℕ) := by
  classical
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (coeffDeg_ne_bot hℓ p hp hne)
  have hupper : coeffDeg p ≤
      ((p.support.sup (fun s => (heavyBlocks s.support).card) : ℕ) : WithBot ℕ) :=
    (coeffDeg_threshold hℓ p hp _).mpr (fun s hs => Finset.le_sup (f := fun s => (heavyBlocks s.support).card) hs)
  have hdu : d ≤ p.support.sup (fun s => (heavyBlocks s.support).card) := by
    rw [← hd] at hupper
    exact WithBot.coe_le_coe.mp hupper
  have hlower : p.support.sup (fun s => (heavyBlocks s.support).card) ≤ d := by
    apply Finset.sup_le
    exact (coeffDeg_threshold hℓ p hp d).mp (by rw [← hd]; exact le_rfl)
  rw [← hd, Nat.le_antisymm hdu hlower]
  rfl

end AC02Frege.MajorityCoefficientDegree
end

section
-- Inlined Solutions.MajorityFibreModel

open Module MvPolynomial AC02Frege SemAC02
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation AC02Frege.MajorityTensorIndex
open AC02Frege.MajorityCoordinateBasis AC02Frege.MajorityCoefficientDegree

namespace AC02Frege.MajorityFibreModel

def ones {ℓ : ℕ} (X : Fin ℓ → Bool) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun i => X i = true)

def minorityZero (ℓ : ℕ) : (Fin ℓ → Bool) → Bool :=
  fun X => decide ((ones X).card ≤ ℓ / 2)

theorem minorityZero_antitone (ℓ : ℕ) : Antitone (minorityZero ℓ) := by
  intro X Y hXY
  apply Bool.le_iff_imp.mpr
  intro hY
  simp only [minorityZero, decide_eq_true_eq] at hY ⊢
  have hsub : ones X ⊆ ones Y := by
    intro i hi
    simp only [ones, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hle := hXY i
    rw [hi] at hle
    exact Bool.eq_true_of_true_le hle
  exact (Finset.card_le_card hsub).trans hY

theorem ones_indicator (ℓ : ℕ) (S : Finset (Fin ℓ)) : ones (indicatorVec S) = S := by
  ext i
  simp [ones, indicatorVec]

theorem minorityZero_indicator (ℓ : ℕ) (S : Finset (Fin ℓ)) :
    minorityZero ℓ (indicatorVec S) = true ↔ S.card ≤ ℓ / 2 := by
  simp only [minorityZero, ones_indicator, decide_eq_true_eq]

theorem ones_not_card (ℓ : ℕ) (X : Fin ℓ → Bool) :
    (ones (fun i => !X i)).card + (ones X).card = ℓ := by
  have heq : ones (fun i => !X i) = (ones X)ᶜ := by
    ext i
    cases h : X i <;> simp [ones, h]
  rw [heq, Finset.card_compl]
  have hc := Finset.card_le_univ (ones X)
  simp only [Fintype.card_fin] at *
  omega

theorem fibre_hBlock {n ℓ : ℕ} (hℓ : Odd ℓ) (z : Fin n → Bool)
    (X : Fin n × Fin ℓ → Bool) (hX : InFiber (minorityZero ℓ) z X) (i : Fin n) :
    eval (toF2 X) (hBlock i) = toF2 z i := by
  have hXi := hX i
  have hcard : Finset.univ.filter (fun j => toF2 X (i, j) = 1) = ones (fun j => X (i, j)) := by
    ext j
    cases h : X (i, j) <;> simp [toF2, ones, h]
  rw [hBlock_eval, majOne_eval]
  change (if ℓ / 2 < (Finset.univ.filter (fun j => toF2 X (i, j) = 1)).card then 1 else 0) = toF2 z i
  rw [hcard]
  cases hz : z i
  · simp only [InFiber, hz, Bool.false_eq_true, ↓reduceIte, minorityZero, decide_eq_true_eq] at hXi
    rw [if_neg (by omega)]
    simp [toF2, hz]
  · simp only [InFiber, hz, ↓reduceIte, minorityZero, decide_eq_true_eq] at hXi
    have hc := ones_not_card ℓ (fun j => X (i, j))
    have hh : ℓ / 2 < (ones (fun j => X (i, j))).card := by
      rcases hℓ with ⟨k, hk⟩
      omega
    rw [if_pos hh]
    simp [toF2, hz]

theorem lnSupport_iff_light {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ)) :
    IsLnSupport (minorityZero ℓ) A ↔ A ∈ lightSets n ℓ := by
  simp only [IsLnSupport, minorityZero_indicator, lightSets, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro i
  change (tensorSection A i).card ≤ ℓ / 2 ↔ (blockPart A i).card ≤ ℓ / 2
  rw [section_card]

def globalIndexEquiv (n ℓ : ℕ) :
    SemAC02.FibreBasis.GlobalIndex (minorityZero ℓ) n ≃ GlobalLight n ℓ where
  toFun A := ⟨A.1, (lnSupport_iff_light A.1).mp A.2⟩
  invFun A := ⟨A.1, (lnSupport_iff_light A.1).mpr A.2⟩
  left_inv A := rfl
  right_inv A := rfl

theorem toF2_surjective {V : Type} : Function.Surjective (toF2 (V := V)) := by
  intro x
  refine ⟨fun i => decide (x i = 1), ?_⟩
  funext i
  rcases eq_zero_or_one (x i) with hi | hi <;> simp [toF2, hi]

theorem multilinear_ext_bool {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (he : ∀ X : V → Bool, eval (toF2 X) p = eval (toF2 X) q) : p = q := by
  apply multilinear_ext hp hq
  intro x
  obtain ⟨X, rfl⟩ := toF2_surjective x
  exact he X

end AC02Frege.MajorityFibreModel
end

section
-- Inlined Solutions.MajorityCoefficientFibres

open Module MvPolynomial AC02Frege SemAC02
open AC02Frege.BooleanAlgebra AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoordinateBasis
open AC02Frege.MajorityExpansionCoordinates AC02Frege.MajorityCoefficientDegree
open AC02Frege.MajorityFibreModel

namespace AC02Frege.MajorityCoefficientFibres

theorem subst_on_fibre {n ℓ : ℕ} (hℓ : Odd ℓ) (z : Fin n → Bool)
    (X : Fin n × Fin ℓ → Bool) (hX : InFiber (minorityZero ℓ) z X)
    (q : MvPolynomial (Fin n) (ZMod 2)) :
    eval (toF2 X) (bind₁ (fun i => hBlock (ℓ := ℓ) i) q) = eval (toF2 z) q := by
  rw [eval_bind_majority]
  have heq : (fun i => eval (toF2 X) (hBlock (ℓ := ℓ) i)) = toF2 z := by
    funext i
    exact fibre_hBlock hℓ z X hX i
  rw [heq]

theorem coefficient_on_fibre {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (S : SemAC02.FibreBasis.GlobalIndex (minorityZero ℓ) n) (z : Fin n → Bool) :
    SemAC02.FibreCoordinates.coordinates (minorityZero ℓ) (minorityZero_antitone ℓ) p S z =
      eval (toF2 z) (coeffPoly p S.1) := by
  classical
  have hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin ℓ → Bool), InFiber (minorityZero ℓ) z X →
      eval (toF2 X) p = ∑ S : SemAC02.FibreBasis.GlobalIndex (minorityZero ℓ) n,
        eval (toF2 z) (coeffPoly p S.1) * eval (toF2 X) (xMon S.1) := by
    intro z X hX
    have he := congrArg (eval (toF2 X)) (coeffPoly_expansion hℓ p).2.2
    change eval (toF2 X) (ML (∑ A ∈ lightSets n ℓ,
      xMon A * bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p A))) = eval (toF2 X) (ML p) at he
    rw [eval_ml, eval_ml, map_sum] at he
    simp only [map_mul, subst_on_fibre hℓ z X hX] at he
    have hsum : (∑ A ∈ lightSets n ℓ, eval (toF2 X) (xMon A) * eval (toF2 z) (coeffPoly p A)) =
        ∑ S : SemAC02.FibreBasis.GlobalIndex (minorityZero ℓ) n,
          eval (toF2 z) (coeffPoly p S.1) * eval (toF2 X) (xMon S.1) := by
      rw [← Finset.sum_coe_sort (lightSets n ℓ)]
      rw [← (globalIndexEquiv n ℓ).sum_comp
        (fun A : GlobalLight n ℓ => eval (toF2 X) (xMon A.1) * eval (toF2 z) (coeffPoly p A.1))]
      apply Finset.sum_congr rfl
      intro A _
      exact mul_comm _ _
    exact he.symm.trans hsum
  exact (SemAC02.FibreCoordinates.coordinates_unique (minorityZero ℓ) (minorityZero_antitone ℓ)
    p (fun S z => eval (toF2 z) (coeffPoly p S.1)) hc S z).symm

theorem coeffPoly_congr {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hpq : ML p = ML q) :
    coeffPoly p = coeffPoly q := by
  have hq := coeffPoly_expansion hℓ q
  have hq' : IsExpansion p (coeffPoly q) := ⟨hq.1, hq.2.1, hq.2.2.trans hpq.symm⟩
  exact (majority_expansion hℓ p).unique (coeffPoly_expansion hℓ p) hq'

theorem light_product_degree {n ℓ : ℕ} (hℓ : Odd ℓ)
    (B A : GlobalLight n ℓ) (v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    (coeffPoly (xMon B.1 * v) A.1).totalDegree ≤ v.totalDegree := by
  let g := minorityZero ℓ
  let hg := minorityZero_antitone ℓ
  let S := (globalIndexEquiv n ℓ).symm A
  have hf : xMon B.1 ∈ lnSpan g n := Submodule.subset_span
    ⟨B.1, (lnSupport_iff_light B.1).mpr B.2, rfl⟩
  have hc := SemAC02.CoefficientControl.coefficient_degree g hg (xMon B.1) hf v S
  obtain ⟨r, hr, he⟩ := (SemAC02.CoordinateSpaces.mem_degreeSpace _).mp hc
  have heq : ML r = coeffPoly (xMon B.1 * v) A.1 := by
    apply multilinear_ext_bool _ _ (ml_multilinear _) ((coeffPoly_expansion hℓ _).1 A.1)
    intro z
    rw [eval_ml]
    exact (he z).trans (coefficient_on_fibre hℓ (xMon B.1 * v) S z)
  rw [← heq]
  exact (AC02Frege.BooleanFlip.ml_totalDegree_le r).trans hr

theorem light_product_blocks {n ℓ : ℕ} (hℓ : Odd ℓ)
    (B A : GlobalLight n ℓ) (v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    (coeffPoly (xMon B.1 * v) A.1).totalDegree ≤ (v.vars.image Prod.fst).card := by
  classical
  let g := minorityZero ℓ
  let hg := minorityZero_antitone ℓ
  let S := (globalIndexEquiv n ℓ).symm A
  have hf : xMon B.1 ∈ lnSpan g n := Submodule.subset_span
    ⟨B.1, (lnSupport_iff_light B.1).mpr B.2, rfl⟩
  have hc := SemAC02.CoefficientControl.coefficient_locality g hg (xMon B.1) hf v
    (v.vars.image Prod.fst) (fun w hw => Finset.mem_image.mpr ⟨w, hw, rfl⟩) S
  obtain ⟨r, hr, he⟩ := SemAC02.BooleanLocality.represents_local_function (v.vars.image Prod.fst)
    (SemAC02.CoordinateSpaces.coordinateMap g hg S (xMon B.1 * v)) hc
  have heq : ML r = coeffPoly (xMon B.1 * v) A.1 := by
    apply multilinear_ext_bool _ _ (ml_multilinear _) ((coeffPoly_expansion hℓ _).1 A.1)
    intro z
    rw [eval_ml]
    exact (he z).trans (coefficient_on_fibre hℓ (xMon B.1 * v) S z)
  rw [← heq]
  exact (AC02Frege.BooleanFlip.ml_totalDegree_le r).trans hr

theorem light_product_function_bounds {n ℓ : ℕ} (hℓ : Odd ℓ)
    (B A : GlobalLight n ℓ) (v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    (coeffPoly (xMon B.1 * v) A.1).totalDegree ≤ (ML v).totalDegree ∧
      (coeffPoly (xMon B.1 * v) A.1).totalDegree ≤ blocksOf v := by
  have he := congrFun (coeffPoly_congr hℓ (xMon B.1 * ML v) (xMon B.1 * v)
    (ml_mul_right _ _)) A.1
  rw [← he]
  exact ⟨light_product_degree hℓ B A (ML v), light_product_blocks hℓ B A (ML v)⟩

end AC02Frege.MajorityCoefficientFibres
end

section
-- Inlined Solutions.MajorityCoefficientAlgebra

open Module MvPolynomial AC02Frege SemAC02
open AC02Frege.BooleanAlgebra AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoefficientDegree
open AC02Frege.MajorityFibreModel AC02Frege.MajorityCoefficientFibres

namespace AC02Frege.MajorityCoefficientAlgebra

theorem multilinear_add {V : Type} (p q : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) (hq : IsMultilinear q) : IsMultilinear (p + q) :=
  (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).add_mem
    ((mem_restrictDegree V _ 1).mpr hp) ((mem_restrictDegree V _ 1).mpr hq))

theorem multilinear_smul {V : Type} (a : ZMod 2) (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : IsMultilinear (a • p) :=
  (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).smul_mem a
    ((mem_restrictDegree V _ 1).mpr hp))

theorem coefficient_characterization {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (A : GlobalLight n ℓ)
    (r : MvPolynomial (Fin n) (ZMod 2)) (hr : IsMultilinear r)
    (he : ∀ z : Fin n → Bool, SemAC02.FibreCoordinates.coordinates (minorityZero ℓ)
      (minorityZero_antitone ℓ) p ((globalIndexEquiv n ℓ).symm A) z = eval (toF2 z) r) :
    coeffPoly p A.1 = r := by
  apply multilinear_ext_bool _ _ ((coeffPoly_expansion hℓ p).1 A.1) hr
  intro z
  exact (coefficient_on_fibre hℓ p ((globalIndexEquiv n ℓ).symm A) z).symm.trans (he z)

noncomputable def coefficientMap {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ) :
    MvPolynomial (Fin n × Fin ℓ) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) where
  toFun p := coeffPoly p A.1
  map_add' p q := by
    apply coefficient_characterization hℓ _ A _
      (multilinear_add _ _ ((coeffPoly_expansion hℓ p).1 A.1) ((coeffPoly_expansion hℓ q).1 A.1))
    intro z
    rw [SemAC02.FibreCoordinates.coordinates_add, map_add]
    exact congrArg₂ (· + ·)
      (coefficient_on_fibre hℓ p ((globalIndexEquiv n ℓ).symm A) z)
      (coefficient_on_fibre hℓ q ((globalIndexEquiv n ℓ).symm A) z)
  map_smul' a p := by
    change coeffPoly (a • p) A.1 = a • coeffPoly p A.1
    apply coefficient_characterization hℓ _ A _
      (multilinear_smul a _ ((coeffPoly_expansion hℓ p).1 A.1))
    intro z
    rw [SemAC02.FibreCoordinates.coordinates_smul, smul_eval]
    exact congrArg (fun x => a * x)
      (coefficient_on_fibre hℓ p ((globalIndexEquiv n ℓ).symm A) z)

theorem coefficientMap_mul_base {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ)
    (q : MvPolynomial (Fin n) (ZMod 2)) (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    coefficientMap hℓ A (bind₁ (fun i => hBlock (ℓ := ℓ) i) q * p) =
      ML (q * coefficientMap hℓ A p) := by
  apply coefficient_characterization hℓ _ A _ (ml_multilinear _)
  intro z
  let S := (globalIndexEquiv n ℓ).symm A
  have he : (fun X : SemAC02.FibreBasis.Fibre (minorityZero ℓ) z =>
      eval (toF2 X.1) (bind₁ (fun i => hBlock (ℓ := ℓ) i) q * p)) =
      eval (toF2 z) q • (fun X : SemAC02.FibreBasis.Fibre (minorityZero ℓ) z => eval (toF2 X.1) p) := by
    funext X
    rw [map_mul, subst_on_fibre hℓ z X.1 X.2]
    rfl
  have hc : SemAC02.FibreCoordinates.coordinates (minorityZero ℓ) (minorityZero_antitone ℓ)
      (bind₁ (fun i => hBlock (ℓ := ℓ) i) q * p) S z =
      eval (toF2 z) q * SemAC02.FibreCoordinates.coordinates (minorityZero ℓ)
        (minorityZero_antitone ℓ) p S z := by
    unfold SemAC02.FibreCoordinates.coordinates
    rw [he, map_smul]
    rfl
  rw [hc, eval_ml, map_mul, coefficient_on_fibre hℓ p S z]
  rfl

theorem coefficientMap_product {n ℓ : ℕ} (hℓ : Odd ℓ) (A : GlobalLight n ℓ)
    (p v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    coefficientMap hℓ A (p * v) = ∑ B ∈ lightSets n ℓ,
      ML (coeffPoly p B * coefficientMap hℓ A (xMon B * v)) := by
  classical
  let P := ∑ B ∈ lightSets n ℓ,
    xMon B * bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p B)
  have hp : ML P = ML p := (coeffPoly_expansion hℓ p).2.2
  have hmul : ML (P * v) = ML (p * v) := by
    calc
      ML (P * v) = ML (ML P * v) := (ml_mul_left P v).symm
      _ = ML (ML p * v) := by rw [hp]
      _ = ML (p * v) := ml_mul_left p v
  have hmap : coefficientMap hℓ A (P * v) = coefficientMap hℓ A (p * v) :=
    congrFun (coeffPoly_congr hℓ _ _ hmul) A.1
  rw [← hmap]
  change coefficientMap hℓ A ((∑ B ∈ lightSets n ℓ,
    xMon B * bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p B)) * v) = _
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro B _
  have he : (xMon B * bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p B)) * v =
      bind₁ (fun i => hBlock (ℓ := ℓ) i) (coeffPoly p B) * (xMon B * v) := by ring
  rw [he, coefficientMap_mul_base]

end AC02Frege.MajorityCoefficientAlgebra
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
-- Inlined Solutions.PCMultiplication

open MvPolynomial
open AC02Frege AC02Frege.Support

theorem pc_polynomial_mul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : PCDerivable F D u)
    (hdeg : u.totalDegree + v.totalDegree ≤ D) : PCDerivable F D (u * v) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    simpa only [mul_comm u (C c), ← smul_eq_C_mul] using pc_smul F D hu c
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
    rw [mul_add]
    exact pc_add F D (ihm (by omega)) (ihp (by omega))
  | mul_X p i ih =>
    by_cases hp : p = 0
    · simp only [hp, zero_mul, mul_zero]; exact pc_zero F D
    have hdp : (p * X i).totalDegree = p.totalDegree + 1 := by
      rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
    have hbound : u.totalDegree + p.totalDegree + 1 ≤ D := by omega
    have hmul : (u * p).totalDegree + 1 ≤ D := by
      have := totalDegree_mul u p
      omega
    simpa only [mul_assoc] using pc_mul_X F D (ih (by omega)) i hmul
end

section
-- Inlined Solutions.PCMultilinearization

open MvPolynomial AC02Frege AC02Frege.Support

private theorem ml_monomial_formula {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl, h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

private theorem monomial_reduction {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (s : Fin n →₀ ℕ) (c : ZMod 2) (hdeg : s.sum (fun _ e => e) ≤ D) :
    PCDerivable F D (monomial s c + monomial (sqfree s) c) := by
  classical
  induction hs : s.sum (fun _ e => e) using Nat.strong_induction_on generalizing s with
  | h k ih =>
    by_cases hsq : ∀ i, s i ≤ 1
    · have heq : sqfree s = s := by
        ext i
        simp only [sqfree, Finsupp.mapRange_apply, min_eq_left (hsq i)]
      rw [heq, CharTwo.add_self_eq_zero]
      exact pc_zero F D
    obtain ⟨i, hi⟩ := not_forall.mp hsq
    have hi2 : 2 ≤ s i := by omega
    let r : Fin n →₀ ℕ := s - Finsupp.single i 2
    have hle : Finsupp.single i 2 ≤ s := by
      intro j
      by_cases hj : j = i
      · subst j; simpa using hi2
      · simp [Finsupp.single_apply, hj]
    have heq : r + Finsupp.single i 2 = s := tsub_add_cancel_of_le hle
    let t : Fin n →₀ ℕ := r + Finsupp.single i 1
    have hsum : r.sum (fun _ e => e) + 2 = s.sum (fun _ e => e) := by
      have h := congrArg (fun z : Fin n →₀ ℕ => z.sum (fun _ e => e)) heq
      simpa [Finsupp.sum_add_index'] using h
    have htsum : t.sum (fun _ e => e) = r.sum (fun _ e => e) + 1 := by
      simp [t, Finsupp.sum_add_index']
    have hsqeq : sqfree t = sqfree s := by
      rw [← heq]
      ext j
      by_cases hj : j = i
      · subst j
        simp only [sqfree, Finsupp.mapRange_apply, t, Finsupp.add_apply,
          Finsupp.single_eq_same]
        omega
      · simp [sqfree, Finsupp.mapRange_apply, t, Finsupp.single_apply, hj]
    have hBdeg : (X i ^ 2 + X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤ 2 := by
      have h := totalDegree_add (X i ^ 2 : MvPolynomial (Fin n) (ZMod 2)) (X i)
      simpa only [totalDegree_X_pow, totalDegree_X, max_eq_left (by omega : 1 ≤ 2)] using h
    have hB : PCDerivable F D (X i ^ 2 + X i) :=
      pc_axiom F D _ (Or.inr ⟨i, rfl⟩) (by omega)
    have hstep : PCDerivable F D (monomial s c + monomial t c) := by
      have hprod := pc_polynomial_mul F D (X i ^ 2 + X i) (monomial r c) hB
        (by
          have hrdeg : (monomial r c : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤
              r.sum (fun _ e => e) := totalDegree_monomial_le r c
          omega)
      have hfactor : monomial s c + monomial t c =
          monomial r c * (X i ^ 2 + X i) := by
        calc
          monomial s c + monomial t c =
            monomial (r + Finsupp.single i 2) c +
              monomial (r + Finsupp.single i 1) c := by rw [heq]
          _ = monomial r c * (X i ^ 2 + X i) := by
            simp only [monomial_add_single, pow_one, mul_add]
      rw [hfactor]
      simpa only [mul_comm] using hprod
    have htdeg : t.sum (fun _ e => e) ≤ D := by omega
    have htlt : t.sum (fun _ e => e) < k := by omega
    have hrec := ih _ htlt t htdeg rfl
    have hresult := pc_add F D hstep hrec
    simpa only [hsqeq, add_assoc, CharTwo.add_cancel_left] using hresult

theorem pc_multilinearization {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : PCDerivable F D p) :
    PCDerivable F D (ML p) := by
  classical
  have hdiff : PCDerivable F D (p + ML p) := by
    have hmono : ∀ s ∈ p.support,
        PCDerivable F D (monomial s (coeff s p) + monomial (sqfree s) (coeff s p)) := by
      intro s hs
      exact monomial_reduction F D s (coeff s p) ((le_totalDegree hs).trans (pc_degree hp))
    have hsum : ∀ (S : Finset (Fin n →₀ ℕ)), S ⊆ p.support →
        PCDerivable F D (∑ s ∈ S,
          (monomial s (coeff s p) + monomial (sqfree s) (coeff s p))) := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; simpa using pc_zero F D
      | @insert s S hs ih =>
        intro hsub
        rw [Finset.sum_insert hs]
        exact pc_add F D (hmono s (hsub (by simp)))
          (ih (fun a ha => hsub (by simp [ha])))
    have h := hsum p.support (fun _ h => h)
    have heq : p + ML p = ∑ s ∈ p.support,
        (monomial s (coeff s p) + monomial (sqfree s) (coeff s p)) := by
      rw [Finset.sum_add_distrib, support_sum_monomial_coeff]
      congr 1
      conv_lhs => rw [p.as_sum]
      simp only [map_sum, ml_monomial_formula]
    rw [heq]
    exact h
  have h := pc_add F D hp hdiff
  simpa only [CharTwo.add_cancel_left] using h
end

section
-- Inlined Solutions.MajorityMultiplication

open Module MvPolynomial AC02Frege LiftSAParity
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip AC02Frege.Support
open AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoefficientDegree
open AC02Frege.MajorityCoefficientFibres AC02Frege.MajorityCoefficientAlgebra

namespace AC02Frege.MajorityMultiplication

theorem coeffDeg_bot_iff {n ℓ : ℕ} (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    coeffDeg p = ⊥ ↔ ∀ A ∈ lightSets n ℓ, coeffPoly p A = 0 := by
  classical
  constructor
  · intro hp A hA
    by_contra hne
    have hle := Finset.le_sup (s := lightSets n ℓ)
      (f := fun A => if coeffPoly p A = 0 then (⊥ : WithBot ℕ) else (coeffPoly p A).totalDegree) hA
    rw [if_neg hne] at hle
    change ((coeffPoly p A).totalDegree : WithBot ℕ) ≤ coeffDeg p at hle
    rw [hp] at hle
    exact WithBot.not_coe_le_bot _ hle
  · intro hp
    apply le_antisymm
    · unfold coeffDeg
      apply Finset.sup_le
      intro A hA
      rw [if_pos (hp A hA)]
    · exact bot_le

theorem coefficient_degree_le_beta {n ℓ : ℕ} (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (b : ℕ) (hp : coeffDeg p ≤ (b : WithBot ℕ)) (A : GlobalLight n ℓ) :
    (coeffPoly p A.1).totalDegree ≤ b := by
  classical
  by_cases hz : coeffPoly p A.1 = 0
  · simp only [hz, totalDegree_zero, zero_le]
  · have hle := Finset.le_sup (s := lightSets n ℓ)
      (f := fun A => if coeffPoly p A = 0 then (⊥ : WithBot ℕ) else (coeffPoly p A).totalDegree) A.2
    rw [if_neg hz] at hle
    have hh := hle.trans hp
    exact_mod_cast hh

theorem beta_le_of_coefficient_degree {n ℓ : ℕ} (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (b : ℕ) (hp : ∀ A : GlobalLight n ℓ, (coeffPoly p A.1).totalDegree ≤ b) :
    coeffDeg p ≤ (b : WithBot ℕ) := by
  classical
  unfold coeffDeg
  apply Finset.sup_le
  intro A hA
  split_ifs
  · exact bot_le
  · exact WithBot.coe_le_coe.mpr (hp ⟨A, hA⟩)

noncomputable def consequenceSpace {n : ℕ} (F : CNF (Fin n)) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := CD F D
  zero_mem' := ⟨by simpa only [map_zero] using ml_multilinear (0 : MvPolynomial (Fin n) (ZMod 2)),
    pc_zero F D⟩
  add_mem' := by
    intro p q hp hq
    exact ⟨multilinear_add p q hp.1 hq.1, pc_add F D hp.2 hq.2⟩
  smul_mem' := by
    intro a p hp
    exact ⟨multilinear_smul a p hp.1, pc_smul F D hp.2 a⟩

theorem consequence_mul {n : ℕ} (F : CNF (Fin n)) (D : ℕ)
    (p q : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ CD F D)
    (hd : p.totalDegree + q.totalDegree ≤ D) : ML (p * q) ∈ CD F D :=
  ⟨ml_multilinear _, pc_multilinearization F D (p * q) (pc_polynomial_mul F D p q hp.2 hd)⟩

theorem product_zero_coefficients {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : coeffDeg p = ⊥) :
    ∀ A : GlobalLight n ℓ, coefficientMap hℓ A (p * v) = 0 := by
  classical
  intro A
  rw [coefficientMap_product]
  apply Finset.sum_eq_zero
  intro B hB
  rw [(coeffDeg_bot_iff p).mp hp B hB, zero_mul, map_zero]

theorem multiplication_estimate {n ℓ : ℕ} (hℓ : Odd ℓ)
    (v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (d : ℕ)
    (hv : ∀ B A : GlobalLight n ℓ, (coefficientMap hℓ A (xMon B.1 * v)).totalDegree ≤ d) :
    ∀ p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2), coeffDeg (p * v) ≤ coeffDeg p + (d : WithBot ℕ) := by
  classical
  intro p
  by_cases hp : coeffDeg p = ⊥
  · have hz : coeffDeg (p * v) = ⊥ := (coeffDeg_bot_iff _).mpr
      (fun A hA => product_zero_coefficients hℓ p v hp ⟨A, hA⟩)
    rw [hz, hp]
    exact bot_le
  · obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hp
    have hbound : coeffDeg (p * v) ≤ ((b + d : ℕ) : WithBot ℕ) := by
      apply beta_le_of_coefficient_degree
      intro A
      change (coefficientMap hℓ A (p * v)).totalDegree ≤ b + d
      rw [coefficientMap_product]
      apply totalDegree_finsetSum_le
      intro B hB
      apply (ml_totalDegree_le _).trans
      apply (totalDegree_mul _ _).trans
      exact Nat.add_le_add (coefficient_degree_le_beta p b (by rw [← hb]; exact le_rfl) ⟨B, hB⟩)
        (hv ⟨B, hB⟩ A)
    rw [← hb]
    exact_mod_cast hbound

theorem multiplication_preserves {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ)
    (v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (d : ℕ)
    (hv : ∀ B A : GlobalLight n ℓ, (coefficientMap hℓ A (xMon B.1 * v)).totalDegree ≤ d)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : p ∈ CHat F ℓ D)
    (hd : coeffDeg p + (d : WithBot ℕ) ≤ (D : WithBot ℕ)) : p * v ∈ CHat F ℓ D := by
  classical
  intro A hA
  change coefficientMap hℓ ⟨A, hA⟩ (p * v) ∈ CD F D
  by_cases hz : coeffDeg p = ⊥
  · rw [product_zero_coefficients hℓ p v hz ⟨A, hA⟩]
    exact (consequenceSpace F D).zero_mem
  · obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hz
    have hbd : b + d ≤ D := by
      rw [← hb] at hd
      have hc : ((b + d : ℕ) : WithBot ℕ) = (b : WithBot ℕ) + (d : WithBot ℕ) := WithBot.coe_add b d
      exact WithBot.coe_le_coe.mp (hc.trans_le hd)
    rw [coefficientMap_product]
    apply (consequenceSpace F D).sum_mem
    intro B hB
    apply consequence_mul F D _ _ (hp B hB)
    have hpb := coefficient_degree_le_beta p b (by rw [← hb]; exact le_rfl) ⟨B, hB⟩
    exact (Nat.add_le_add hpb (hv ⟨B, hB⟩ ⟨A, hA⟩)).trans hbd

end AC02Frege.MajorityMultiplication
end

section
-- Inlined Solutions.MajorityFunctionCongruence

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.MajorityFunctionCongruence

open MvPolynomial LiftSAParity MajorityCoefficientDegree MajorityCoefficientFibres
open MajorityCoefficientAlgebra MajorityTensorIndex

lemma coeffPoly_congr {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (h : ML p = ML q) : coeffPoly p = coeffPoly q := by
  have hq := coeffPoly_expansion hℓ q
  have hqp : IsExpansion p (coeffPoly q) := ⟨hq.1,hq.2.1,hq.2.2.trans h.symm⟩
  exact (MajorityExpansionCoordinates.majority_expansion hℓ p).unique (coeffPoly_expansion hℓ p) hqp

lemma chat_congr {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (h : ML p = ML q) :
    p ∈ CHat F ℓ D ↔ q ∈ CHat F ℓ D := by
  simp only [CHat,Set.mem_setOf_eq,coeffPoly_congr hℓ p q h]

lemma beta_congr {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (h : ML p = ML q) : coeffDeg p = coeffDeg q := by
  simp only [coeffDeg,coeffPoly_congr hℓ p q h]

@[simp] lemma beta_ml {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : coeffDeg (ML p) = coeffDeg p :=
  beta_congr hℓ _ _ (BooleanAlgebra.ml_idempotent p)

lemma degree_estimate {n ℓ : ℕ} (hℓ : Odd ℓ)
    (p v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    coeffDeg (p*v) ≤ coeffDeg p+((ML v).totalDegree : WithBot ℕ) :=
  MajorityMultiplication.multiplication_estimate hℓ v (ML v).totalDegree
    (fun B A => (light_product_function_bounds hℓ B A v).1) p

lemma degree_preserves {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (p v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : p ∈ CHat F ℓ D)
    (hd : coeffDeg p+((ML v).totalDegree : WithBot ℕ) ≤ (D : WithBot ℕ)) :
    p*v ∈ CHat F ℓ D :=
  MajorityMultiplication.multiplication_preserves hℓ F D v (ML v).totalDegree
    (fun B A => (light_product_function_bounds hℓ B A v).1) p hp hd

end AC02Frege.MajorityFunctionCongruence
end

section
-- Inlined Solutions.LinearSubspaceDimension

namespace ProofComplexity.LinearSubspaceDimension

open Module

theorem map_add_inter_ker {K M N : Type} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (B : Submodule K M) [Module.Finite K B]
    (T : M →ₗ[K] N) :
    finrank K (B.map T)+finrank K ↥(B ⊓ T.ker) = finrank K B := by
  let f := T.domRestrict B
  have hker : f.ker.map B.subtype = B ⊓ T.ker := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.2,hy⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  have hkdim : finrank K f.ker = finrank K ↥(B ⊓ T.ker) := by
    rw [← hker,Submodule.finrank_map_subtype_eq]
  have hrange : f.range = B.map T := LinearMap.range_domRestrict B T
  have h := f.finrank_range_add_finrank_ker
  rw [hrange,hkdim] at h
  exact h

/-- Restricting a subspace loses at most the ambient codimension of the restriction. -/
theorem intersection_loss {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (B : Submodule K M) [Module.Finite K B] (A G : Submodule K M) (hAB : A ≤ B) :
    finrank K A ≤ finrank K ↥(A ⊓ G)+(finrank K B-finrank K ↥(B ⊓ G)) := by
  let C := B ⊓ G
  letI : Module.Finite K A := Module.Finite.of_injective (Submodule.inclusion hAB)
    (Submodule.inclusion_injective hAB)
  letI : Module.Finite K C := Module.Finite.of_injective
    (Submodule.inclusion (show C ≤ B from inf_le_left))
    (Submodule.inclusion_injective (show C ≤ B from inf_le_left))
  have hi : A ⊓ C = A ⊓ G := by
    ext x
    constructor
    · intro hx; exact ⟨hx.1,hx.2.2⟩
    · intro hx; exact ⟨hx.1,hAB hx.1,hx.2⟩
  have hd := Submodule.finrank_sup_add_finrank_inf_eq A C
  rw [hi] at hd
  have hs : finrank K ↥(A ⊔ C) ≤ finrank K B :=
    Submodule.finrank_mono (sup_le hAB inf_le_left)
  have hc : finrank K C ≤ finrank K B := Submodule.finrank_mono inf_le_left
  change finrank K A ≤ finrank K ↥(A ⊓ G)+(finrank K B-finrank K C)
  omega

end ProofComplexity.LinearSubspaceDimension
end

section
-- Inlined Solutions.LinearStandardMonomials

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.LinearStandardMonomials

open MvPolynomial
open scoped MonomialOrder

variable {σ : Type}

def Standard (m : MonomialOrder σ) (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (d : σ →₀ ℕ) : Prop := ∀ p ∈ S, p ≠ 0 → m.degree p ≠ d

lemma leadingCoeff_one (m : MonomialOrder σ) {p : MvPolynomial σ (ZMod 2)} (hp : p ≠ 0) :
    m.leadingCoeff p = 1 := by
  have hn := m.leadingCoeff_ne_zero_iff.mpr hp
  generalize m.leadingCoeff p = a at *
  fin_cases a <;> simp_all

lemma cancel_lt (m : MonomialOrder σ) {p q : MvPolynomial σ (ZMod 2)} (hp : p ≠ 0)
    (hq : q ≠ 0) (hd : m.degree q = m.degree p) :
    m.toWithBotSyn (m.withBotDegree (p-q)) < m.toWithBotSyn (m.withBotDegree p) := by
  classical
  rw [m.withBotDegree_lt_withBotDegree_iff]
  by_cases hz : p-q = 0
  · exact Or.inr ⟨hz,hp⟩
  · apply Or.inl
    have hle : m.toSyn (m.degree (p-q)) ≤ m.toSyn (m.degree p) := by
      exact m.degree_sub_le.trans (by rw [hd,max_self])
    apply lt_of_le_of_ne hle
    intro he
    have he' : m.degree (p-q) = m.degree p := m.toSyn.injective he
    have hc : coeff (m.degree p) (p-q) ≠ 0 := by
      rw [← he']
      exact m.coeff_degree_ne_zero_iff.mpr hz
    apply hc
    rw [coeff_sub]
    have hp1 : coeff (m.degree p) p = 1 := leadingCoeff_one m hp
    have hq1 : coeff (m.degree p) q = 1 := by rw [← hd]; exact leadingCoeff_one m hq
    rw [hp1,hq1,sub_self]

/-- Linear elimination modulo an arbitrary subspace, preserving the leading-degree bound.
Unlike polynomial ideal division, this only subtracts scalar multiples of subspace vectors. -/
theorem remainder (m : MonomialOrder σ) (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) :
    ∃ r : MvPolynomial σ (ZMod 2), p-r ∈ S ∧
      m.toWithBotSyn (m.withBotDegree r) ≤ m.toWithBotSyn (m.withBotDegree p) ∧
      ∀ d ∈ r.support, Standard m S d := by
  classical
  have hwf : WellFounded (fun p q : MvPolynomial σ (ZMod 2) =>
      m.toWithBotSyn (m.withBotDegree p) < m.toWithBotSyn (m.withBotDegree q)) :=
    InvImage.wf _ wellFounded_lt
  induction p using hwf.induction with
  | h p ih =>
    by_cases hp : p = 0
    · subst p
      exact ⟨0,by simp,le_rfl,by simp⟩
    by_cases hstd : Standard m S (m.degree p)
    · let t := m.leadingTerm p
      have ht : t ≠ 0 := (m.leadingTerm_eq_zero_iff p).not.mpr hp
      have htd : m.degree t = m.degree p := m.degree_leadingTerm p
      have hlt := cancel_lt m hp ht htd
      obtain ⟨r,hrS,hrle,hrstd⟩ := ih (p-t) hlt
      refine ⟨t+r,?_,?_,?_⟩
      · convert hrS using 1 <;> ring
      · exact (m.withBotDegree_add_le t r).trans (max_le
          (by rw [m.withBotDegree_leadingTerm]) (hrle.trans hlt.le))
      · intro d hd
        have hmem := (Finset.mem_union.mp (MvPolynomial.support_add hd))
        rcases hmem with hdt | hdr
        · have he : d = m.degree p := by simpa only [t,m.support_leadingTerm' hp,Finset.mem_singleton] using hdt
          simpa only [he] using hstd
        · exact hrstd d hdr
    · simp only [Standard,not_forall,_root_.not_imp,not_not] at hstd
      obtain ⟨q,hqS,hq,hqd⟩ := hstd
      have hlt := cancel_lt m hp hq hqd
      obtain ⟨r,hrS,hrle,hrstd⟩ := ih (p-q) hlt
      refine ⟨r,?_,hrle.trans hlt.le,hrstd⟩
      convert S.add_mem hqS hrS using 1 <;> ring

noncomputable def supported (m : MonomialOrder σ)
    (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictSupport (ZMod 2) {d | Standard m S d}

theorem supported_disjoint (m : MonomialOrder σ)
    (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) : Disjoint (supported m S) S := by
  rw [Submodule.disjoint_def]
  intro p hp hpS
  by_contra hn
  exact (hp (m.degree_mem_support hn)) p hpS hn rfl

/-- The graded version used to count leading monomials in a bounded-degree solution space. -/
theorem remainder_totalDegree [LinearOrder σ] [WellFoundedGT σ]
    (S : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (p : MvPolynomial σ (ZMod 2)) :
    ∃ r : MvPolynomial σ (ZMod 2), p-r ∈ S ∧ r.totalDegree ≤ p.totalDegree ∧
      ∀ d ∈ r.support, Standard MonomialOrder.degLex S d := by
  classical
  obtain ⟨r,hrS,hrle,hrstd⟩ := remainder MonomialOrder.degLex S p
  refine ⟨r,hrS,?_,hrstd⟩
  exact MvPolynomial.degLex_totalDegree_monotone
    ((MonomialOrder.withBotDegree_le_withBotDegree_iff _ _).mp hrle).1

end AC02Frege.LinearStandardMonomials
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
-- Inlined Solutions.LinearStandardBooleanBasis

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.LinearStandardMonomials

open Module MvPolynomial BooleanBasis BooleanAlgebra

variable {V : Type} [LinearOrder V] [WellFoundedGT V]

abbrev StandardIndex (S : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) (k : ℕ) :=
  {T : Finset V // T.card ≤ k ∧ Standard MonomialOrder.degLex S
    (Finsupp.indicator T (fun _ _ => 1))}

theorem standard_images_independent {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (S : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (T : MvPolynomial V (ZMod 2) →ₗ[ZMod 2] W) (hker : ∀ p, p ∈ S ↔ T p = 0) (k : ℕ) :
    LinearIndependent (ZMod 2) (fun A : StandardIndex S k => T (xMon A.1)) := by
  classical
  let v : StandardIndex S k → MvPolynomial V (ZMod 2) := fun A => xMon A.1
  have hv : LinearIndependent (ZMod 2) v := xMon_linearIndependent.comp Subtype.val Subtype.val_injective
  have hspan : Submodule.span (ZMod 2) (Set.range v) ≤ supported MonomialOrder.degLex S := by
    apply Submodule.span_le.mpr
    rintro p ⟨A,rfl⟩
    change xMon A.1 ∈ supported MonomialOrder.degLex S
    rw [xMon_eq_monomial]
    exact (monomial_mem_restrictSupport (ZMod 2)).mpr (Or.inl A.2.2)
  apply hv.map_injOn T
  intro p hp q hq he
  apply sub_eq_zero.mp
  exact (Submodule.disjoint_def.mp (supported_disjoint MonomialOrder.degLex S))
    (p-q) ((supported MonomialOrder.degLex S).sub_mem (hspan hp) (hspan hq))
    ((hker _).mpr (by rw [map_sub,he,sub_self]))

theorem boolean_degree_image_span {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (S : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (hS : ∀ p ∈ S, IsMultilinear p)
    (T : MvPolynomial V (ZMod 2) →ₗ[ZMod 2] W) (hker : ∀ p, p ∈ S ↔ T p = 0) (k : ℕ) :
    (SemAC02.Ble V k).map T = Submodule.span (ZMod 2)
      (Set.range (fun A : StandardIndex S k => T (xMon A.1))) := by
  classical
  apply le_antisymm
  · rintro v ⟨p,hp,rfl⟩
    obtain ⟨r,hrS,hrdeg,hrstd⟩ := remainder_totalDegree S p
    have hp' := (SemAC02.BooleanDegreeSpaces.mem_Ble_iff k p).mp hp
    have hmlr : IsMultilinear r := by
      have hpM : p ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree _ _ _).mpr hp'.1
      have hqM : p-r ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree _ _ _).mpr (hS _ hrS)
      apply (mem_restrictDegree _ _ _).mp
      convert (restrictDegree V (ZMod 2) 1).sub_mem hpM hqM using 1 <;> ring
    have he : T p = T r := sub_eq_zero.mp (by rw [← map_sub]; exact (hker _).mp hrS)
    rw [he,r.as_sum,map_sum]
    apply Submodule.sum_mem
    intro d hd
    have hfree := hmlr d hd
    have hk : d.support.card ≤ k := by
      rw [← squarefree_sum d hfree]
      exact (le_totalDegree hd).trans (hrdeg.trans hp'.2)
    have hstd : Standard MonomialOrder.degLex S (Finsupp.indicator d.support (fun _ _ => 1)) := by
      rw [← squarefree_eq_indicator d hfree]
      exact hrstd d hd
    rw [squarefree_monomial d _ hfree,map_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨d.support,hk,hstd⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨A,rfl⟩
    exact ⟨xMon A.1,Submodule.subset_span ⟨A.1,A.2.1,rfl⟩,rfl⟩

theorem image_rank_eq_card [Fintype V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (S : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (hS : ∀ p ∈ S, IsMultilinear p)
    (T : MvPolynomial V (ZMod 2) →ₗ[ZMod 2] W) (hker : ∀ p, p ∈ S ↔ T p = 0) (k : ℕ) :
    finrank (ZMod 2) ((SemAC02.Ble V k).map T) = Nat.card (StandardIndex S k) := by
  classical
  rw [boolean_degree_image_span S hS T hker k,Nat.card_eq_fintype_card]
  exact finrank_span_eq_card (standard_images_independent S T hker k)

/-- The codimension of the solution space is exactly the number of counted monomials. -/
theorem codimension_eq_card [Fintype V]
    (S : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (hS : ∀ p ∈ S, IsMultilinear p) (k : ℕ) :
    finrank (ZMod 2) (SemAC02.Ble V k)-finrank (ZMod 2) ↥(SemAC02.Ble V k ⊓ S) =
      Nat.card (StandardIndex S k) := by
  classical
  have h := ProofComplexity.LinearSubspaceDimension.map_add_inter_ker (SemAC02.Ble V k) S.mkQ
  rw [S.ker_mkQ] at h
  have hker (p : MvPolynomial V (ZMod 2)) : p ∈ S ↔ S.mkQ p = 0 := by
    rw [← LinearMap.mem_ker,S.ker_mkQ]
  rw [image_rank_eq_card S hS S.mkQ hker k] at h
  omega

end AC02Frege.LinearStandardMonomials
end

section
-- Inlined Solutions.HeavyBlockCounting

set_option maxHeartbeats 1000000

namespace AC02Frege.HeavyBlockCounting

def blockUnion {n ℓ : ℕ} (J : Finset (Fin n)) : Finset (Fin n × Fin ℓ) :=
  J ×ˢ Finset.univ

def flipBlocks {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) :
    Finset (Fin n × Fin ℓ) := symmDiff T (blockUnion J)

def fold {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) : Finset (Fin n × Fin ℓ) :=
  flipBlocks T (heavyBlocks T)

theorem sum_block_card {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) :
    ∑ i : Fin n, (blockPart T i).card = T.card := by
  exact (Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (s:=T) (t:=Finset.univ)
    (fun v hv => Finset.mem_univ v.1)).symm

theorem block_univ_card {n ℓ : ℕ} (i : Fin n) :
    (blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i).card = ℓ := by
  have he : blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i = {i} ×ˢ Finset.univ := by
    ext ⟨v,a⟩
    simp [blockPart,eq_comm]
  rw [he]
  simp

theorem block_card_le {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (i : Fin n) :
    (blockPart T i).card ≤ ℓ := by
  calc
    _ ≤ (blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i).card := by
      apply Finset.card_le_card
      intro v hv
      simp only [blockPart,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      exact hv.2
    _ = _ := block_univ_card i

theorem block_inter_union {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) (i : Fin n) :
    blockPart (T ∩ blockUnion J) i = if i ∈ J then blockPart T i else ∅ := by
  by_cases hi : i ∈ J
  · rw [if_pos hi]
    ext v
    by_cases hvi : v.1 = i <;> simp_all [blockPart,blockUnion]
  · rw [if_neg hi]
    ext v
    by_cases hvi : v.1 = i <;> simp_all [blockPart,blockUnion]

theorem inter_union_card {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) :
    (T ∩ blockUnion J).card = ∑ i ∈ J, (blockPart T i).card := by
  rw [← sum_block_card]
  simp_rw [block_inter_union]
  simp only [apply_ite Finset.card,Finset.card_empty,Finset.sum_ite_mem,Finset.univ_inter]

theorem flipBlocks_involution {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) :
    flipBlocks (flipBlocks T J) J = T := symmDiff_symmDiff_cancel_right _ _

theorem block_flip {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (J : Finset (Fin n)) (i : Fin n) :
    blockPart (flipBlocks T J) i = if i ∈ J then
      blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i \ blockPart T i else blockPart T i := by
  by_cases hi : i ∈ J
  · rw [if_pos hi]
    ext v
    by_cases hvi : v.1 = i <;> by_cases hvT : v ∈ T <;>
      simp_all [blockPart,flipBlocks,blockUnion,Finset.mem_symmDiff]
  · rw [if_neg hi]
    ext v
    by_cases hvi : v.1 = i <;> by_cases hvT : v ∈ T <;>
      simp_all [blockPart,flipBlocks,blockUnion,Finset.mem_symmDiff]

theorem fold_block_card {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) (i : Fin n) :
    (blockPart (fold T) i).card = if ℓ/2 < (blockPart T i).card then
      ℓ-(blockPart T i).card else (blockPart T i).card := by
  have hsub : blockPart T i ⊆ blockPart (Finset.univ : Finset (Fin n × Fin ℓ)) i := by
    intro v hv
    simp only [blockPart,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
    exact hv.2
  simp only [fold,block_flip,heavyBlocks,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs
  · rw [Finset.card_sdiff_of_subset hsub,block_univ_card]
  · rfl

theorem fold_light {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) : fold T ∈ lightSets n ℓ := by
  simp only [lightSets,Finset.mem_filter,Finset.mem_univ,true_and]
  intro i
  rw [fold_block_card]
  have h := block_card_le T i
  split_ifs <;> omega

theorem fold_card_le {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) : (fold T).card ≤ T.card := by
  rw [← sum_block_card,← sum_block_card T]
  apply Finset.sum_le_sum
  intro i hi
  rw [fold_block_card]
  split_ifs <;> omega

theorem fold_encoding_injective {n ℓ : ℕ} :
    Function.Injective (fun T : Finset (Fin n × Fin ℓ) => (fold T,heavyBlocks T)) := by
  intro T S h
  have hfold := congrArg Prod.fst h
  have hheavy := congrArg Prod.snd h
  change fold T = fold S at hfold
  change heavyBlocks T = heavyBlocks S at hheavy
  have hT := flipBlocks_involution T (heavyBlocks T)
  have hS := flipBlocks_involution S (heavyBlocks S)
  change flipBlocks (fold T) (heavyBlocks T) = T at hT
  change flipBlocks (fold S) (heavyBlocks S) = S at hS
  rw [hfold,hheavy,hS] at hT
  exact hT.symm

end AC02Frege.HeavyBlockCounting
end

section
-- Inlined Solutions.MajorityLightCount

set_option maxHeartbeats 1000000

open MvPolynomial Module
open AC02Frege.BooleanAlgebra

namespace AC02Frege.MajorityLightCount

open HeavyBlockCounting

def lightFamily (n ℓ K : ℕ) : Finset (Finset (Fin n × Fin ℓ)) :=
  Finset.univ.filter (fun T => T ∈ lightSets n ℓ ∧ T.card ≤ K)

theorem light_count (n ℓ K : ℕ) :
    SemAC02.Hn (n*ℓ) K ≤ (lightFamily n ℓ K).card*2^n := by
  let A := (Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter (fun T => T.card ≤ K)
  let B := lightFamily n ℓ K ×ˢ (Finset.univ : Finset (Finset (Fin n)))
  have hmap : Set.MapsTo (fun T : Finset (Fin n × Fin ℓ) => (fold T,heavyBlocks T)) (↑A) (↑B) := by
    intro T hT
    have hTK : T.card ≤ K := (Finset.mem_filter.mp hT).2
    refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fold_light T,(fold_card_le T).trans hTK⟩
  have h := Finset.card_le_card_of_injOn (fun T => (fold T,heavyBlocks T)) hmap fold_encoding_injective.injOn
  have hA : A.card = SemAC02.Hn (n*ℓ) K := by
    simpa only [A,Fintype.card_prod,Fintype.card_fin] using
      SemAC02.MultiplierSupportCount.low_support_card (Fin n × Fin ℓ) K
  rw [hA] at h
  simpa only [B,Finset.card_product,Finset.card_univ,Fintype.card_finset,Fintype.card_fin] using h

theorem light_count_real (n ℓ K : ℕ) :
    (SemAC02.Hn (n*ℓ) K : ℝ)/2^n ≤ ((lightFamily n ℓ K).card : ℝ) := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^n)).mpr
  exact_mod_cast light_count n ℓ K

abbrev LightIndex (n ℓ K : ℕ) :=
  {T : Finset (Fin n × Fin ℓ) // T ∈ lightSets n ℓ ∧ T.card ≤ K}

noncomputable def lightSpace (n ℓ K : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  Submodule.span (ZMod 2) (xMon '' {T | T ∈ lightSets n ℓ ∧ T.card ≤ K})

theorem light_span (n ℓ K : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun T : LightIndex n ℓ K => xMon T.1)) = lightSpace n ℓ K := by
  unfold lightSpace
  congr 1
  ext p
  constructor
  · rintro ⟨T,rfl⟩; exact ⟨T.1,T.2,rfl⟩
  · rintro ⟨T,hT,rfl⟩; exact ⟨⟨T,hT⟩,rfl⟩

noncomputable def lightBasis (n ℓ K : ℕ) : Basis (LightIndex n ℓ K) (ZMod 2) (lightSpace n ℓ K) :=
  (Basis.span (xMon_linearIndependent.comp (fun T : LightIndex n ℓ K => T.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (light_span n ℓ K))

instance finite_lightSpace (n ℓ K : ℕ) : Module.Finite (ZMod 2) (lightSpace n ℓ K) :=
  Module.Finite.of_basis (lightBasis n ℓ K)

theorem finrank_lightSpace (n ℓ K : ℕ) :
    finrank (ZMod 2) (lightSpace n ℓ K) = (lightFamily n ℓ K).card := by
  rw [Module.finrank_eq_card_basis (lightBasis n ℓ K)]
  exact Fintype.card_subtype _

end AC02Frege.MajorityLightCount
end

section
-- Inlined Solutions.MajorityLightSeparation

set_option maxHeartbeats 2000000

open MvPolynomial AC02Frege.BooleanAlgebra

namespace AC02Frege.MajorityLightSeparation

open MajorityLightCount MajorityTensorIndex MajorityCoefficientAlgebra

theorem light_le_Ble (n ℓ K : ℕ) : lightSpace n ℓ K ≤ SemAC02.Ble (Fin n × Fin ℓ) K := by
  apply Submodule.span_mono
  rintro p ⟨T,⟨hlight,hcard⟩,rfl⟩
  exact ⟨T,hcard,rfl⟩

theorem coefficient_constant {n ℓ K : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : p ∈ lightSpace n ℓ K) :
    ∀ A : GlobalLight n ℓ, (coefficientMap hℓ A p).totalDegree ≤ 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨T,⟨hlight,hcard⟩,rfl⟩ := hp
    intro A
    change (coeffPoly (xMon T) A.1).totalDegree ≤ 0
    simpa only [mul_one,totalDegree_one] using
      MajorityCoefficientFibres.light_product_degree hℓ ⟨T,hlight⟩ A (1 : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
  | zero => intro A; simp
  | add p q hp hq ihp ihq =>
    intro A
    rw [map_add]
    exact (totalDegree_add _ _).trans (max_le (ihp A) (ihq A))
  | smul a p hp ih =>
    intro A
    rw [map_smul]
    exact (totalDegree_smul_le a _).trans (ih A)

theorem light_chat_eq_zero {n ℓ K D : ℕ} (hℓ : Odd ℓ)
    (F : LiftSAParity.CNF (Fin n)) (hF : ¬PCDerivable F D 1)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hp : p ∈ lightSpace n ℓ K)
    (hchat : p ∈ CHat F ℓ D) : p = 0 := by
  classical
  have hml : IsMultilinear p :=
    ((SemAC02.BooleanDegreeSpaces.mem_Ble_iff K p).mp (light_le_Ble n ℓ K hp)).1
  have hall : ∀ A ∈ lightSets n ℓ, coeffPoly p A = 0 := by
    intro A hA
    have hdeg := coefficient_constant hℓ p hp ⟨A,hA⟩
    change (coeffPoly p A).totalDegree ≤ 0 at hdeg
    have hC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
    rcases MajorityFoundation.eq_zero_or_one (coeff 0 (coeffPoly p A)) with ha | ha
    · simpa only [ha,map_zero] using hC
    · have h1 : coeffPoly p A = 1 := by simpa only [ha,map_one] using hC
      have hc := (hchat A hA).2
      rw [h1] at hc
      exact False.elim (hF hc)
  have hexpand : expand (coeffPoly p) = p :=
    (MajorityCoefficientDegree.coeffPoly_expansion hℓ p).2.2.trans (ml_of_multilinear p hml)
  rw [← hexpand]
  unfold expand
  have hz : (∑ A ∈ lightSets n ℓ, xMon A*bind₁ (fun i => hBlock (ℓ:=ℓ) i) (coeffPoly p A)) = 0 := by
    apply Finset.sum_eq_zero
    intro A hA
    rw [hall A hA,map_zero,mul_zero]
  rw [hz,map_zero]

noncomputable def baseSpace {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := CD F D
  zero_mem' := ⟨by simpa only [map_zero] using ml_multilinear (0 : MvPolynomial (Fin n) (ZMod 2)),Support.pc_zero F D⟩
  add_mem' hp hq := ⟨multilinear_add _ _ hp.1 hq.1,Support.pc_add F D hp.2 hq.2⟩
  smul_mem' a p hp := ⟨multilinear_smul a p hp.1,Support.pc_smul F D hp.2 a⟩

noncomputable def chatSpace {n ℓ : ℕ} (hℓ : Odd ℓ) (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  ⨅ A : GlobalLight n ℓ, (baseSpace F D).comap (coefficientMap hℓ A)

theorem mem_chatSpace {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : LiftSAParity.CNF (Fin n))
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : p ∈ chatSpace hℓ F D ↔ p ∈ CHat F ℓ D := by
  simp only [chatSpace,Submodule.mem_iInf,Submodule.mem_comap]
  constructor
  · intro h A hA
    exact h ⟨A,hA⟩
  · intro h A
    exact h A.1 A.2

end AC02Frege.MajorityLightSeparation
end

section
-- Inlined Solutions.ErrorSolutionSpaces

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ErrorSolutionSpaces

open Module MvPolynomial LiftSAParity MajorityLightSeparation LinearStandardMonomials

local instance variableOrder (n ℓ : ℕ) : LinearOrder (Fin n × Fin ℓ) :=
  LinearOrder.lift' (toLex : (Fin n × Fin ℓ) → Lex (Fin n × Fin ℓ)) (fun _ _ he => he)
local instance variableWellFounded (n ℓ : ℕ) : @WellFoundedGT (Fin n × Fin ℓ) (variableOrder n ℓ).toLT :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

/-- All multilinear solutions of a line's error conditions, before a degree cutoff. -/
noncomputable def lineSpace {n ℓ s : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ)
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  restrictDegree (Fin n × Fin ℓ) (ZMod 2) 1 ⊓
    ⨅ i, (chatSpace hℓ F D).comap (LinearMap.mulRight (ZMod 2) (P*u i))

lemma mem_lineSpace {n ℓ s D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    f ∈ lineSpace hℓ F D P u ↔ IsMultilinear f ∧ ∀ i, f*P*u i ∈ CHat F ℓ D := by
  simp only [lineSpace,Submodule.mem_inf,Submodule.mem_iInf,Submodule.mem_comap,
    LinearMap.mulRight_apply]
  constructor
  · rintro ⟨hf,hi⟩
    refine ⟨(mem_restrictDegree _ _ _).mp hf,?_⟩
    intro i
    exact (mem_chatSpace hℓ F _).mp (by simpa only [mul_assoc] using hi i)
  · rintro ⟨hf,hi⟩
    refine ⟨(mem_restrictDegree _ _ _).mpr hf,?_⟩
    intro i
    exact (mem_chatSpace hℓ F _).mpr (by simpa only [mul_assoc] using hi i)

lemma zsol_eq {n ℓ s D j : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    Zsol F ℓ D j P u = (↑(SemAC02.Ble (Fin n × Fin ℓ) j ⊓ lineSpace hℓ F D P u) :
      Set (MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) := by
  ext f
  change f ∈ Zsol F ℓ D j P u ↔ f ∈ SemAC02.Ble (Fin n × Fin ℓ) j ∧ f ∈ lineSpace hℓ F D P u
  simp only [Zsol,Vdeg,Set.mem_setOf_eq,Submodule.mem_inf,
    SemAC02.BooleanDegreeSpaces.mem_Ble_iff,mem_lineSpace]
  tauto

/-- The source's error count is the exact number of standard squarefree monomials. -/
theorem error_count_eq_card {n ℓ s D j : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hj : j ≤ n*ℓ) :
    cErr F ℓ D j P u = Nat.card (StandardIndex (lineSpace hℓ F D P u) j) := by
  classical
  have hS (f) (hf : f ∈ lineSpace hℓ F D P u) : IsMultilinear f :=
    ((mem_lineSpace hℓ F P u f).mp hf).1
  have hdim : dimSpan (Zsol F ℓ D j P u) =
      finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) j ⊓ lineSpace hℓ F D P u) := by
    unfold dimSpan
    rw [zsol_eq hℓ F P u,Submodule.span_eq]
  have hV : finrank (ZMod 2) (SemAC02.Ble (Fin n × Fin ℓ) j) = monoCount (n*ℓ) j := by
    rw [SemAC02.BooleanDegreeBasis.finrank_Ble]
    simp only [Fintype.card_prod,Fintype.card_fin,SemAC02.Hn,monoCount,min_eq_left hj]
  unfold cErr
  rw [hdim,← hV]
  exact codimension_eq_card (lineSpace hℓ F D P u) hS j

lemma lineSpace_congr {n ℓ s D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P Q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (h : ML P = ML Q) :
    lineSpace hℓ F D P u = lineSpace hℓ F D Q u := by
  ext f
  rw [mem_lineSpace,mem_lineSpace]
  have hprod (i : Fin s) : ML (f*P*u i) = ML (f*Q*u i) := by
    apply BooleanAlgebra.multilinear_ext (BooleanAlgebra.ml_multilinear _) (BooleanAlgebra.ml_multilinear _)
    intro x
    have hx := congrArg (eval x) h
    simp only [BooleanAlgebra.eval_ml] at hx
    simp only [BooleanAlgebra.eval_ml,map_mul,hx]
  simp only [MajorityFunctionCongruence.chat_congr hℓ F _ _ (hprod _)]

lemma cErr_congr {n ℓ s D K : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P Q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (h : ML P = ML Q) :
    cErr F ℓ D K P u = cErr F ℓ D K Q u := by
  unfold cErr
  rw [zsol_eq hℓ F P u,zsol_eq hℓ F Q u,lineSpace_congr hℓ F P Q u h]

@[simp] lemma cErr_ml {n ℓ s D K : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    cErr F ℓ D K (ML P) u = cErr F ℓ D K P u :=
  cErr_congr hℓ F _ _ u (BooleanAlgebra.ml_idempotent P)

end AC02Frege.ErrorSolutionSpaces
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
-- Inlined Solutions.FiniteErrorFamilies

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.FiniteErrorFamilies

open Module MvPolynomial LiftSAParity MajorityLightSeparation ErrorSolutionSpaces

noncomputable def enumerate {I : Type} (S : Finset I) : Fin (Fintype.card S) → I :=
  fun j => ((Fintype.equivFin S).symm j).1

lemma enumerate_mem {I : Type} (S : Finset I) (j : Fin (Fintype.card S)) : enumerate S j ∈ S :=
  ((Fintype.equivFin S).symm j).2

noncomputable def space {n ℓ : ℕ} {I : Type} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ)
    (S : Finset I) (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (x : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  restrictDegree (Fin n × Fin ℓ) (ZMod 2) 1 ⊓
    ⨅ i ∈ S, (chatSpace hℓ F D).comap (LinearMap.mulRight (ZMod 2) (P*x i))

lemma mem_space {n ℓ D : ℕ} {I : Type} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (S : Finset I) (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (x : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    f ∈ space hℓ F D S P x ↔ IsMultilinear f ∧ ∀ i ∈ S, f*P*x i ∈ CHat F ℓ D := by
  simp only [space,Submodule.mem_inf,Submodule.mem_iInf,Submodule.mem_comap,LinearMap.mulRight_apply]
  constructor
  · rintro ⟨hf,hx⟩
    refine ⟨(mem_restrictDegree _ _ _).mp hf,?_⟩
    intro i hi
    exact (mem_chatSpace hℓ F _).mp (by simpa only [mul_assoc] using hx i hi)
  · rintro ⟨hf,hx⟩
    refine ⟨(mem_restrictDegree _ _ _).mpr hf,?_⟩
    intro i hi
    exact (mem_chatSpace hℓ F _).mpr (by simpa only [mul_assoc] using hx i hi)

lemma space_eq_fin {n ℓ D : ℕ} {I : Type} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (S : Finset I) (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (x : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    space hℓ F D S P x = lineSpace hℓ F D P (fun j => x (enumerate S j)) := by
  ext f
  rw [mem_space,mem_lineSpace]
  constructor
  · rintro ⟨hf,hx⟩
    exact ⟨hf,fun j => hx _ (enumerate_mem S j)⟩
  · rintro ⟨hf,hx⟩
    refine ⟨hf,?_⟩
    intro i hi
    have hh := hx ((Fintype.equivFin S) ⟨i,hi⟩)
    simpa only [enumerate,Equiv.symm_apply_apply] using hh

noncomputable def rank {n ℓ : ℕ} {I : Type} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D K : ℕ)
    (S : Finset I) (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (x : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : ℕ :=
  monoCount (n*ℓ) K-finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) K ⊓ space hℓ F D S P x)

lemma rank_eq_cErr {n ℓ D K : ℕ} {I : Type} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (S : Finset I) (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (x : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    rank hℓ F D K S P x = cErr F ℓ D K P (fun j => x (enumerate S j)) := by
  unfold rank cErr dimSpan
  rw [space_eq_fin,zsol_eq hℓ F P,Submodule.span_eq]

lemma rank_nullity {n ℓ D K : ℕ} {I : Type} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (S : Finset I) (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (x : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    rank hℓ F D K S P x+finrank (ZMod 2)
      ↥(SemAC02.Ble (Fin n × Fin ℓ) K ⊓ space hℓ F D S P x) = monoCount (n*ℓ) K := by
  have hB : finrank (ZMod 2) (SemAC02.Ble (Fin n × Fin ℓ) K) = monoCount (n*ℓ) K := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using BooleanDegreeCounts.finrank_Ble (V := Fin n × Fin ℓ) K
  have hd : finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) K ⊓ space hℓ F D S P x) ≤ monoCount (n*ℓ) K := by
    rw [← hB]
    exact Submodule.finrank_mono inf_le_left
  unfold rank
  omega

lemma rank_zero_of_satisfied {n ℓ D K : ℕ} {I : Type} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (S : Finset I) (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (x : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (h : ∀ f ∈ SemAC02.Ble (Fin n × Fin ℓ) K, ∀ i ∈ S, f*P*x i ∈ CHat F ℓ D) :
    rank hℓ F D K S P x = 0 := by
  have hs : SemAC02.Ble (Fin n × Fin ℓ) K ≤ space hℓ F D S P x := by
    intro f hf
    exact (mem_space hℓ F S P x f).mpr
      ⟨((SemAC02.BooleanDegreeSpaces.mem_Ble_iff K f).mp hf).1,h f hf⟩
  have he : (SemAC02.Ble (Fin n × Fin ℓ) K ⊓ space hℓ F D S P x) =
      SemAC02.Ble (Fin n × Fin ℓ) K := inf_eq_left.mpr hs
  have hn := rank_nullity hℓ F S P x (D := D) (K := K)
  rw [he] at hn
  have hB : finrank (ZMod 2) (SemAC02.Ble (Fin n × Fin ℓ) K) = monoCount (n*ℓ) K := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using BooleanDegreeCounts.finrank_Ble (V := Fin n × Fin ℓ) K
  omega

end AC02Frege.FiniteErrorFamilies
end

section
-- Inlined Solutions.MajorityQuotient

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.MajorityQuotient

open Module MvPolynomial LiftSAParity BooleanAlgebra MajorityLightSeparation MajorityFunctionCongruence

noncomputable abbrev BoolSpace (V : Type) := restrictDegree V (ZMod 2) 1

instance finite_BoolSpace (V : Type) [Fintype V] [DecidableEq V] : Module.Finite (ZMod 2) (BoolSpace V) :=
  Module.Finite.of_basis (ProofComplexity.BooleanCoordinates.booleanBasis V)

noncomputable def reduce (V : Type) : MvPolynomial V (ZMod 2) →ₗ[ZMod 2] BoolSpace V :=
  ML.codRestrict (BoolSpace V) (fun p => (mem_restrictDegree _ _ _).mpr (ml_multilinear p))

noncomputable def consequence {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ) :
    Submodule (ZMod 2) (BoolSpace (Fin n × Fin ℓ)) :=
  (chatSpace hℓ F D).comap (BoolSpace (Fin n × Fin ℓ)).subtype

abbrev Quot {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ) :=
  BoolSpace (Fin n × Fin ℓ) ⧸ consequence hℓ F D

noncomputable def remainder {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ) :
    MvPolynomial (Fin n × Fin ℓ) (ZMod 2) →ₗ[ZMod 2] Quot hℓ F D :=
  (consequence hℓ F D).mkQ.comp (reduce (Fin n × Fin ℓ))

lemma remainder_zero_iff {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    remainder hℓ F D p = 0 ↔ p ∈ CHat F ℓ D := by
  change (consequence hℓ F D).mkQ (reduce _ p) = 0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ]
  change ML p ∈ chatSpace hℓ F D ↔ p ∈ CHat F ℓ D
  rw [mem_chatSpace]
  exact chat_congr hℓ F (ML p) p (ml_idempotent p)

lemma remainder_congr {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (h : ML p = ML q) :
    remainder hℓ F D p = remainder hℓ F D q := by
  apply congrArg (consequence hℓ F D).mkQ
  apply Subtype.ext
  exact h

@[simp] lemma remainder_ml {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    remainder hℓ F D (ML p) = remainder hℓ F D p :=
  remainder_congr hℓ F _ _ (ml_idempotent p)

lemma remainder_mul_ml_left {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    remainder hℓ F D (ML p*q) = remainder hℓ F D (p*q) :=
  remainder_congr hℓ F _ _ (ml_mul_left p q)

lemma remainder_mul_ml_right {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    remainder hℓ F D (p*ML q) = remainder hℓ F D (p*q) :=
  remainder_congr hℓ F _ _ (ml_mul_right p q)

lemma ml_square {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2)) : ML (p*p) = ML p := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  rw [eval_ml,eval_ml,map_mul]
  simpa only [ZMod.card,pow_two] using FiniteField.pow_card (eval x p)

lemma remainder_square_mul {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (p u : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    remainder hℓ F D (p*u*u) = remainder hℓ F D (p*u) := by
  calc
    _ = remainder hℓ F D (p*(u*u)) := by congr 1; ring
    _ = remainder hℓ F D (p*ML (u*u)) := (remainder_mul_ml_right hℓ F p (u*u)).symm
    _ = _ := by rw [ml_square,remainder_mul_ml_right]

end AC02Frege.MajorityQuotient
end

section
-- Inlined Solutions.BooleanMonomialSubspaces

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.BooleanMonomialSubspaces

open Module MvPolynomial BooleanBasis BooleanAlgebra

lemma span_index {V : Type} (P : Finset V → Prop) :
    Submodule.span (ZMod 2) (Set.range (fun A : {T : Finset V // P T} => xMon A.1)) = monomialSpan P := by
  unfold monomialSpan
  congr 1
  ext p
  constructor
  · rintro ⟨A,rfl⟩
    exact ⟨A.1,A.2,rfl⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨⟨A,hA⟩,rfl⟩

noncomputable def basis {V : Type} (P : Finset V → Prop) :
    Basis {T : Finset V // P T} (ZMod 2) (monomialSpan P) :=
  (Basis.span (xMon_linearIndependent.comp (fun T : {T : Finset V // P T} => T.1)
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ (span_index P))

lemma finrank_span {V : Type} [Fintype V] (P : Finset V → Prop) :
    finrank (ZMod 2) (monomialSpan P) = Nat.card {T : Finset V // P T} := by
  classical
  rw [Module.finrank_eq_card_basis (basis P),Nat.card_eq_fintype_card]

lemma span_inter {V : Type} (P Q : Finset V → Prop) :
    monomialSpan P ⊓ monomialSpan Q = monomialSpan (fun T => P T ∧ Q T) := by
  ext p
  simp only [Submodule.mem_inf,mem_monomialSpan_iff]
  constructor
  · rintro ⟨⟨hm,hP⟩,⟨_,hQ⟩⟩
    exact ⟨hm,fun d hd => ⟨hP d hd,hQ d hd⟩⟩
  · rintro ⟨hm,h⟩
    exact ⟨⟨hm,fun d hd => (h d hd).1⟩,⟨hm,fun d hd => (h d hd).2⟩⟩

lemma degree_space {V : Type} (j : ℕ) :
    SemAC02.Ble V j = monomialSpan (fun T : Finset V => T.card ≤ j) := by
  ext p
  rw [SemAC02.BooleanDegreeSpaces.mem_Ble_iff,BooleanBasis.mem_light_iff]

end AC02Frege.BooleanMonomialSubspaces
end

section
-- Inlined Solutions.GoodCoefficientSpace

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.GoodCoefficientSpace

open Module MvPolynomial BooleanBasis BooleanMonomialSubspaces

noncomputable def goodSpace (n ℓ Q : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  monomialSpan (fun T => (heavyBlocks T).card ≤ Q)

lemma mem_goodSpace {n ℓ Q : ℕ} (hℓ : Odd ℓ)
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    p ∈ goodSpace n ℓ Q ↔ IsMultilinear p ∧ p ∈ WQ n ℓ Q := by
  rw [goodSpace,mem_monomialSpan_iff]
  constructor
  · rintro ⟨hp,hs⟩
    exact ⟨hp,(MajorityCoefficientDegree.coeffDeg_threshold hℓ p hp Q).mpr hs⟩
  · rintro ⟨hp,hs⟩
    exact ⟨hp,(MajorityCoefficientDegree.coeffDeg_threshold hℓ p hp Q).mp hs⟩

lemma good_dimension (n ℓ Q j : ℕ) :
    finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) j ⊓ goodSpace n ℓ Q) =
      ((Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter
        (fun T => T.card ≤ j ∧ (heavyBlocks T).card ≤ Q)).card := by
  classical
  rw [degree_space,goodSpace,span_inter,finrank_span,Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

/-- The cost of restricting degree-j multipliers to coefficient degree at most Q is exactly E_j. -/
theorem excluded_codimension (n ℓ Q j : ℕ) :
    finrank (ZMod 2) (SemAC02.Ble (Fin n × Fin ℓ) j) =
      finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) j ⊓ goodSpace n ℓ Q)+Eexcl n ℓ Q j := by
  classical
  rw [SemAC02.BooleanDegreeBasis.finrank_Ble,good_dimension]
  have hfull : ((Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter (fun T => T.card ≤ j)).card =
      SemAC02.Hn (n*ℓ) j := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using
      SemAC02.MultiplierSupportCount.low_support_card (Fin n × Fin ℓ) j
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Finset (Fin n × Fin ℓ))).filter (fun T => T.card ≤ j))
    (p := fun T => (heavyBlocks T).card ≤ Q)
  simpa only [Finset.filter_filter,not_le,Fintype.card_prod,Fintype.card_fin,← hfull,Eexcl] using h.symm

/-- Any degree-j solution space loses at most E_j dimensions on restriction to W_Q. -/
theorem solution_restriction_loss (n ℓ Q j : ℕ)
    (S : Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) :
    finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) j ⊓ S) ≤
      finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) j ⊓ (S ⊓ goodSpace n ℓ Q))+Eexcl n ℓ Q j := by
  classical
  let B := SemAC02.Ble (Fin n × Fin ℓ) j
  have h := ProofComplexity.LinearSubspaceDimension.intersection_loss B (B ⊓ S)
    (goodSpace n ℓ Q) inf_le_left
  have he := excluded_codimension n ℓ Q j
  have hd : finrank (ZMod 2) B-finrank (ZMod 2) ↥(B ⊓ goodSpace n ℓ Q) = Eexcl n ℓ Q j := by
    change finrank (ZMod 2) B = finrank (ZMod 2) ↥(B ⊓ goodSpace n ℓ Q)+Eexcl n ℓ Q j at he
    omega
  rw [hd,inf_assoc] at h
  exact h

end AC02Frege.GoodCoefficientSpace
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
-- Inlined Solutions.MajorityQuotientMultiplication

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.MajorityQuotientMultiplication

open Module MvPolynomial LiftSAParity BooleanAlgebra BooleanFlip GoodCoefficientSpace
open MajorityFunctionCongruence MajorityQuotient

/-- Multiplication descends on low coefficient-degree quotient images and extends linearly
from those images to the whole finite-dimensional quotient. -/
theorem exists_multiplier {n ℓ D L r : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (u : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hu : u.totalDegree ≤ r) (hD : L+r ≤ D) :
    ∃ H : Quot hℓ F D →ₗ[ZMod 2] Quot hℓ F D,
      ∀ p ∈ goodSpace n ℓ L, H (remainder hℓ F D p) = remainder hℓ F D (p*u) := by
  classical
  let A := goodSpace n ℓ L
  let R := remainder hℓ F D
  let f := R.domRestrict A
  let g := (R.comp (LinearMap.mulRight (ZMod 2) u)).domRestrict A
  have hker : f.ker ≤ g.ker := by
    intro p hp
    have hpC : (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) ∈ CHat F ℓ D :=
      (remainder_zero_iff hℓ F _).mp hp
    have hb : coeffDeg p.1 ≤ (L : WithBot ℕ) := ((mem_goodSpace hℓ p.1).mp p.2).2
    have hd : (ML u).totalDegree ≤ r := (ml_totalDegree_le u).trans hu
    have hdw : ((ML u).totalDegree : WithBot ℕ) ≤ (r : WithBot ℕ) := by exact_mod_cast hd
    have hD' : (L : WithBot ℕ)+(r : WithBot ℕ) ≤ (D : WithBot ℕ) := by exact_mod_cast hD
    have hc := degree_preserves hℓ F p.1 u hpC ((add_le_add hb hdw).trans hD')
    exact (remainder_zero_iff hℓ F _).mpr hc
  obtain ⟨H,hH⟩ := ProofComplexity.LinearMapFactorThrough.exists_factor f g hker
  refine ⟨H,?_⟩
  intro p hp
  exact LinearMap.congr_fun hH ⟨p,hp⟩

noncomputable def errorMap {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P u : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) :
    X →ₗ[ZMod 2] Quot hℓ F D :=
  ((remainder hℓ F D).comp (LinearMap.mulRight (ZMod 2) (P*u))).domRestrict X

/-- The auxiliary binary maps for the one-factor gain. -/
theorem exists_certificate {n ℓ s D Q r : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hu : ∀ i, (u i).totalDegree ≤ r)
    (hD : Q+P.totalDegree+3*r ≤ D)
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) (hX : X ≤ goodSpace n ℓ Q) :
    ∃ H : Fin s → Quot hℓ F D →ₗ[ZMod 2] Quot hℓ F D,
      (∀ i, (H i).comp (errorMap hℓ F P (u i) X) = errorMap hℓ F P (u i) X) ∧
      ∀ i j, (H i).comp (errorMap hℓ F P (u j) X) = (H j).comp (errorMap hℓ F P (u i) X) := by
  classical
  let L := Q+P.totalDegree+r
  have hbudget : L+r ≤ D := by dsimp [L]; omega
  choose H hH using (fun i => exists_multiplier (L := L) hℓ F (u i) (hu i) hbudget)
  have hgood (j : Fin s) (x : X) : ML (x.1*(P*u j)) ∈ goodSpace n ℓ L := by
    apply (mem_goodSpace hℓ _).mpr
    refine ⟨ml_multilinear _,?_⟩
    change coeffDeg (ML (x.1*(P*u j))) ≤ (L : WithBot ℕ)
    rw [beta_ml hℓ]
    have hb : coeffDeg x.1 ≤ (Q : WithBot ℕ) := ((mem_goodSpace hℓ x.1).mp (hX x.2)).2
    have hd : (ML (P*u j)).totalDegree ≤ P.totalDegree+r :=
      (ml_totalDegree_le _).trans ((totalDegree_mul _ _).trans (Nat.add_le_add_left (hu j) _))
    have hdw : ((ML (P*u j)).totalDegree : WithBot ℕ) ≤ (P.totalDegree : WithBot ℕ)+(r : WithBot ℕ) := by
      exact_mod_cast hd
    have hh := (degree_estimate hℓ x.1 (P*u j)).trans (add_le_add hb hdw)
    convert hh using 1 <;> dsimp [L] <;> push_cast <;> ac_rfl
  have haction (i j : Fin s) (x : X) :
      H i (errorMap hℓ F P (u j) X x) = remainder hℓ F D (x.1*(P*u j)*u i) := by
    change H i (remainder hℓ F D (x.1*(P*u j))) = _
    calc
      _ = H i (remainder hℓ F D (ML (x.1*(P*u j)))) := by rw [remainder_ml]
      _ = remainder hℓ F D (ML (x.1*(P*u j))*u i) := hH i _ (hgood j x)
      _ = _ := remainder_mul_ml_left hℓ F _ _
  refine ⟨H,?_,?_⟩
  · intro i
    ext x
    rw [LinearMap.comp_apply,haction]
    calc
      _ = remainder hℓ F D ((x.1*P)*u i*u i) := by congr 1; ring
      _ = remainder hℓ F D ((x.1*P)*u i) := remainder_square_mul hℓ F _ _
      _ = errorMap hℓ F P (u i) X x := by change _ = remainder hℓ F D (x.1*(P*u i)); congr 1; ring
  · intro i j
    ext x
    rw [LinearMap.comp_apply,LinearMap.comp_apply,haction,haction]
    congr 1
    ring

end AC02Frege.MajorityQuotientMultiplication
end

section
-- Inlined Solutions.OneFactorAlgebra

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.OneFactorAlgebra

open Module MvPolynomial LiftSAParity BooleanAlgebra BooleanFlip GoodCoefficientSpace
open MajorityFunctionCongruence MajorityQuotient MajorityQuotientMultiplication ErrorSolutionSpaces

noncomputable def combination {V : Type} {s : ℕ} (u : Fin s → MvPolynomial V (ZMod 2))
    (a : Fin s → ZMod 2) : MvPolynomial V (ZMod 2) := ∑ i, a i • u i

lemma combination_degree {V : Type} {s r : ℕ} (u : Fin s → MvPolynomial V (ZMod 2))
    (hu : ∀ i, (u i).totalDegree ≤ r) (a : Fin s → ZMod 2) : (combination u a).totalDegree ≤ r := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_smul_le _ _).trans (hu i)

lemma factor_degree {V : Type} {s r : ℕ} (u : Fin s → MvPolynomial V (ZMod 2))
    (hu : ∀ i, (u i).totalDegree ≤ r) (a : Fin s → ZMod 2) :
    (1+combination u a).totalDegree ≤ r :=
  (totalDegree_add _ _).trans (max_le (by simp) (combination_degree u hu a))

lemma complement_zero {V : Type} [Finite V] (t : MvPolynomial V (ZMod 2)) : ML (t*(1+t)) = 0 := by
  rw [mul_add,mul_one,map_add,ml_square]
  exact CharTwo.add_self_eq_zero _

lemma remainder_combination {n ℓ s D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (f P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (a : Fin s → ZMod 2) :
    remainder hℓ F D (f*P*combination u a) = ∑ i, a i • remainder hℓ F D (f*P*u i) := by
  rw [combination,Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_smul_comm,map_smul]

noncomputable def candidate {n ℓ : ℕ}
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)))
    (t : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    X →ₗ[ZMod 2] MvPolynomial (Fin n × Fin ℓ) (ZMod 2) :=
  ML.comp ((LinearMap.mulRight (ZMod 2) t).domRestrict X)

lemma candidate_in_new {n ℓ s D K Q r : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hu : ∀ i, (u i).totalDegree ≤ r)
    (a : Fin s → ZMod 2) (hrK : r ≤ K)
    (x : ↥(SemAC02.Ble (Fin n × Fin ℓ) (K-r) ⊓ goodSpace n ℓ Q)) :
    candidate (SemAC02.Ble (Fin n × Fin ℓ) (K-r) ⊓ goodSpace n ℓ Q) (combination u a) x ∈
      SemAC02.Ble (Fin n × Fin ℓ) K ⊓ lineSpace hℓ F D (P*(1+combination u a)) u := by
  classical
  let t := combination u a
  change ML (x.1*t) ∈ _
  have hx := (SemAC02.BooleanDegreeSpaces.mem_Ble_iff (K-r) x.1).mp x.2.1
  have hdeg : (ML (x.1*t)).totalDegree ≤ K :=
    (ml_totalDegree_le _).trans ((totalDegree_mul _ _).trans
      ((Nat.add_le_add hx.2 (combination_degree u hu a)).trans (by omega)))
  refine ⟨(SemAC02.BooleanDegreeSpaces.mem_Ble_iff K _).mpr ⟨ml_multilinear _,hdeg⟩,?_⟩
  apply (mem_lineSpace hℓ F _ u _).mpr
  refine ⟨ml_multilinear _,?_⟩
  intro i
  apply (remainder_zero_iff hℓ F _).mp
  calc
    _ = remainder hℓ F D (ML (x.1*t)*(P*u i*(1+t))) := by congr 1; ring
    _ = remainder hℓ F D ((x.1*t)*(P*u i*(1+t))) := remainder_mul_ml_left hℓ F _ _
    _ = remainder hℓ F D ((x.1*P*u i)*(t*(1+t))) := by congr 1; ring
    _ = remainder hℓ F D ((x.1*P*u i)*ML (t*(1+t))) := (remainder_mul_ml_right hℓ F _ _).symm
    _ = 0 := by rw [complement_zero,mul_zero,map_zero]

lemma old_solutions_persist {n ℓ s D Q r : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hu : ∀ i, (u i).totalDegree ≤ r)
    (a : Fin s → ZMod 2) (hD : Q+P.totalDegree+3*r ≤ D)
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hf : f ∈ lineSpace hℓ F D P u ⊓ goodSpace n ℓ Q) :
    f ∈ lineSpace hℓ F D (P*(1+combination u a)) u := by
  have hs := (mem_lineSpace hℓ F P u f).mp hf.1
  have hb : coeffDeg f ≤ (Q : WithBot ℕ) := ((mem_goodSpace hℓ f).mp hf.2).2
  apply (mem_lineSpace hℓ F _ u f).mpr
  refine ⟨hs.1,?_⟩
  intro i
  have hd : (ML (P*u i)).totalDegree ≤ P.totalDegree+r :=
    (ml_totalDegree_le _).trans ((totalDegree_mul _ _).trans (Nat.add_le_add_left (hu i) _))
  have hdw : ((ML (P*u i)).totalDegree : WithBot ℕ) ≤ (P.totalDegree : WithBot ℕ)+(r : WithBot ℕ) := by exact_mod_cast hd
  have hp := (degree_estimate hℓ f (P*u i)).trans (add_le_add hb hdw)
  have hq : (ML (1+combination u a)).totalDegree ≤ r := (ml_totalDegree_le _).trans (factor_degree u hu a)
  have hqw : ((ML (1+combination u a)).totalDegree : WithBot ℕ) ≤ (r : WithBot ℕ) := by exact_mod_cast hq
  have hbudget : coeffDeg (f*P*u i)+((ML (1+combination u a)).totalDegree : WithBot ℕ) ≤ (D : WithBot ℕ) := by
    have hh := add_le_add hp hqw
    have hdw' : (Q : WithBot ℕ)+((P.totalDegree : WithBot ℕ)+(r : WithBot ℕ))+(r : WithBot ℕ) ≤
        (D : WithBot ℕ) := by exact_mod_cast (show Q+(P.totalDegree+r)+r ≤ D by omega)
    simpa only [mul_assoc] using hh.trans hdw'
  have hc := degree_preserves hℓ F (f*P*u i) (1+combination u a) (hs.2 i) hbudget
  have he : f*(P*(1+combination u a))*u i = (f*P*u i)*(1+combination u a) := by ring
  rw [he]
  exact hc

lemma combined_map {n ℓ s D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (a : Fin s → ZMod 2)
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) :
    (∑ i, a i • errorMap (D := D) hℓ F P (u i) X) = errorMap (D := D) hℓ F P (combination u a) X := by
  ext x
  simp only [LinearMap.sum_apply,LinearMap.smul_apply]
  change (∑ i, a i • remainder hℓ F D (x.1*(P*u i))) = remainder hℓ F D (x.1*(P*combination u a))
  simpa only [mul_assoc] using (remainder_combination hℓ F x.1 P u a).symm

/-- Candidates already in the old solution space are killed by the correction-rank map. -/
lemma candidate_relation {n ℓ s D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (a : Fin s → ZMod 2)
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) (x : X)
    (hx : candidate X (combination u a) x ∈ lineSpace hℓ F D P u) :
    errorMap (D := D) hℓ F P (combination u a) X x = 0 := by
  classical
  let t := combination u a
  have hs := ((mem_lineSpace hℓ F P u _).mp hx).2
  change ∀ i, ML (x.1*t)*P*u i ∈ CHat F ℓ D at hs
  have hz : remainder hℓ F D (ML (x.1*t)*P*t) = 0 := by
    rw [remainder_combination]
    apply Finset.sum_eq_zero
    intro i hi
    rw [(remainder_zero_iff hℓ F _).mpr (hs i),smul_zero]
  change remainder hℓ F D (x.1*(P*t)) = 0
  calc
    _ = remainder hℓ F D ((x.1*P)*t) := by congr 1; ring
    _ = remainder hℓ F D ((x.1*P)*t*t) := (remainder_square_mul hℓ F _ _).symm
    _ = remainder hℓ F D ((x.1*t)*(P*t)) := by congr 1; ring
    _ = remainder hℓ F D (ML (x.1*t)*(P*t)) := (remainder_mul_ml_left hℓ F _ _).symm
    _ = _ := by simpa only [mul_assoc] using hz

end AC02Frege.OneFactorAlgebra
end

section
-- Inlined Solutions.ErrorSpaceDimensions

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ErrorSpaceDimensions

open Module MvPolynomial LiftSAParity ErrorSolutionSpaces GoodCoefficientSpace MajorityQuotient
open MajorityQuotientMultiplication

lemma error_rank_nullity {n ℓ s D K : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    cErr F ℓ D K P u+finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) K ⊓ lineSpace hℓ F D P u) =
      finrank (ZMod 2) (SemAC02.Ble (Fin n × Fin ℓ) K) := by
  classical
  have hd : dimSpan (Zsol F ℓ D K P u) =
      finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) K ⊓ lineSpace hℓ F D P u) := by
    unfold dimSpan
    rw [zsol_eq hℓ F P u,Submodule.span_eq]
  have hB : finrank (ZMod 2) (SemAC02.Ble (Fin n × Fin ℓ) K) = monoCount (n*ℓ) K := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using BooleanDegreeCounts.finrank_Ble (V := Fin n × Fin ℓ) K
  have hle : finrank (ZMod 2) ↥(SemAC02.Ble (Fin n × Fin ℓ) K ⊓ lineSpace hℓ F D P u) ≤
      finrank (ZMod 2) (SemAC02.Ble (Fin n × Fin ℓ) K) := Submodule.finrank_mono inf_le_left
  unfold cErr
  rw [hd,← hB]
  omega

lemma threshold_rank_nullity {n ℓ D K : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) :
    hThresh F ℓ D K+finrank (ZMod 2)
      ↥(SemAC02.Ble (Fin n × Fin ℓ) K ⊓ MajorityLightSeparation.chatSpace hℓ F D) =
        finrank (ZMod 2) (SemAC02.Ble (Fin n × Fin ℓ) K) := by
  classical
  let B := SemAC02.Ble (Fin n × Fin ℓ) K
  let C := MajorityLightSeparation.chatSpace hℓ F D
  have hs : Vdeg (Fin n × Fin ℓ) K ∩ CHat F ℓ D = (↑(B ⊓ C) :
      Set (MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) := by
    ext p
    change (IsMultilinear p ∧ p.totalDegree ≤ K) ∧ p ∈ CHat F ℓ D ↔ p ∈ B ∧ p ∈ C
    rw [SemAC02.BooleanDegreeSpaces.mem_Ble_iff,MajorityLightSeparation.mem_chatSpace]
  have hd : dimSpan (Vdeg (Fin n × Fin ℓ) K ∩ CHat F ℓ D) = finrank (ZMod 2) ↥(B ⊓ C) := by
    unfold dimSpan
    rw [hs,Submodule.span_eq]
  have hB : finrank (ZMod 2) B = monoCount (n*ℓ) K := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using BooleanDegreeCounts.finrank_Ble (V := Fin n × Fin ℓ) K
  have hle : finrank (ZMod 2) ↥(B ⊓ C) ≤ finrank (ZMod 2) B := Submodule.finrank_mono inf_le_left
  unfold hThresh
  rw [hd,← hB]
  change (finrank (ZMod 2) B-finrank (ZMod 2) ↥(B ⊓ C))+finrank (ZMod 2) ↥(B ⊓ C) = finrank (ZMod 2) B
  omega

lemma common_kernel_map {n ℓ s D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (X : Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)))
    (hX : ∀ p ∈ X, IsMultilinear p) :
    (⨅ i, (errorMap (D := D) hℓ F P (u i) X).ker).map X.subtype = X ⊓ lineSpace hℓ F D P u := by
  ext f
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.2,(mem_lineSpace hℓ F P u x.1).mpr ⟨hX x.1 x.2,?_⟩⟩
    intro i
    have hh := (Submodule.mem_iInf _).mp hx i
    have hz : remainder hℓ F D (x.1*(P*u i)) = 0 := hh
    simpa only [mul_assoc] using (remainder_zero_iff hℓ F _).mp hz
  · intro hf
    refine ⟨⟨f,hf.1⟩,?_,rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro i
    have hh := ((mem_lineSpace hℓ F P u f).mp hf.2).2 i
    change remainder hℓ F D (f*(P*u i)) = 0
    exact (remainder_zero_iff hℓ F _).mpr (by simpa only [mul_assoc] using hh)

/-- The common rank on the restricted multiplier domain loses at most the excluded count. -/
theorem common_rank_lower {n ℓ s D j Q : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    let B := SemAC02.Ble (Fin n × Fin ℓ) j
    let X := B ⊓ goodSpace n ℓ Q
    cErr F ℓ D j P u ≤
      (finrank (ZMod 2) X-finrank (ZMod 2) ↥(⨅ i, (errorMap (D := D) hℓ F P (u i) X).ker))+Eexcl n ℓ Q j := by
  classical
  intro B X
  let S := lineSpace hℓ F D P u
  let K := ⨅ i, (errorMap (D := D) hℓ F P (u i) X).ker
  letI : Module.Finite (ZMod 2) X := Module.Finite.of_injective
    (Submodule.inclusion (show X ≤ B from inf_le_left))
    (Submodule.inclusion_injective (show X ≤ B from inf_le_left))
  letI : Module.Finite (ZMod 2) ↥(B ⊓ S) := Module.Finite.of_injective
    (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective (show B ⊓ S ≤ B from inf_le_left))
  have hmap : K.map X.subtype = X ⊓ S := common_kernel_map hℓ F P u X
    (fun p hp => ((SemAC02.BooleanDegreeSpaces.mem_Ble_iff j p).mp hp.1).1)
  have hkdim : finrank (ZMod 2) K = finrank (ZMod 2) ↥(X ⊓ S) := by
    rw [← hmap,Submodule.finrank_map_subtype_eq]
  have hkbound : finrank (ZMod 2) K ≤ finrank (ZMod 2) ↥(B ⊓ S) := by
    rw [hkdim]
    exact Submodule.finrank_mono (inf_le_inf inf_le_left le_rfl)
  have hKX : finrank (ZMod 2) K ≤ finrank (ZMod 2) X := Submodule.finrank_le _
  have he := excluded_codimension n ℓ Q j
  change finrank (ZMod 2) B = finrank (ZMod 2) X+Eexcl n ℓ Q j at he
  have hn := error_rank_nullity hℓ F P u (D := D) (K := j)
  change cErr F ℓ D j P u+finrank (ZMod 2) ↥(B ⊓ S) = finrank (ZMod 2) B at hn
  change cErr F ℓ D j P u ≤ (finrank (ZMod 2) X-finrank (ZMod 2) K)+Eexcl n ℓ Q j
  omega

end AC02Frege.ErrorSpaceDimensions
end

section
-- Inlined Solutions.InitialErrorCount

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.InitialErrorCount

open Module MvPolynomial LiftSAParity ErrorSolutionSpaces ErrorSpaceDimensions GoodCoefficientSpace
open BooleanFlip MajorityLightSeparation MajorityFunctionCongruence

/-- The initial error count loses at most E_K on restriction to coefficient degree Q. -/
theorem initial_count {n ℓ s D K Q r : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hu : ∀ i, (u i).totalDegree ≤ r)
    (hD : Q+r ≤ D) : cErr F ℓ D K 1 u ≤ hThresh F ℓ D K+Eexcl n ℓ Q K := by
  classical
  let B := SemAC02.Ble (Fin n × Fin ℓ) K
  let C := chatSpace hℓ F D
  let S := lineSpace hℓ F D 1 u
  let Z := B ⊓ S
  let U := B ⊓ (C ⊓ goodSpace n ℓ Q)
  letI : Module.Finite (ZMod 2) Z := Module.Finite.of_injective
    (Submodule.inclusion (show Z ≤ B from inf_le_left))
    (Submodule.inclusion_injective (show Z ≤ B from inf_le_left))
  have hUZ : U ≤ Z := by
    intro f hf
    refine ⟨hf.1,(mem_lineSpace hℓ F 1 u f).mpr ⟨?_,?_⟩⟩
    · exact ((SemAC02.BooleanDegreeSpaces.mem_Ble_iff K f).mp hf.1).1
    · intro i
      have hc : f ∈ CHat F ℓ D := (mem_chatSpace hℓ F f).mp hf.2.1
      have hb : coeffDeg f ≤ (Q : WithBot ℕ) := ((mem_goodSpace hℓ f).mp hf.2.2).2
      have hd : (ML (u i)).totalDegree ≤ r := (ml_totalDegree_le _).trans (hu i)
      have hdw : ((ML (u i)).totalDegree : WithBot ℕ) ≤ (r : WithBot ℕ) := by exact_mod_cast hd
      have hD' : (Q : WithBot ℕ)+(r : WithBot ℕ) ≤ (D : WithBot ℕ) := by exact_mod_cast hD
      simpa only [mul_one] using degree_preserves hℓ F f (u i) hc ((add_le_add hb hdw).trans hD')
  have hmono : finrank (ZMod 2) U ≤ finrank (ZMod 2) Z := Submodule.finrank_mono hUZ
  have hloss : finrank (ZMod 2) ↥(B ⊓ C) ≤ finrank (ZMod 2) U+Eexcl n ℓ Q K :=
    solution_restriction_loss n ℓ Q K C
  have hC : hThresh F ℓ D K+finrank (ZMod 2) ↥(B ⊓ C) = finrank (ZMod 2) B := threshold_rank_nullity hℓ F
  have hS : cErr F ℓ D K 1 u+finrank (ZMod 2) Z = finrank (ZMod 2) B := error_rank_nullity hℓ F 1 u
  omega

end AC02Frege.InitialErrorCount
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
-- Inlined Solutions.OneFactorGain

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.OneFactorGain

open Module MvPolynomial LiftSAParity GoodCoefficientSpace ErrorSolutionSpaces
open MajorityQuotient MajorityQuotientMultiplication OneFactorAlgebra ErrorSpaceDimensions

theorem one_factor_gain {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D Q K r s : ℕ)
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hP : IsMultilinear P)
    (hrK : r ≤ K) (hD : Q + P.totalDegree + 3 * r ≤ D) :
    ∃ a : Fin s → ZMod 2,
      (cErr F ℓ D K (P * (1 + ∑ i, a i • u i)) u : ℝ) ≤
        (cErr F ℓ D K P u : ℝ) - (1 / 2) * (cErr F ℓ D (K - r) P u : ℝ)
          + (Eexcl n ℓ Q K : ℝ) + (1 / 2) * (Eexcl n ℓ Q (K - r) : ℝ)  := by
  classical
  let B := SemAC02.Ble (Fin n × Fin ℓ) K
  let Bsmall := SemAC02.Ble (Fin n × Fin ℓ) (K-r)
  let X := Bsmall ⊓ goodSpace n ℓ Q
  let S := lineSpace hℓ F D P u
  let U := B ⊓ (S ⊓ goodSpace n ℓ Q)
  let M := fun i => errorMap (D := D) hℓ F P (u i) X
  let J := ⨅ i, (M i).ker
  letI : Module.Finite (ZMod 2) X := Module.Finite.of_injective
    (Submodule.inclusion (show X ≤ Bsmall from inf_le_left))
    (Submodule.inclusion_injective (show X ≤ Bsmall from inf_le_left))
  obtain ⟨H,hd,hc⟩ := exists_certificate hℓ F P u (fun i => (hu i).2) hD X inf_le_right
  obtain ⟨a,ha⟩ := LinearPang.half_joint_rank s M H hd hc
  let t := combination u a
  let P' := P*(1+t)
  let Z := B ⊓ lineSpace hℓ F D P' u
  let L := candidate X t
  let Φ := errorMap (D := D) hℓ F P t X
  letI : Module.Finite (ZMod 2) Z := Module.Finite.of_injective
    (Submodule.inclusion (show Z ≤ B from inf_le_left))
    (Submodule.inclusion_injective (show Z ≤ B from inf_le_left))
  have hsum : (∑ i, a i • M i) = Φ := combined_map hℓ F P u a X
  rw [hsum] at ha
  have hhalf : finrank (ZMod 2) X-finrank (ZMod 2) J ≤ 2*finrank (ZMod 2) Φ.range := by
    have hh : ((finrank (ZMod 2) X-finrank (ZMod 2) J : ℕ) : ℝ) ≤
        2*(finrank (ZMod 2) Φ.range : ℝ) := by linarith [ha]
    exact_mod_cast hh
  have hUZ : U ≤ Z := by
    intro f hf
    refine ⟨hf.1,?_⟩
    exact old_solutions_persist hℓ F P u (fun i => (hu i).2) a hD f hf.2
  have hL : ∀ x : X, L x ∈ Z := by
    intro x
    exact candidate_in_new hℓ F P u (fun i => (hu i).2) a hrK x
  have hkill : ∀ x : X, L x ∈ U → Φ x = 0 := by
    intro x hx
    exact candidate_relation hℓ F P u a X x hx.2.1
  have hgain := ProofComplexity.LinearDimensionGain.gain_bound U Z hUZ L Φ hL hkill
  have hold : finrank (ZMod 2) ↥(B ⊓ S) ≤ finrank (ZMod 2) U+Eexcl n ℓ Q K :=
    solution_restriction_loss n ℓ Q K S
  have hlow : cErr F ℓ D (K-r) P u ≤
      (finrank (ZMod 2) X-finrank (ZMod 2) J)+Eexcl n ℓ Q (K-r) :=
    common_rank_lower hℓ F P u (j := K-r) (Q := Q)
  have hnold : cErr F ℓ D K P u+finrank (ZMod 2) ↥(B ⊓ S) = finrank (ZMod 2) B :=
    error_rank_nullity hℓ F P u
  have hnnew : cErr F ℓ D K P' u+finrank (ZMod 2) Z = finrank (ZMod 2) B :=
    error_rank_nullity hℓ F P' u
  have hnat : 2*cErr F ℓ D K P' u+cErr F ℓ D (K-r) P u ≤
      2*cErr F ℓ D K P u+2*Eexcl n ℓ Q K+Eexcl n ℓ Q (K-r) := by omega
  have hreal : 2*(cErr F ℓ D K P' u : ℝ)+(cErr F ℓ D (K-r) P u : ℝ) ≤
      2*(cErr F ℓ D K P u : ℝ)+2*(Eexcl n ℓ Q K : ℝ)+(Eexcl n ℓ Q (K-r) : ℝ) := by exact_mod_cast hnat
  refine ⟨a,?_⟩
  change (cErr F ℓ D K P' u : ℝ) ≤ _
  nlinarith

end AC02Frege.OneFactorGain
end

section
-- Inlined Solutions.BooleanLeadingMonomials

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.BooleanLeadingMonomials

open MvPolynomial BooleanAlgebra BooleanBasis
open scoped MonomialOrder

variable {V : Type}

lemma ml_expansion (p : MvPolynomial V (ZMod 2)) :
    ML p = ∑ d ∈ p.support, monomial (sqfree d) (p.coeff d) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum,ml_monomial]

lemma sqfree_le (d : V →₀ ℕ) : sqfree d ≤ d := by
  intro i
  exact min_le_left _ _

lemma degree_ml_le (m : MonomialOrder V) (p : MvPolynomial V (ZMod 2)) :
    m.toSyn (m.degree (ML p)) ≤ m.toSyn (m.degree p) := by
  classical
  apply m.degree_le_iff.mpr
  intro d hd
  rw [ml_expansion] at hd
  obtain ⟨s,hs,hds⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have he : d = sqfree s := Finset.mem_singleton.mp (support_monomial_subset hds)
  rw [he]
  exact (m.toSyn_monotone (sqfree_le s)).trans (m.le_degree hs)

lemma coeff_leading_ml (m : MonomialOrder V) (p : MvPolynomial V (ZMod 2)) (hp : p ≠ 0)
    (hfree : ∀ i, m.degree p i ≤ 1) : coeff (m.degree p) (ML p) = m.leadingCoeff p := by
  classical
  rw [ml_expansion,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (m.degree p)]
  · rw [sqfree_eq_self _ hfree,MvPolynomial.coeff_monomial,if_pos rfl]
    rfl
  · intro d hd hne
    have hs : sqfree d ≠ m.degree p := by
      intro he
      have hle : m.toSyn (m.degree p) ≤ m.toSyn d := by
        rw [← he]
        exact m.toSyn_monotone (sqfree_le d)
      have hd' : d = m.degree p := m.toSyn.injective (le_antisymm (m.le_degree hd) hle)
      exact hne hd'
    simp only [MvPolynomial.coeff_monomial,if_neg hs]
  · intro hnot
    exact False.elim (hnot (m.degree_mem_support hp))

lemma leading_ml {m : MonomialOrder V} {p : MvPolynomial V (ZMod 2)} (hp : p ≠ 0)
    (hfree : ∀ i, m.degree p i ≤ 1) : ML p ≠ 0 ∧ m.degree (ML p) = m.degree p := by
  have hc : coeff (m.degree p) (ML p) ≠ 0 := by
    rw [coeff_leading_ml m p hp hfree]
    exact m.leadingCoeff_ne_zero_iff.mpr hp
  have hn : ML p ≠ 0 := by intro hz; simp [hz] at hc
  refine ⟨hn,m.toSyn.injective (le_antisymm (degree_ml_le m p) (m.le_degree (mem_support_iff.mpr hc)))⟩

lemma indicator_insert [DecidableEq V] {S : Finset V} {v : V} (hv : v ∉ S) :
    Finsupp.indicator S (fun _ _ => (1 : ℕ))+Finsupp.single v 1 =
      Finsupp.indicator (insert v S) (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i = v
  · subst i; simp [Finsupp.indicator_apply,hv]
  · by_cases hS : i ∈ S <;> simp [Finsupp.indicator_apply,hi,hS]

/-- Multiplication by a variable absent from the leading monomial preserves that extension
as the leading monomial after Boolean multilinearization. -/
theorem leading_extension [DecidableEq V] (m : MonomialOrder V) {p : MvPolynomial V (ZMod 2)} (hp : p ≠ 0)
    (S : Finset V) (hS : m.degree p = Finsupp.indicator S (fun _ _ => 1))
    (v : V) (hv : v ∉ S) :
    ML (p*X v) ≠ 0 ∧ m.degree (ML (p*X v)) = Finsupp.indicator (insert v S) (fun _ _ => 1) := by
  classical
  have hX : (X v : MvPolynomial V (ZMod 2)) ≠ 0 := X_ne_zero v
  have hprod : p*X v ≠ 0 := mul_ne_zero hp hX
  have hd : m.degree (p*X v) = Finsupp.indicator (insert v S) (fun _ _ => 1) := by
    rw [m.degree_mul hp hX,m.degree_X,hS,indicator_insert hv]
  have hfree : ∀ i, m.degree (p*X v) i ≤ 1 := by
    intro i
    rw [hd]
    simp only [Finsupp.indicator_apply]
    split_ifs <;> omega
  obtain ⟨hn,he⟩ := leading_ml hprod hfree
  exact ⟨hn,he.trans hd⟩

end AC02Frege.BooleanLeadingMonomials
end

section
-- Inlined Solutions.ErrorSpaceMultiplication

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ErrorSpaceMultiplication

open MvPolynomial LiftSAParity BooleanAlgebra BooleanFlip ErrorSolutionSpaces GoodCoefficientSpace
open MajorityFunctionCongruence

/-- The multiplication needed in Appendix B.1, with its coefficient-degree budget explicit. -/
theorem multiply_variable {n ℓ s D Q r : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hu : ∀ i, (u i).totalDegree ≤ r)
    (hD : Q+P.totalDegree+r+1 ≤ D)
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hf : f ∈ lineSpace hℓ F D P u ⊓ goodSpace n ℓ Q) (v : Fin n × Fin ℓ) :
    ML (f*X v) ∈ lineSpace hℓ F D P u := by
  classical
  have hfs := (mem_lineSpace hℓ F P u f).mp hf.1
  have hb : coeffDeg f ≤ (Q : WithBot ℕ) := ((mem_goodSpace hℓ f).mp hf.2).2
  apply (mem_lineSpace hℓ F P u _).mpr
  refine ⟨ml_multilinear _,?_⟩
  intro i
  have hprod : coeffDeg (f*P*u i) ≤ (Q : WithBot ℕ)+(P.totalDegree : WithBot ℕ)+(r : WithBot ℕ) := by
    have hd : (ML (P*u i)).totalDegree ≤ P.totalDegree+r :=
      (ml_totalDegree_le _).trans ((totalDegree_mul _ _).trans (Nat.add_le_add_left (hu i) _))
    have hdw : ((ML (P*u i)).totalDegree : WithBot ℕ) ≤ (P.totalDegree : WithBot ℕ)+(r : WithBot ℕ) := by
      exact_mod_cast hd
    have hh := (degree_estimate hℓ f (P*u i)).trans (add_le_add hb hdw)
    simpa only [mul_assoc,add_assoc] using hh
  have hx : (ML (X v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))).totalDegree = 1 := by
    rw [ml_of_multilinear _ (by simpa [xMon] using xMon_multilinear ({v} : Finset (Fin n × Fin ℓ))),totalDegree_X]
  have hbudget : coeffDeg (f*P*u i)+((ML (X v)).totalDegree : WithBot ℕ) ≤ (D : WithBot ℕ) := by
    rw [hx]
    have hdw : (Q : WithBot ℕ)+(P.totalDegree : WithBot ℕ)+(r : WithBot ℕ)+(1 : WithBot ℕ) ≤
        (D : WithBot ℕ) := by exact_mod_cast hD
    exact (add_le_add hprod le_rfl).trans hdw
  have hc := degree_preserves hℓ F (f*P*u i) (X v) (hfs.2 i) hbudget
  apply (chat_congr hℓ F _ _ ?_).mpr hc
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [eval_ml,map_mul]
  ring

end AC02Frege.ErrorSpaceMultiplication
end

section
-- Inlined Solutions.StandardMonomialFamilies

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.StandardMonomialFamilies

open Module MvPolynomial LinearStandardMonomials

variable {V : Type} [Fintype V] [LinearOrder V] [WellFoundedGT V]

noncomputable def family (S : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun T => Standard MonomialOrder.degLex S (Finsupp.indicator T (fun _ _ => 1)))

lemma family_mono {S S' : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} (h : S' ≤ S) :
    family S ⊆ family S' := by
  classical
  intro T hT
  have ht : Standard MonomialOrder.degLex S (Finsupp.indicator T (fun _ _ => 1)) :=
    (Finset.mem_filter.mp hT).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro p hp hn
  exact ht p (h hp) hn

lemma cumulative_card (S : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))) (j : ℕ) :
    ((family S).filter (fun T => T.card ≤ j)).card = Nat.card (StandardIndex S j) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp only [family,Finset.filter_filter,and_comm]

/-- A cumulative difference between nested families bounds the difference in each layer. -/
lemma layer_bound_of_cumulative (A B : Finset (Finset V)) (hAB : A ⊆ B) (j E : ℕ)
    (hcard : (B.filter (fun T => T.card ≤ j)).card ≤ (A.filter (fun T => T.card ≤ j)).card+E) :
    (B.filter (fun T => T.card = j)).card ≤ (A.filter (fun T => T.card = j)).card+E := by
  classical
  let X := B.filter (fun T => T.card ≤ j)
  let Y := A.filter (fun T => T.card ≤ j)
  have hYX : Y ⊆ X := Finset.filter_subset_filter _ hAB
  have hdiff : (X \ Y).card ≤ E := by
    rw [Finset.card_sdiff_of_subset hYX]
    change X.card ≤ Y.card+E at hcard
    omega
  have hs : B.filter (fun T => T.card = j) ⊆ A.filter (fun T => T.card = j) ∪ (X \ Y) := by
    intro T hT
    have ht := Finset.mem_filter.mp hT
    by_cases ha : T ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha,ht.2⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨ht.1,ht.2.le⟩,?_⟩
      intro hy
      exact ha (Finset.mem_filter.mp hy).1
  calc
    _ ≤ (A.filter (fun T => T.card = j) ∪ (X \ Y)).card := Finset.card_le_card hs
    _ ≤ (A.filter (fun T => T.card = j)).card+(X \ Y).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left hdiff _

/-- Loss of E solution-space dimensions adds at most E counted monomials in a layer. -/
theorem layer_card_loss (S S' : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (hSS : S' ≤ S) (hS : ∀ p ∈ S, IsMultilinear p) (j E : ℕ)
    (hloss : finrank (ZMod 2) ↥(SemAC02.Ble V j ⊓ S) ≤
      finrank (ZMod 2) ↥(SemAC02.Ble V j ⊓ S')+E) :
    ((family S').filter (fun T => T.card = j)).card ≤
      ((family S).filter (fun T => T.card = j)).card+E := by
  classical
  apply layer_bound_of_cumulative (family S) (family S') (family_mono hSS) j E
  rw [cumulative_card,cumulative_card]
  have hS' (p) (hp : p ∈ S') : IsMultilinear p := hS p (hSS hp)
  have h1 := codimension_eq_card S hS j
  have h2 := codimension_eq_card S' hS' j
  have hle1 : finrank (ZMod 2) ↥(SemAC02.Ble V j ⊓ S) ≤ finrank (ZMod 2) (SemAC02.Ble V j) :=
    Submodule.finrank_mono inf_le_left
  have hle2 : finrank (ZMod 2) ↥(SemAC02.Ble V j ⊓ S') ≤ finrank (ZMod 2) (SemAC02.Ble V j) :=
    Submodule.finrank_mono inf_le_left
  omega

end AC02Frege.StandardMonomialFamilies
end

section
-- Inlined Solutions.BooleanFamilyIncidence

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.BooleanFamilyIncidence

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

def layer (A : Finset (Finset V)) (j : ℕ) : Finset (Finset V) := A.filter (fun S => S.card = j)

lemma extension_bound (A : Finset (Finset V)) (S : Finset V) (j : ℕ) (hS : S.card = j) :
    ((layer A (j+1)).bipartiteAbove (· ⊆ ·) S).card ≤ Fintype.card V-j := by
  let U := (univ : Finset V) \ S
  have hU : U.card = Fintype.card V-j := by
    rw [card_sdiff_of_subset (subset_univ S),card_univ,hS]
  rw [← hU]
  refine le_trans (card_le_card (t := U.image (fun v => insert v S)) ?_) card_image_le
  intro T hT
  simp only [Finset.mem_bipartiteAbove] at hT
  obtain ⟨hT,hST⟩ := hT
  obtain ⟨hTA,hTc⟩ := mem_filter.mp hT
  obtain ⟨v,hv,rfl⟩ := exists_eq_insert_iff.mpr ⟨hST,by omega⟩
  exact mem_image.mpr ⟨v,mem_sdiff.mpr ⟨mem_univ _,hv⟩,rfl⟩

/-- An approximate downset incidence bound, allowing a larger family of divisors. -/
theorem incidence (A B : Finset (Finset V)) (j : ℕ)
    (hdiv : ∀ T ∈ layer A (j+1), ∀ S ⊆ T, S.card = j → S ∈ B) :
    (layer A (j+1)).card*(j+1) ≤ (layer B j).card*(Fintype.card V-j) := by
  apply card_mul_le_card_mul' (· ⊆ ·)
  · intro T hT
    obtain ⟨hTA,hTc⟩ := mem_filter.mp hT
    rw [← hTc,← card_image_of_injOn T.erase_injOn]
    apply card_le_card
    intro S hS
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hS
    simp only [Finset.mem_bipartiteBelow]
    refine ⟨mem_filter.mpr ⟨hdiv T hT (T.erase v) (erase_subset _ _) ?_,?_⟩,erase_subset _ _⟩
    · rw [card_erase_of_mem hv,hTc]; omega
    · rw [card_erase_of_mem hv,hTc]; omega
  · intro S hS
    exact extension_bound A S j (mem_filter.mp hS).2

lemma cumulative_card (A : Finset (Finset V)) (k : ℕ) :
    (A.filter (fun T => T.card ≤ k)).card = ∑ j ∈ range (k+1), (layer A j).card := by
  have h := sum_card_fiberwise_eq_card_filter A (range (k+1)) (fun T => T.card)
  simpa only [layer,mem_range,Nat.lt_succ_iff] using h.symm

end AC02Frege.BooleanFamilyIncidence
end

section
-- Inlined Solutions.ErrorCountIncidence

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ErrorCountIncidence

open Module MvPolynomial LiftSAParity ErrorSolutionSpaces GoodCoefficientSpace
open LinearStandardMonomials StandardMonomialFamilies BooleanFamilyIncidence

local instance variableOrder (n ℓ : ℕ) : LinearOrder (Fin n × Fin ℓ) := ErrorSolutionSpaces.variableOrder n ℓ
local instance variableWellFounded (n ℓ : ℕ) : @WellFoundedGT (Fin n × Fin ℓ) (variableOrder n ℓ).toLT :=
  ErrorSolutionSpaces.variableWellFounded n ℓ

lemma divisor_counted {n ℓ s D Q r : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hu : ∀ i, (u i).totalDegree ≤ r)
    (hD : Q+P.totalDegree+r+1 ≤ D)
    (T S : Finset (Fin n × Fin ℓ))
    (hT : T ∈ family (lineSpace hℓ F D P u)) (hST : S ⊆ T) (hcard : S.card+1 = T.card) :
    S ∈ family (lineSpace hℓ F D P u ⊓ goodSpace n ℓ Q) := by
  classical
  have ht : Standard MonomialOrder.degLex (lineSpace hℓ F D P u)
      (Finsupp.indicator T (fun _ _ => 1)) := (Finset.mem_filter.mp hT).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro p hp hn hd
  obtain ⟨v,hv,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hST,hcard⟩
  have hm := ErrorSpaceMultiplication.multiply_variable hℓ F P u hu hD p hp v
  obtain ⟨hmn,hmd⟩ := BooleanLeadingMonomials.leading_extension MonomialOrder.degLex hn S hd v hv
  exact ht _ hm hmn hmd

/-- The exact approximate-incidence inequality in Appendix B.1. -/
theorem error_incidence {n ℓ s D Q r : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hu : ∀ i, (u i).totalDegree ≤ r)
    (hD : Q+P.totalDegree+r+1 ≤ D) (j : ℕ) :
    let A := family (lineSpace hℓ F D P u)
    (layer A (j+1)).card*(j+1) ≤ ((layer A j).card+Eexcl n ℓ Q j)*(n*ℓ-j) := by
  classical
  intro A
  let S := lineSpace hℓ F D P u
  let B := family (S ⊓ goodSpace n ℓ Q)
  have hi : (layer A (j+1)).card*(j+1) ≤ (layer B j).card*(n*ℓ-j) := by
    have h := incidence A B j (by
      intro T hT U hUT hUc
      exact divisor_counted hℓ F P u hu hD T U (Finset.mem_filter.mp hT).1 hUT
        (by have := (Finset.mem_filter.mp hT).2; omega))
    simpa only [Fintype.card_prod,Fintype.card_fin] using h
  have hl : (layer B j).card ≤ (layer A j).card+Eexcl n ℓ Q j :=
    layer_card_loss S (S ⊓ goodSpace n ℓ Q) inf_le_left
      (fun f hf => ((mem_lineSpace hℓ F P u f).mp hf).1) j (Eexcl n ℓ Q j)
      (solution_restriction_loss n ℓ Q j S)
  exact hi.trans (Nat.mul_le_mul_right _ hl)

lemma error_count_sum {n ℓ s D j : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hj : j ≤ n*ℓ) :
    cErr F ℓ D j P u = ∑ i ∈ Finset.range (j+1),
      (layer (family (lineSpace hℓ F D P u)) i).card := by
  rw [error_count_eq_card hℓ F P u hj,← StandardMonomialFamilies.cumulative_card,BooleanFamilyIncidence.cumulative_card]

end AC02Frege.ErrorCountIncidence
end

section
-- Inlined Solutions.ApproximateCumulativeRatios

set_option maxHeartbeats 2000000

namespace ProofComplexity.ApproximateCumulativeRatios

open Finset

/-- Pairwise approximate monotonicity of layer densities bounds their cumulative averages,
with the error paid once, rather than at every cumulative step. -/
theorem cumulative_comparison (a w : ℕ → ℝ) (k K : ℕ) (hkK : k ≤ K)
    (hw : ∀ i ≤ K, 0 < w i) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ i ≤ k, ∀ j, k < j → j ≤ K → a j/w j ≤ a i/w i+E) :
    (∑ j ∈ range (K+1), a j)/(∑ j ∈ range (K+1), w j) ≤
      (∑ j ∈ range (k+1), a j)/(∑ j ∈ range (k+1), w j)+E := by
  let B := ∑ i ∈ range (k+1), a i
  let W := ∑ i ∈ range (k+1), w i
  have hW : 0 < W := by
    apply Finset.sum_pos
    · intro i hi
      exact hw i (by have := mem_range.mp hi; omega)
    · exact ⟨0,by simp⟩
  have hWfull : 0 < ∑ i ∈ range (K+1), w i := by
    apply Finset.sum_pos
    · intro i hi
      exact hw i (by have := mem_range.mp hi; omega)
    · exact ⟨0,by simp⟩
  have hlate (j : ℕ) (hkj : k < j) (hjK : j ≤ K) : a j ≤ (B/W+E)*w j := by
    have hcross : (a j/w j-E)*W ≤ B := by
      dsimp only [B,W]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      apply (le_div_iff₀ (hw i (hik.trans hkK))).mp
      have hh := hpair i hik j hkj hjK
      linarith
    have hd : a j/w j-E ≤ B/W := (le_div_iff₀ hW).mpr hcross
    apply (div_le_iff₀ (hw j hjK)).mp
    linarith
  have hbase : B ≤ (B/W+E)*W := by
    have heq : B/W*W = B := div_mul_cancel₀ B hW.ne'
    have hn := mul_nonneg hE hW.le
    nlinarith
  have hsum : ∀ t, k ≤ t → t ≤ K →
      (∑ j ∈ range (t+1), a j) ≤ (B/W+E)*(∑ j ∈ range (t+1), w j) := by
    intro t hkt
    induction t,hkt using Nat.le_induction with
    | base => intro _; exact hbase
    | succ t hkt ih =>
      intro htK
      have hh := ih (by omega)
      have hl := hlate (t+1) (by omega) htK
      rw [Finset.sum_range_succ a (t+1),Finset.sum_range_succ w (t+1)]
      nlinarith
  exact (div_le_iff₀ hWfull).mpr (hsum K hkK le_rfl)

/-- A per-step error bounded by e*N accumulates to at most e*N^2 over at most N steps. -/
theorem density_drift (δ : ℕ → ℝ) (N K : ℕ) (hKN : K ≤ N) (e : ℝ) (he : 0 ≤ e)
    (hstep : ∀ j < K, δ (j+1) ≤ δ j+e*N) :
    ∀ i ≤ K, ∀ j, i ≤ j → j ≤ K → δ j ≤ δ i+e*(N : ℝ)^2 := by
  intro i hi j hij hjK
  have hchain : ∀ t, i ≤ t → t ≤ K → δ t ≤ δ i+e*N*((t-i : ℕ) : ℝ) := by
    intro t hit
    induction t,hit using Nat.le_induction with
    | base => intro _; simp
    | succ t hit ih =>
      intro htK
      have hh := ih (by omega)
      have hs := hstep t (by omega)
      have hsub : t+1-i = (t-i)+1 := by omega
      rw [hsub,Nat.cast_add,Nat.cast_one]
      nlinarith
  have h := hchain j hij hjK
  have hlen : ((j-i : ℕ) : ℝ) ≤ N := by exact_mod_cast (show j-i ≤ N by omega)
  have hn : 0 ≤ e*(N : ℝ) := mul_nonneg he (Nat.cast_nonneg _)
  have he' := mul_le_mul_of_nonneg_left hlen hn
  nlinarith

end ProofComplexity.ApproximateCumulativeRatios
end

section
-- Inlined Solutions.ExcludedCumulativeCounts

set_option maxHeartbeats 2000000

namespace AC02Frege.ExcludedCumulativeCounts

open Finset

def badLayer (n ℓ Q j : ℕ) : ℕ :=
  ((univ : Finset (Finset (Fin n × Fin ℓ))).filter
    (fun T => T.card = j ∧ Q < (heavyBlocks T).card)).card

lemma excluded_sum (n ℓ Q j : ℕ) : Eexcl n ℓ Q j = ∑ i ∈ range (j+1), badLayer n ℓ Q i := by
  let A := (univ : Finset (Finset (Fin n × Fin ℓ))).filter (fun T => Q < (heavyBlocks T).card)
  have h := sum_card_fiberwise_eq_card_filter A (range (j+1)) (fun T => T.card)
  simpa only [A,Eexcl,badLayer,filter_filter,mem_range,Nat.lt_succ_iff,and_comm] using h.symm

lemma layer_fraction_le (n ℓ Q K j : ℕ) (hj : j ≤ K) :
    (badLayer n ℓ Q j : ℝ)/((n*ℓ).choose j : ℝ) ≤ epsExcl n ℓ Q K := by
  exact Finset.le_sup' (fun i : ℕ => (badLayer n ℓ Q i : ℝ)/((n*ℓ).choose i : ℝ))
    (show j ∈ range (K+1) by simpa using hj)

lemma eps_nonneg (n ℓ Q K : ℕ) : 0 ≤ epsExcl n ℓ Q K := by
  exact (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans (layer_fraction_le n ℓ Q K 0 (by omega))

lemma excluded_bound (n ℓ Q K j : ℕ) (hj : j ≤ K) (hKN : K ≤ n*ℓ) :
    (Eexcl n ℓ Q j : ℝ) ≤ epsExcl n ℓ Q K*(monoCount (n*ℓ) j : ℝ) := by
  rw [excluded_sum,Nat.cast_sum,monoCount,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hij : i ≤ j := by have := mem_range.mp hi; omega
  have hp : (0 : ℝ) < ((n*ℓ).choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (hij.trans (hj.trans hKN))
  exact (div_le_iff₀ hp).mp (layer_fraction_le n ℓ Q K i (hij.trans hj))

lemma cumulative_choose_le (N j : ℕ) (hj : j ≤ N/2) :
    monoCount N j ≤ (j+1)*N.choose j := by
  have hchoose : ∀ i ≤ j, N.choose i ≤ N.choose j := by
    intro i hij
    have hh : ∀ t, i ≤ t → t ≤ j → N.choose i ≤ N.choose t := by
      intro t hit
      induction t,hit using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ t hit ih =>
        intro htj
        exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
    exact hh j hij le_rfl
  unfold monoCount
  calc
    _ ≤ ∑ _i ∈ range (j+1), N.choose j := by
      apply Finset.sum_le_sum
      intro i hi
      exact hchoose i (by have := mem_range.mp hi; omega)
    _ = _ := by simp

end AC02Frege.ExcludedCumulativeCounts
end

section
-- Inlined Solutions.ApproximateBinomialRatios

set_option maxHeartbeats 2000000

namespace AC02Frege.ApproximateBinomialRatios

open Finset ExcludedCumulativeCounts

lemma monoCount_pos (N j : ℕ) : 0 < monoCount N j := by
  have h : 1 ≤ monoCount N j := by
    unfold monoCount
    simpa only [Nat.choose_zero_right] using
      (Finset.single_le_sum (f := fun i => N.choose i) (s := range (j+1)) (by intros; omega) (show 0 ∈ range (j+1) by simp))
  omega

lemma density_step (N K : ℕ) (hKN : 2*K < N) (b E : ℕ → ℕ) (e : ℝ) (he : 0 ≤ e)
    (hinc : ∀ j < K, b (j+1)*(j+1) ≤ (b j+E j)*(N-j))
    (hE : ∀ j ≤ K, (E j : ℝ) ≤ e*(monoCount N j : ℝ)) (j : ℕ) (hj : j < K) :
    (b (j+1) : ℝ)/(N.choose (j+1) : ℝ) ≤ (b j : ℝ)/(N.choose j : ℝ)+e*(j+1) := by
  have hjN : j+1 ≤ N := by omega
  have hp : (0 : ℝ) < (N.choose j : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : j ≤ N)
  have hp' : (0 : ℝ) < (N.choose (j+1) : ℝ) := by exact_mod_cast Nat.choose_pos hjN
  have hi : (b (j+1) : ℝ)*(j+1) ≤ ((b j : ℝ)+(E j : ℝ))*((N-j : ℕ) : ℝ) := by exact_mod_cast hinc j hj
  have hc : (N.choose (j+1) : ℝ)*(j+1) = (N.choose j : ℝ)*((N-j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq N j
  have hcross : (b (j+1) : ℝ)*(N.choose j : ℝ) ≤ ((b j : ℝ)+(E j : ℝ))*(N.choose (j+1) : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < j+1)).mp
    calc
      _ = ((b (j+1) : ℝ)*(j+1))*(N.choose j : ℝ) := by ring
      _ ≤ (((b j : ℝ)+(E j : ℝ))*((N-j : ℕ) : ℝ))*(N.choose j : ℝ) :=
        mul_le_mul_of_nonneg_right hi hp.le
      _ = ((b j : ℝ)+(E j : ℝ))*((N.choose j : ℝ)*((N-j : ℕ) : ℝ)) := by ring
      _ = _ := by rw [← hc]; ring
  have hratio : (b (j+1) : ℝ)/(N.choose (j+1) : ℝ) ≤ ((b j : ℝ)+(E j : ℝ))/(N.choose j : ℝ) :=
    (div_le_div_iff₀ hp' hp).mpr hcross
  have hcount : (monoCount N j : ℝ) ≤ (j+1)*(N.choose j : ℝ) := by
    exact_mod_cast cumulative_choose_le N j (by omega)
  have hEb : (E j : ℝ) ≤ e*(j+1)*(N.choose j : ℝ) :=
    (hE j (by omega)).trans (by nlinarith [mul_le_mul_of_nonneg_left hcount he])
  have hEr : (E j : ℝ)/(N.choose j : ℝ) ≤ e*(j+1) := (div_le_iff₀ hp).mpr hEb
  rw [add_div] at hratio
  linarith

/-- The numerical conclusion of Appendix B.1 from its approximate incidence hypothesis. -/
theorem cumulative_bound (N K k : ℕ) (hKN : 2*K < N) (hk : k ≤ K)
    (b E : ℕ → ℕ) (e : ℝ) (he : 0 ≤ e)
    (hinc : ∀ j < K, b (j+1)*(j+1) ≤ (b j+E j)*(N-j))
    (hE : ∀ j ≤ K, (E j : ℝ) ≤ e*(monoCount N j : ℝ)) :
    (monoCount N k : ℝ)/(monoCount N K : ℝ)*(∑ j ∈ range (K+1), (b j : ℝ))
        -(N : ℝ)^2*e*(monoCount N k : ℝ) ≤ ∑ j ∈ range (k+1), (b j : ℝ) := by
  let δ := fun j => (b j : ℝ)/(N.choose j : ℝ)
  have hstep (j : ℕ) (hj : j < K) : δ (j+1) ≤ δ j+e*N := by
    have h := density_step N K hKN b E e he hinc hE j hj
    have hn : (j : ℝ)+1 ≤ N := by exact_mod_cast (show j+1 ≤ N by omega)
    dsimp only [δ]
    nlinarith [mul_le_mul_of_nonneg_left hn he]
  have hpair := ProofComplexity.ApproximateCumulativeRatios.density_drift δ N K (by omega) e he hstep
  have hw (i : ℕ) (hi : i ≤ K) : (0 : ℝ) < (N.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : i ≤ N)
  have hcum := ProofComplexity.ApproximateCumulativeRatios.cumulative_comparison
    (fun j => (b j : ℝ)) (fun j => (N.choose j : ℝ)) k K hk hw
    (e*(N : ℝ)^2) (mul_nonneg he (sq_nonneg _))
    (fun i hi j hkj hj => hpair i (hi.trans hk) j (by omega) hj)
  have hkpos : (0 : ℝ) < (monoCount N k : ℝ) := by exact_mod_cast monoCount_pos N k
  have hM : ∀ j, (∑ i ∈ range (j+1), (N.choose i : ℝ)) = (monoCount N j : ℝ) := by
    intro j
    rw [monoCount,Nat.cast_sum]
  rw [hM,hM] at hcum
  have h := mul_le_mul_of_nonneg_right hcum hkpos.le
  rw [add_mul,div_mul_cancel₀ _ hkpos.ne'] at h
  have hl : ((∑ j ∈ range (K+1), (b j : ℝ))/(monoCount N K : ℝ))*(monoCount N k : ℝ) =
      (monoCount N k : ℝ)/(monoCount N K : ℝ)*(∑ j ∈ range (K+1), (b j : ℝ)) := by ring
  rw [hl] at h
  nlinarith

end AC02Frege.ApproximateBinomialRatios
end

section
-- Inlined Solutions.ErrorDegreeComparison

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ErrorDegreeComparison

open MvPolynomial LiftSAParity ErrorSolutionSpaces ErrorCountIncidence
open StandardMonomialFamilies BooleanFamilyIncidence

local instance variableOrder (n ℓ : ℕ) : LinearOrder (Fin n × Fin ℓ) := ErrorSolutionSpaces.variableOrder n ℓ
local instance variableWellFounded (n ℓ : ℕ) : @WellFoundedGT (Fin n × Fin ℓ) (variableOrder n ℓ).toLT :=
  ErrorSolutionSpaces.variableWellFounded n ℓ

theorem degree_comparison {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D Q K r s : ℕ)
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hP : IsMultilinear P)
    (hrK : r ≤ K) (hKN : 2 * K < n * ℓ) (hD : Q + P.totalDegree + r + 1 ≤ D) :
    (monoCount (n * ℓ) (K - r) : ℝ) / (monoCount (n * ℓ) K : ℝ) * (cErr F ℓ D K P u : ℝ)
        - ((n * ℓ : ℕ) : ℝ) ^ 2 * epsExcl n ℓ Q K * (monoCount (n * ℓ) (K - r) : ℝ)
      ≤ (cErr F ℓ D (K - r) P u : ℝ)  := by
  classical
  let A := family (lineSpace hℓ F D P u)
  let b := fun j => (layer A j).card
  let E := fun j => Eexcl n ℓ Q j
  let e := epsExcl n ℓ Q K
  have hN : K ≤ n*ℓ := by omega
  have hinc (j : ℕ) (hj : j < K) : b (j+1)*(j+1) ≤ (b j+E j)*(n*ℓ-j) :=
    error_incidence hℓ F P u (fun i => (hu i).2) hD j
  have hE (j : ℕ) (hj : j ≤ K) : (E j : ℝ) ≤ e*(monoCount (n*ℓ) j : ℝ) :=
    ExcludedCumulativeCounts.excluded_bound n ℓ Q K j hj hN
  have h := ApproximateBinomialRatios.cumulative_bound (n*ℓ) K (K-r) hKN (Nat.sub_le _ _)
    b E e (ExcludedCumulativeCounts.eps_nonneg n ℓ Q K) hinc hE
  have hsum (j : ℕ) (hj : j ≤ n*ℓ) : (∑ i ∈ Finset.range (j+1), (b i : ℝ)) = (cErr F ℓ D j P u : ℝ) := by
    exact_mod_cast (error_count_sum hℓ F P u hj).symm
  rw [hsum K hN,hsum (K-r) ((Nat.sub_le _ _).trans hN)] at h
  exact h

end AC02Frege.ErrorDegreeComparison
end

section
-- Inlined Solutions.MajorityApproximationNumerics

namespace AC02Frege.MajorityApproximationNumerics

lemma eta_pos (N K r : ℕ) : 0 < etaFrac N K r := by
  have hm : (0 : ℝ) < (monoCount N (K-r) : ℝ) := by exact_mod_cast ApproximateBinomialRatios.monoCount_pos N (K-r)
  have hM : (0 : ℝ) < (monoCount N K : ℝ) := by exact_mod_cast ApproximateBinomialRatios.monoCount_pos N K
  unfold etaFrac
  positivity

lemma eta_le_half (N K r : ℕ) : etaFrac N K r ≤ (1/2 : ℝ) := by
  have hM : (0 : ℝ) < (monoCount N K : ℝ) := by exact_mod_cast ApproximateBinomialRatios.monoCount_pos N K
  have hm : (monoCount N (K-r) : ℝ) ≤ (monoCount N K : ℝ) := by
    exact_mod_cast BooleanDegreeCounts.monoCount_mono N (Nat.sub_le K r)
  unfold etaFrac
  apply (div_le_iff₀ hM).mpr
  nlinarith

lemma contraction_numerics (N M m e x z y EK Es : ℝ) (hN : 1 ≤ N) (hm : m ≤ M)
    (hM : 0 ≤ M) (he : 0 ≤ e) (α : ℝ)
    (hcomp : α*x-N^2*e*m ≤ z) (hgain : y ≤ x-(1/2)*z+EK+(1/2)*Es)
    (hEK : EK ≤ e*M) (hEs : Es ≤ e*m) : y ≤ (1-(1/2)*α)*x+2*N^2*e*M := by
  have hsq : 1 ≤ N^2 := by nlinarith
  have hsmall : e*m ≤ e*M := mul_le_mul_of_nonneg_left hm he
  have hbig : N^2*e*m ≤ N^2*e*M := mul_le_mul_of_nonneg_left hm (mul_nonneg (sq_nonneg _) he)
  have hscale : e*M ≤ N^2*e*M := by
    have hh := mul_le_mul_of_nonneg_right hsq (mul_nonneg he hM)
    nlinarith
  nlinarith

end AC02Frege.MajorityApproximationNumerics
end

section
-- Inlined Solutions.MajorityApproximationStep

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.MajorityApproximationStep

open MvPolynomial LiftSAParity ErrorSolutionSpaces OneFactorAlgebra ExcludedCumulativeCounts
open MajorityApproximationNumerics

/-- One corrected factor contracts the error count, with the explicit uniform loss budget. -/
theorem one_step {n ℓ s D Q K r : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) (hP : IsMultilinear P)
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (hr : 1 ≤ r) (hrK : r ≤ K) (hKN : 2*K < n*ℓ) (hD : Q+P.totalDegree+3*r ≤ D) :
    ∃ a : Fin s → ZMod 2,
      (cErr F ℓ D K (ML (P*(1+combination u a))) u : ℝ) ≤
        (1-etaFrac (n*ℓ) K r)*(cErr F ℓ D K P u : ℝ)+
          2*((n*ℓ : ℕ) : ℝ)^2*epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ) := by
  obtain ⟨a,ha⟩ := OneFactorGain.one_factor_gain hℓ F D Q K r s u hu P hP hrK hD
  refine ⟨a,?_⟩
  have hcomp := ErrorDegreeComparison.degree_comparison hℓ F D Q K r s u hu P hP hrK hKN (by omega)
  have hgain : (cErr F ℓ D K (ML (P*(1+combination u a))) u : ℝ) ≤
      (cErr F ℓ D K P u : ℝ)-(1/2)*(cErr F ℓ D (K-r) P u : ℝ)+
        (Eexcl n ℓ Q K : ℝ)+(1/2)*(Eexcl n ℓ Q (K-r) : ℝ) := by
    rw [cErr_ml hℓ F]
    exact ha
  have hN : K ≤ n*ℓ := by omega
  have hEK := excluded_bound n ℓ Q K K le_rfl hN
  have hEs := excluded_bound n ℓ Q K (K-r) (Nat.sub_le _ _) hN
  have hm : (monoCount (n*ℓ) (K-r) : ℝ) ≤ (monoCount (n*ℓ) K : ℝ) := by
    exact_mod_cast BooleanDegreeCounts.monoCount_mono (n*ℓ) (Nat.sub_le K r)
  have hh := contraction_numerics ((n*ℓ : ℕ) : ℝ) (monoCount (n*ℓ) K : ℝ)
    (monoCount (n*ℓ) (K-r) : ℝ) (epsExcl n ℓ Q K)
    (cErr F ℓ D K P u : ℝ) (cErr F ℓ D (K-r) P u : ℝ)
    (cErr F ℓ D K (ML (P*(1+combination u a))) u : ℝ)
    (Eexcl n ℓ Q K : ℝ) (Eexcl n ℓ Q (K-r) : ℝ)
    (by exact_mod_cast (show 1 ≤ n*ℓ by omega)) hm (Nat.cast_nonneg _) (eps_nonneg n ℓ Q K)
    ((monoCount (n*ℓ) (K-r) : ℝ)/(monoCount (n*ℓ) K : ℝ)) hcomp hgain hEK hEs
  convert hh using 1
  unfold etaFrac
  ring

end AC02Frege.MajorityApproximationStep
end

section
-- Inlined Solutions.MajorityApproximatorProducts

set_option maxHeartbeats 2000000

namespace AC02Frege.MajorityApproximatorProducts

open MvPolynomial BooleanAlgebra BooleanFlip OneFactorAlgebra

noncomputable def approximator {V : Type} {s m : ℕ} (u : Fin s → MvPolynomial V (ZMod 2))
    (a : Fin m → Fin s → ZMod 2) : MvPolynomial V (ZMod 2) :=
  ML (∏ i : Fin m, (1+combination u (a i)))

lemma approximator_degree {V : Type} {s m r : ℕ} (u : Fin s → MvPolynomial V (ZMod 2))
    (hu : ∀ i, (u i).totalDegree ≤ r) (a : Fin m → Fin s → ZMod 2) :
    (approximator u a).totalDegree ≤ m*r := by
  apply (ml_totalDegree_le _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : Fin m, r := Finset.sum_le_sum (fun i hi => factor_degree u hu (a i))
    _ = _ := by simp

lemma approximator_multilinear {V : Type} {s m : ℕ} (u : Fin s → MvPolynomial V (ZMod 2))
    (a : Fin m → Fin s → ZMod 2) : IsMultilinear (approximator u a) := ml_multilinear _

lemma approximator_succ {V : Type} [Finite V] {s m : ℕ} (u : Fin s → MvPolynomial V (ZMod 2))
    (a : Fin m → Fin s → ZMod 2) (b : Fin s → ZMod 2) :
    approximator u (Fin.cons b a) = ML (approximator u a*(1+combination u b)) := by
  have hp : (∏ i : Fin (m+1), (1+combination u ((Fin.cons b a : Fin (m+1) → Fin s → ZMod 2) i))) =
      (1+combination u b)*(∏ i : Fin m, (1+combination u (a i))) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ]
  unfold approximator
  rw [hp,ml_mul_left]
  congr 1
  ring

end AC02Frege.MajorityApproximatorProducts
end

section
-- Inlined Solutions.MajorityApproximationIteration

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.MajorityApproximationIteration

open MvPolynomial LiftSAParity ErrorSolutionSpaces ExcludedCumulativeCounts
open MajorityApproximationNumerics MajorityApproximationStep MajorityApproximatorProducts

/-- Iteration of the one-factor contraction, retaining a finite array of all chosen coefficients. -/
theorem iterate {n ℓ s D Q K r t : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (ht : 1 ≤ t) (hr : 1 ≤ r) (hrK : r ≤ K) (hKN : 2*K < n*ℓ) (hD : Q+(t+2)*r ≤ D) :
    ∃ a : Fin t → Fin s → ZMod 2,
      (cErr F ℓ D K (approximator u a) u : ℝ) ≤
        (1-etaFrac (n*ℓ) K r)^t*((hThresh F ℓ D K : ℝ)+epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ))+
          2*((n*ℓ : ℕ) : ℝ)^2*epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ)/etaFrac (n*ℓ) K r := by
  classical
  let η := etaFrac (n*ℓ) K r
  let q := 1-η
  let A := (hThresh F ℓ D K : ℝ)+epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ)
  let B := 2*((n*ℓ : ℕ) : ℝ)^2*epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ)
  have hη : 0 < η := eta_pos _ _ _
  have hq : 0 ≤ q := by have hh := eta_le_half (n*ℓ) K r; dsimp only [q,η]; linarith
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (eps_nonneg _ _ _ _)) (Nat.cast_nonneg _)
  have hBη : 0 ≤ B/η := div_nonneg hB hη.le
  have hinit : (cErr F ℓ D K 1 u : ℝ) ≤ A := by
    have hi := InitialErrorCount.initial_count hℓ F u (fun i => (hu i).2) (Q := Q) (K := K) (D := D)
      (by
        have hm : r ≤ (t+2)*r := by nlinarith
        omega)
    have hi' : (cErr F ℓ D K 1 u : ℝ) ≤ (hThresh F ℓ D K : ℝ)+(Eexcl n ℓ Q K : ℝ) := by exact_mod_cast hi
    have he := excluded_bound n ℓ Q K K le_rfl (by omega)
    exact hi'.trans (add_le_add le_rfl he)
  have hbuild : ∀ m, m ≤ t → ∃ a : Fin m → Fin s → ZMod 2,
      (cErr F ℓ D K (approximator u a) u : ℝ) ≤ q^m*A+B/η := by
    intro m
    induction m with
    | zero =>
      intro hm
      refine ⟨Fin.elim0,?_⟩
      have hh := hinit.trans (le_add_of_nonneg_right hBη)
      simpa only [approximator,Finset.univ_eq_empty,Finset.prod_empty,cErr_ml hℓ F,pow_zero,one_mul] using hh
    | succ m ih =>
      intro hm
      obtain ⟨a,ha⟩ := ih (by omega)
      let P := approximator u a
      have hP := approximator_multilinear u a
      have hdeg := approximator_degree u (fun i => (hu i).2) a
      have hbudget : Q+P.totalDegree+3*r ≤ D := by
        have hb : Q+m*r+3*r ≤ Q+(t+2)*r := by nlinarith
        exact (Nat.add_le_add_right (Nat.add_le_add_left hdeg Q) _).trans (hb.trans hD)
      obtain ⟨b,hb⟩ := one_step hℓ F P hP u hu hr hrK hKN hbudget
      refine ⟨Fin.cons b a,?_⟩
      rw [approximator_succ]
      calc
        _ ≤ q*(cErr F ℓ D K P u : ℝ)+B := hb
        _ ≤ q*(q^m*A+B/η)+B := add_le_add (mul_le_mul_of_nonneg_left ha hq) le_rfl
        _ = q^(m+1)*A+B/η := by
          rw [pow_succ]
          dsimp only [q]
          field_simp [hη.ne']
          ring
  exact hbuild t le_rfl

end AC02Frege.MajorityApproximationIteration
end

section
-- Inlined Solutions.MajorityApproximation

set_option maxHeartbeats 2000000

namespace AC02Frege.MajorityApproximation

open MvPolynomial LiftSAParity MajorityApproximationIteration MajorityApproximationNumerics
open MajorityApproximatorProducts ExcludedCumulativeCounts

theorem approximation {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (D Q K r t s : ℕ) (u : Fin s → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (ht : 1 ≤ t) (hr : 1 ≤ r) (hrK : r ≤ K) (hKN : 2 * K < n * ℓ) (hD : Q + (t + 2) * r ≤ D) :
    ∃ a : Fin t → Fin s → ZMod 2,
      (cErr F ℓ D K (ML (∏ ν : Fin t, (1 + ∑ i, a ν i • u i))) u : ℝ) ≤
        Real.exp (-(etaFrac (n * ℓ) K r * t)) *
            ((hThresh F ℓ D K : ℝ) + epsExcl n ℓ Q K * (monoCount (n * ℓ) K : ℝ))
          + 2 * ((n * ℓ : ℕ) : ℝ) ^ 2 * epsExcl n ℓ Q K * (monoCount (n * ℓ) K : ℝ)
            / etaFrac (n * ℓ) K r  := by
  obtain ⟨a,ha⟩ := iterate hℓ F u hu ht hr hrK hKN hD
  refine ⟨a,?_⟩
  let η := etaFrac (n*ℓ) K r
  have hη : η ≤ (1/2 : ℝ) := eta_le_half _ _ _
  have hq : 0 ≤ 1-η := by linarith
  have hpow : (1-η)^t ≤ Real.exp (-(η*t)) := by
    calc
      _ ≤ Real.exp (-η)^t := pow_le_pow_left₀ hq (Real.one_sub_le_exp_neg η) t
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hA : 0 ≤ (hThresh F ℓ D K : ℝ)+epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ) :=
    add_nonneg (Nat.cast_nonneg _) (mul_nonneg (eps_nonneg _ _ _ _) (Nat.cast_nonneg _))
  change (cErr F ℓ D K (approximator u a) u : ℝ) ≤ _
  exact ha.trans (add_le_add (mul_le_mul_of_nonneg_right hpow hA) le_rfl)

end AC02Frege.MajorityApproximation
end

section
-- Inlined Solutions.FiniteSetApproximation

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.FiniteSetApproximation

open MvPolynomial LiftSAParity FiniteErrorFamilies MajorityApproximationNumerics ExcludedCumulativeCounts

noncomputable def errorBound {n : ℕ} (F : CNF (Fin n)) (ℓ D Q K r t : ℕ) : ℝ :=
  Real.exp (-(etaFrac (n*ℓ) K r*t))*
    ((hThresh F ℓ D K : ℝ)+epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ))+
    2*((n*ℓ : ℕ) : ℝ)^2*epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ)/etaFrac (n*ℓ) K r

lemma errorBound_nonneg {n : ℕ} (F : CNF (Fin n)) (ℓ D Q K r t : ℕ) :
    0 ≤ errorBound F ℓ D Q K r t := by
  unfold errorBound
  have he := eps_nonneg n ℓ Q K
  have hη := eta_pos (n*ℓ) K r
  positivity

theorem finite_set {n ℓ D Q K r t : ℕ} {I : Type} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (S : Finset I) (x : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hx : ∀ i ∈ S, IsMultilinear (x i) ∧ (x i).totalDegree ≤ r)
    (ht : 1 ≤ t) (hr : 1 ≤ r) (hrK : r ≤ K) (hKN : 2*K < n*ℓ) (hD : Q+(t+2)*r ≤ D) :
    ∃ b : Fin t → I → ZMod 2,
      (FiniteErrorFamilies.rank hℓ F D K S (ML (∏ ν, (1+∑ i ∈ S, b ν i • x i))) x : ℝ) ≤
        errorBound F ℓ D Q K r t := by
  classical
  let e := Fintype.equivFin S
  obtain ⟨a,ha⟩ := MajorityApproximation.approximation hℓ F D Q K r t (Fintype.card S)
    (fun j => x (enumerate S j)) (fun j => hx _ (enumerate_mem S j)) ht hr hrK hKN hD
  let b : Fin t → I → ZMod 2 := fun ν i => if hi : i ∈ S then a ν (e ⟨i,hi⟩) else 0
  have hsum (ν : Fin t) : (∑ i ∈ S, b ν i • x i) = ∑ j, a ν j • x (enumerate S j) := by
    rw [← Finset.sum_coe_sort S]
    apply Fintype.sum_equiv e
    intro i
    dsimp only [b]
    rw [dif_pos i.2]
    simp only [enumerate,e,Equiv.symm_apply_apply]
  refine ⟨b,?_⟩
  rw [rank_eq_cErr]
  have heq : ML (∏ ν, (1+∑ i ∈ S, b ν i • x i)) =
      ML (∏ ν, (1+∑ j, a ν j • x (enumerate S j))) := by
    congr 1
    apply Finset.prod_congr rfl
    intro ν hν
    rw [hsum]
  rw [heq]
  exact ha

end AC02Frege.FiniteSetApproximation
end

section
-- Inlined Solutions.ApproximantProducts

set_option maxHeartbeats 2000000

namespace AC02Frege.ApproximantProducts

open MvPolynomial BooleanFlip

noncomputable def product {V I : Type} (S : Finset I) (x : I → MvPolynomial V (ZMod 2))
    {m : ℕ} (a : Fin m → I → ZMod 2) : MvPolynomial V (ZMod 2) :=
  ∏ ν, (1 + ∑ i ∈ S, a ν i • x i)

lemma product_degree {V I : Type} (S : Finset I) (x : I → MvPolynomial V (ZMod 2))
    {m r : ℕ} (hx : ∀ i ∈ S, (x i).totalDegree ≤ r) (a : Fin m → I → ZMod 2) :
    (product S x a).totalDegree ≤ m*r := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _ν : Fin m, r := by
      apply Finset.sum_le_sum
      intro ν hν
      apply (totalDegree_add _ _).trans
      apply max_le (by simp)
      apply totalDegree_finsetSum_le
      intro i hi
      exact (totalDegree_smul_le _ _).trans (hx i hi)
    _ = _ := by simp

/-- Telescoping the product gives bounded-degree coefficients of its complement. -/
lemma complement_certificate {V I : Type} (S : Finset I)
    (x : I → MvPolynomial V (ZMod 2)) {m r : ℕ}
    (hx : ∀ i ∈ S, (x i).totalDegree ≤ r) (a : Fin m → I → ZMod 2) :
    ∃ v : I → MvPolynomial V (ZMod 2),
      1 + product S x a = ∑ i ∈ S, v i * x i ∧
      ∀ i, (v i).totalDegree ≤ (m-1)*r := by
  classical
  induction m with
  | zero =>
    refine ⟨fun _ => 0, ?_, fun _ => by simp⟩
    simp [product, CharTwo.add_self_eq_zero]
  | succ m ih =>
    obtain ⟨v,hv,hd⟩ := ih (fun ν => a ν.succ)
    let p := product S x (fun ν : Fin m => a ν.succ)
    have hp : p.totalDegree ≤ m*r := product_degree S x hx _
    have he : product S x a = (1 + ∑ i ∈ S, a 0 i • x i)*p := by
      unfold product
      rw [Fin.prod_univ_succ]
      rfl
    refine ⟨fun i => v i + a 0 i • p, ?_, ?_⟩
    · calc
        _ = (1+p) + p*(∑ i ∈ S, a 0 i • x i) := by rw [he]; ring
        _ = _ := by
          rw [hv]
          simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, add_mul, smul_mul_assoc,
            mul_smul_comm, mul_comm p]
    · intro i
      apply (totalDegree_add _ _).trans
      apply max_le
      · exact (hd i).trans (Nat.mul_le_mul_right r (by omega))
      · simpa only [Nat.add_sub_cancel] using (totalDegree_smul_le (a 0 i) p).trans hp

end AC02Frege.ApproximantProducts
end

section
-- Inlined Solutions.ApproximantBounds

set_option maxHeartbeats 2000000

namespace AC02Frege.ApproximantBounds

open MvPolynomial BooleanAlgebra BooleanFlip ApproximantProducts

variable {V : Type} [DecidableEq V] {tin tout : ℕ} (Φ : Approx V tin tout)

@[simp] lemma A_empty : Φ.A ∅ = 1 := by simp [Approx.A]

@[simp] lemma A_singleton (u : MvPolynomial V (ZMod 2)) : Φ.A {u} = u := by
  simp only [Approx.A, Finset.singleton_ne_empty, ↓reduceIte]
  split_ifs with h
  · exact (Finset.singleton_injective h.choose_spec).symm
  · exact (h ⟨u,rfl⟩).elim

lemma A_degree {b : ℕ} (htin : 1 ≤ tin) (T : Term V)
    (hT : ∀ u ∈ T, u.totalDegree ≤ b) : (Φ.A T).totalDegree ≤ b*tin := by
  classical
  unfold Approx.A
  split_ifs with h0 h1
  · simp
  · have hu : h1.choose ∈ T := by
      exact (show ({h1.choose} : Term V) ⊆ T from le_of_eq h1.choose_spec.symm)
        (Finset.mem_singleton_self _)
    exact (hT _ hu).trans (by nlinarith)
  · apply (ml_totalDegree_le _).trans
    have hx : ∀ u ∈ T, (1+u).totalDegree ≤ b := by
      intro u hu
      exact (totalDegree_add _ _).trans (max_le (by simp) (hT u hu))
    exact (product_degree T (fun u => 1+u) hx (Φ.aT T)).trans_eq (Nat.mul_comm _ _)

lemma A_multilinear (T : Term V) (hT : ∀ u ∈ T, IsMultilinear u) : IsMultilinear (Φ.A T) := by
  classical
  unfold Approx.A
  split_ifs with h0 h1
  · intro s hs i
    have hs' : s = 0 := by simpa only [support_one,Finset.mem_singleton] using hs
    subst s
    simp
  · exact hT _ (by
      exact (show ({h1.choose} : Term V) ⊆ T from le_of_eq h1.choose_spec.symm)
        (Finset.mem_singleton_self _))
  · exact ml_multilinear _

lemma P_degree {b : ℕ} (htin : 1 ≤ tin) (L : Line V)
    (hL : ∀ T ∈ L, ∀ u ∈ T, u.totalDegree ≤ b) : (Φ.P L).totalDegree ≤ b*tin*tout := by
  apply (ml_totalDegree_le _).trans
  exact (product_degree L (Φ.A) (fun T hT => A_degree Φ htin T (hL T hT))
    (Φ.aL L)).trans_eq (Nat.mul_comm _ _)

lemma P_multilinear (L : Line V) : IsMultilinear (Φ.P L) := ml_multilinear _

@[simp] lemma P_empty : Φ.P ∅ = 1 := by
  simp only [Approx.P,Finset.sum_empty,add_zero,Finset.prod_const_one]
  exact ml_of_multilinear _ (by
    intro s hs i
    have hs' : s = 0 := by simpa only [support_one,Finset.mem_singleton] using hs
    subst s
    simp)

lemma A_certificate [Finite V] {b : ℕ} (T : Term V)
    (hT : ∀ u ∈ T, u.totalDegree ≤ b) :
    ∃ v : MvPolynomial V (ZMod 2) → MvPolynomial V (ZMod 2),
      ML (1+Φ.A T) = ML (∑ u ∈ T, v u*(1+u)) ∧
      ∀ u, (v u).totalDegree ≤ b*tin-b := by
  classical
  by_cases h0 : T = ∅
  · subst T
    refine ⟨fun _ => 0,?_,fun _ => by simp⟩
    simp [CharTwo.add_self_eq_zero]
  by_cases h1 : ∃ u, T = {u}
  · obtain ⟨u,rfl⟩ := h1
    refine ⟨fun _ => 1,?_,fun _ => by simp⟩
    simp
  · have hx : ∀ u ∈ T, (1+u).totalDegree ≤ b := by
      intro u hu
      exact (totalDegree_add _ _).trans (max_le (by simp) (hT u hu))
    obtain ⟨v,hv,hd⟩ := complement_certificate T (fun u => 1+u) hx (Φ.aT T)
    refine ⟨v,?_,?_⟩
    · simp only [Approx.A,h0,h1,↓reduceDIte,↓reduceIte]
      change ML (1+ML (product T (fun u => 1+u) (Φ.aT T))) = _
      rw [map_add,ml_idempotent,← map_add,hv]
    · intro u
      exact (hd u).trans_eq (by rw [Nat.sub_mul]; simp [Nat.mul_comm])

lemma P_certificate {b : ℕ} (htin : 1 ≤ tin) (L : Line V)
    (hL : ∀ T ∈ L, ∀ u ∈ T, u.totalDegree ≤ b) :
    ∃ v : Term V → MvPolynomial V (ZMod 2),
      ML (1+Φ.P L) = ML (∑ T ∈ L, v T*Φ.A T) ∧
      ∀ T, (v T).totalDegree ≤ b*tin*tout-b*tin := by
  obtain ⟨v,hv,hd⟩ := complement_certificate L (Φ.A)
    (fun T hT => A_degree Φ htin T (hL T hT)) (Φ.aL L)
  refine ⟨v,?_,?_⟩
  · change ML (1+ML (product L (Φ.A) (Φ.aL L))) = _
    rw [map_add,ml_idempotent,← map_add]
    exact congrArg ML hv
  · intro T
    exact (hd T).trans_eq (by rw [Nat.sub_mul]; simp [Nat.mul_comm])

end AC02Frege.ApproximantBounds
end

section
-- Inlined Solutions.WeightedConsequence

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.WeightedConsequence

open MvPolynomial LiftSAParity MajorityQuotient MajorityFunctionCongruence BooleanAlgebra BooleanFlip

def Valid {n ℓ : ℕ} (F : CNF (Fin n)) (D : ℕ)
    (f p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : Prop := f*p ∈ CHat F ℓ D

variable {n ℓ D : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
  (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))

include hℓ

lemma valid_congr (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (h : ML p = ML q) : Valid F D f p ↔ Valid F D f q := by
  apply chat_congr hℓ F
  rw [← ml_mul_right f p, ← ml_mul_right f q, h]

lemma valid_eval (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (h : ∀ x : (Fin n × Fin ℓ) → ZMod 2, eval x p = eval x q) :
    Valid F D f p ↔ Valid F D f q := by
  apply valid_congr hℓ F f
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simpa only [eval_ml] using h x

@[simp] lemma valid_zero : Valid F D f 0 := by
  apply (remainder_zero_iff hℓ F _).mp
  simp [mul_zero]

lemma valid_complement (p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    Valid F D f ((1+p)*q*p) := by
  have hc : ML (p*(1+p)) = 0 := by
    rw [mul_add,mul_one,map_add,MajorityQuotient.ml_square,CharTwo.add_self_eq_zero]
  apply (valid_congr hℓ F f _ 0 ?_).mpr (valid_zero hℓ F f)
  calc
    _ = ML (q*(p*(1+p))) := by congr 1; ring
    _ = ML (q*ML (p*(1+p))) := (ml_mul_right _ _).symm
    _ = _ := by rw [hc,mul_zero]

lemma valid_add {p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)}
    (hp : Valid F D f p) (hq : Valid F D f q) : Valid F D f (p+q) := by
  apply (remainder_zero_iff hℓ F _).mp
  rw [mul_add,map_add,(remainder_zero_iff hℓ F _).mpr hp,(remainder_zero_iff hℓ F _).mpr hq,add_zero]

lemma valid_sum {I : Type} (S : Finset I) (p : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hp : ∀ i ∈ S, Valid F D f (p i)) : Valid F D f (∑ i ∈ S, p i) := by
  apply (remainder_zero_iff hℓ F _).mp
  rw [Finset.mul_sum,map_sum]
  exact Finset.sum_eq_zero (fun i hi => (remainder_zero_iff hℓ F _).mpr (hp i hi))

lemma valid_add_cancel {p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)}
    (hpq : Valid F D f (p+q)) (hq : Valid F D f q) : Valid F D f p := by
  have hh := valid_add hℓ F f hpq hq
  simpa only [add_assoc,CharTwo.add_self_eq_zero,add_zero] using hh

lemma valid_mul {Q a b : ℕ} (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    {p q : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)}
    (hp : Valid F D f p) (hdp : p.totalDegree ≤ a) (hdq : q.totalDegree ≤ b)
    (hD : Q+a+b ≤ D) : Valid F D f (p*q) := by
  have hpa : (ML p).totalDegree ≤ a := (ml_totalDegree_le _).trans hdp
  have hqb : (ML q).totalDegree ≤ b := (ml_totalDegree_le _).trans hdq
  have hpa' : ((ML p).totalDegree : WithBot ℕ) ≤ (a : WithBot ℕ) := by exact_mod_cast hpa
  have hqb' : ((ML q).totalDegree : WithBot ℕ) ≤ (b : WithBot ℕ) := by exact_mod_cast hqb
  have hb := (degree_estimate hℓ f p).trans (add_le_add hf hpa')
  have hD' : (Q : WithBot ℕ)+(a : WithBot ℕ)+(b : WithBot ℕ) ≤ (D : WithBot ℕ) := by exact_mod_cast hD
  have hc := degree_preserves hℓ F (f*p) q hp ((add_le_add hb hqb').trans hD')
  simpa only [Valid,mul_assoc] using hc

lemma valid_certificate {I : Type} (S : Finset I) {Q a b : ℕ}
    (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (x v : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (he : ML p = ML (∑ i ∈ S, v i*x i))
    (hx : ∀ i ∈ S, Valid F D f (x i))
    (hdx : ∀ i ∈ S, (x i).totalDegree ≤ a) (hdv : ∀ i ∈ S, (v i).totalDegree ≤ b)
    (hD : Q+a+b ≤ D) : Valid F D f p := by
  apply (valid_congr hℓ F f _ _ he).mpr
  apply valid_sum hℓ F f
  intro i hi
  rw [mul_comm]
  exact valid_mul hℓ F f hf (hx i hi) (hdx i hi) (hdv i hi) hD

end AC02Frege.WeightedConsequence
end

section
-- Inlined Solutions.TwoLevelApproximationChoice

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.TwoLevelApproximationChoice

open MvPolynomial LiftSAParity BooleanAlgebra ApproximantBounds FiniteSetApproximation WeightedConsequence

noncomputable def termPoly {V : Type} [DecidableEq V] {tin : ℕ} (T : Term V)
    (a : Fin tin → MvPolynomial V (ZMod 2) → ZMod 2) : MvPolynomial V (ZMod 2) :=
  (⟨fun _ => a,fun _ _ _ => 0⟩ : Approx V tin 0).A T

noncomputable def linePoly {V : Type} {tout : ℕ} (A : Term V → MvPolynomial V (ZMod 2))
    (L : Line V) (a : Fin tout → Term V → ZMod 2) : MvPolynomial V (ZMod 2) :=
  ML (∏ ν, (1+∑ T ∈ L, a ν T • A T))

theorem term_choice {n ℓ D Q K b tin : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (T : Term (Fin n × Fin ℓ)) (hT : ∀ u ∈ T, Allowed b u)
    (htin : 1 ≤ tin) (hb : 1 ≤ b) (hbK : b ≤ K) (hKN : 2*K < n*ℓ)
    (hD : Q+(tin+2)*b ≤ D) :
    ∃ a : Fin tin → MvPolynomial (Fin n × Fin ℓ) (ZMod 2) → ZMod 2,
      (FiniteErrorFamilies.rank hℓ F D K T (termPoly T a) (fun u => 1+u) : ℝ) ≤
        errorBound F ℓ D Q K b tin := by
  classical
  by_cases h0 : T = ∅
  · subst T
    refine ⟨fun _ _ => 0,?_⟩
    rw [FiniteErrorFamilies.rank_zero_of_satisfied hℓ F ∅ _ _ (by simp)]
    simpa only [Nat.cast_zero] using errorBound_nonneg F ℓ D Q K b tin
  by_cases h1 : ∃ u, T = {u}
  · obtain ⟨u,rfl⟩ := h1
    refine ⟨fun _ _ => 0,?_⟩
    have hz : FiniteErrorFamilies.rank hℓ F D K {u}
        (termPoly (tin := tin) {u} (fun _ _ => 0)) (fun u => 1+u) = 0 := by
      apply FiniteErrorFamilies.rank_zero_of_satisfied
      intro f hf i hi
      have hi' : i = u := Finset.mem_singleton.mp hi
      subst i
      simp only [termPoly,A_singleton]
      have hh := valid_complement hℓ F f u 1 (D := D)
      have heq : f*u*(1+u) = f*((1+u)*1*u) := by ring
      rw [heq]
      exact hh
    rw [hz]
    simpa only [Nat.cast_zero] using errorBound_nonneg F ℓ D Q K b tin
  · have hone : IsMultilinear (1 : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) := by
      intro s hs i
      have hs' : s = 0 := by simpa only [support_one,Finset.mem_singleton] using hs
      subst s
      simp
    have hx : ∀ u ∈ T, IsMultilinear (1+u) ∧ (1+u).totalDegree ≤ b := by
      intro u hu
      exact ⟨MajorityCoefficientAlgebra.multilinear_add 1 u hone (hT u hu).1,
        (totalDegree_add _ _).trans (max_le (by simp) (hT u hu).2)⟩
    obtain ⟨a,ha⟩ := finite_set hℓ F T (fun u => 1+u) hx htin hb hbK hKN hD
    refine ⟨a,?_⟩
    have heq : termPoly T a = ML (∏ ν, (1+∑ u ∈ T, a ν u • (1+u))) := by
      simp only [termPoly,Approx.A,h0,h1,↓reduceDIte,↓reduceIte]
    rw [heq]
    exact ha

theorem line_choice {n ℓ D Q K b tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (L : Line (Fin n × Fin ℓ))
    (hL : ∀ T ∈ L, ∀ u ∈ T, Allowed b u)
    (htin : 1 ≤ tin) (htout : 1 ≤ tout) (hR : 1 ≤ b*tin) (hRK : b*tin ≤ K)
    (hKN : 2*K < n*ℓ) (hD : Q+(tout+2)*(b*tin) ≤ D) :
    ∃ a : Fin tout → Term (Fin n × Fin ℓ) → ZMod 2,
      (FiniteErrorFamilies.rank hℓ F D K L (linePoly Φ.A L a) Φ.A : ℝ) ≤
        errorBound F ℓ D Q K (b*tin) tout := by
  apply finite_set hℓ F L Φ.A _ htout hR hRK hKN hD
  intro T hT
  exact ⟨A_multilinear Φ T (fun u hu => (hL T hT u hu).1),
    A_degree Φ htin T (fun u hu => (hL T hT u hu).2)⟩

/-- Choose each distinct term once, and then choose all line approximants using those terms. -/
theorem choose_both {n ℓ D Q K b tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (htin : 1 ≤ tin) (htout : 1 ≤ tout) (hb : 1 ≤ b) (hRK : b*tin ≤ K)
    (hKN : 2*K < n*ℓ) (hDin : Q+(tin+2)*b ≤ D) (hDout : Q+(tout+2)*(b*tin) ≤ D) :
    ∃ Φ : Approx (Fin n × Fin ℓ) tin tout,
      (∀ T, (∀ u ∈ T, Allowed b u) →
        (FiniteErrorFamilies.rank hℓ F D K T (Φ.A T) (fun u => 1+u) : ℝ) ≤
          errorBound F ℓ D Q K b tin) ∧
      (∀ L, (∀ T ∈ L, ∀ u ∈ T, Allowed b u) →
        (FiniteErrorFamilies.rank hℓ F D K L (Φ.P L) Φ.A : ℝ) ≤
          (L.card : ℝ)*errorBound F ℓ D Q K (b*tin) tout) := by
  classical
  have hbK : b ≤ K := by nlinarith
  have hR : 1 ≤ b*tin := by nlinarith
  have hin : ∀ T : Term (Fin n × Fin ℓ),
      ∃ a : Fin tin → MvPolynomial (Fin n × Fin ℓ) (ZMod 2) → ZMod 2,
        (∀ u ∈ T, Allowed b u) →
          (FiniteErrorFamilies.rank hℓ F D K T (termPoly T a) (fun u => 1+u) : ℝ) ≤
            errorBound F ℓ D Q K b tin := by
    intro T
    by_cases hT : ∀ u ∈ T, Allowed b u
    · obtain ⟨a,ha⟩ := term_choice hℓ F T hT htin hb hbK hKN hDin
      exact ⟨a,fun _ => ha⟩
    · exact ⟨fun _ _ => 0,fun h => (hT h).elim⟩
  choose aT haT using hin
  let Φ₀ : Approx (Fin n × Fin ℓ) tin tout := ⟨aT,fun _ _ _ => 0⟩
  have hout : ∀ L : Line (Fin n × Fin ℓ),
      ∃ a : Fin tout → Term (Fin n × Fin ℓ) → ZMod 2,
        (∀ T ∈ L, ∀ u ∈ T, Allowed b u) →
          (FiniteErrorFamilies.rank hℓ F D K L (linePoly Φ₀.A L a) Φ₀.A : ℝ) ≤
            errorBound F ℓ D Q K (b*tin) tout := by
    intro L
    by_cases hL : ∀ T ∈ L, ∀ u ∈ T, Allowed b u
    · obtain ⟨a,ha⟩ := line_choice hℓ F Φ₀ L hL htin htout hR hRK hKN hDout
      exact ⟨a,fun _ => ha⟩
    · exact ⟨fun _ _ => 0,fun h => (hL h).elim⟩
  choose aL haL using hout
  let Φ : Approx (Fin n × Fin ℓ) tin tout := ⟨aT,aL⟩
  refine ⟨Φ,?_,?_⟩
  · intro T hT
    exact haT T hT
  · intro L hL
    by_cases h0 : L = ∅
    · subst L
      have hz := FiniteErrorFamilies.rank_zero_of_satisfied hℓ F ∅ (Φ.P ∅) Φ.A
        (D := D) (K := K) (by simp)
      simp only [hz,Finset.card_empty,Nat.cast_zero,zero_mul,le_refl]
    · have hcard : (1 : ℝ) ≤ L.card := by
        exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
      have he := errorBound_nonneg F ℓ D Q K (b*tin) tout
      calc
        _ ≤ errorBound F ℓ D Q K (b*tin) tout := haL L hL
        _ ≤ _ := by nlinarith

end AC02Frege.TwoLevelApproximationChoice
end

section
-- Inlined Solutions.FiniteCodimensionLoss

set_option maxHeartbeats 2000000

namespace ProofComplexity.FiniteCodimensionLoss

open Module

noncomputable def codim {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (B G : Submodule K M) : ℕ := finrank K B-finrank K ↥(B ⊓ G : Submodule K M)

lemma mem_finset_inf {K M I : Type} [Field K] [AddCommGroup M] [Module K M]
    (S : Finset I) (G : I → Submodule K M) (x : M) :
    x ∈ S.inf G ↔ ∀ i ∈ S, x ∈ G i := by
  rw [Finset.inf_eq_iInf]
  simp only [Submodule.mem_iInf]

/-- Intersecting finitely many constraints costs at most the sum of their ambient codimensions. -/
theorem finset_loss {K M I : Type} [Field K] [AddCommGroup M] [Module K M]
    (B : Submodule K M) [Module.Finite K B] (S : Finset I) (G : I → Submodule K M)
    (A : Submodule K M) (hAB : A ≤ B) :
    finrank K A ≤ finrank K ↥(A ⊓ S.inf G : Submodule K M)+
      ∑ i ∈ S, (finrank K B-finrank K ↥(B ⊓ G i : Submodule K M)) := by
  classical
  induction S using Finset.induction_on generalizing A with
  | empty =>
    have he : (A ⊓ (∅ : Finset I).inf G : Submodule K M) = A := by
      rw [Finset.inf_empty,inf_top_eq]
    rw [he,Finset.sum_empty,add_zero]
  | @insert i S hi ih =>
    have hfirst := LinearSubspaceDimension.intersection_loss B A (G i) hAB
    have hrest := ih (A ⊓ G i) (inf_le_left.trans hAB)
    rw [Finset.inf_insert,Finset.sum_insert hi,← inf_assoc]
    omega

theorem codim_finset {K M I : Type} [Field K] [AddCommGroup M] [Module K M]
    (B : Submodule K M) [Module.Finite K B] (S : Finset I) (G : I → Submodule K M) :
    codim B (S.inf G) ≤ ∑ i ∈ S, codim B (G i) := by
  have hh := finset_loss B S G B le_rfl
  unfold codim
  omega

theorem codim_inf {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (B : Submodule K M) [Module.Finite K B] (A G : Submodule K M) :
    codim B (A ⊓ G) ≤ codim B A+codim B G := by
  have hh := LinearSubspaceDimension.intersection_loss B (B ⊓ A) G inf_le_left
  have hA : finrank K ↥(B ⊓ A : Submodule K M) ≤ finrank K B := Submodule.finrank_mono inf_le_left
  have hG : finrank K ↥(B ⊓ G : Submodule K M) ≤ finrank K B := Submodule.finrank_mono inf_le_left
  have he : ((B ⊓ A) ⊓ G : Submodule K M) = B ⊓ (A ⊓ G) := inf_assoc _ _ _
  rw [he] at hh
  unfold codim
  omega

end ProofComplexity.FiniteCodimensionLoss
end

section
-- Inlined Solutions.TwoLevelErrorSpaces

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.TwoLevelErrorSpaces

open Module MvPolynomial LiftSAParity GoodCoefficientSpace
open ProofComplexity.FiniteCodimensionLoss

noncomputable def innerSpace {n ℓ tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ)
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (T : Term (Fin n × Fin ℓ)) :=
  FiniteErrorFamilies.space hℓ F D T (Φ.A T) (fun u => 1+u)

noncomputable def outerSpace {n ℓ tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ)
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (L : Line (Fin n × Fin ℓ)) :=
  FiniteErrorFamilies.space hℓ F D L (Φ.P L) Φ.A

noncomputable def lineConstraints {n ℓ tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D : ℕ)
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (L : Line (Fin n × Fin ℓ)) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  L.inf (innerSpace hℓ F D Φ) ⊓ outerSpace hℓ F D Φ L

noncomputable def common {n ℓ tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D Q K : ℕ)
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (π : List (Line (Fin n × Fin ℓ))) :
    Submodule (ZMod 2) (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  (SemAC02.Ble (Fin n × Fin ℓ) K ⊓ goodSpace n ℓ Q) ⊓ π.toFinset.inf (lineConstraints hℓ F D Φ)

lemma mem_lineConstraints {n ℓ D tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (L : Line (Fin n × Fin ℓ))
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    f ∈ lineConstraints hℓ F D Φ L ↔ IsMultilinear f ∧
      (∀ T ∈ L, ∀ u ∈ T, f*Φ.A T*(1+u) ∈ CHat F ℓ D) ∧
      ∀ T ∈ L, f*Φ.P L*Φ.A T ∈ CHat F ℓ D := by
  change (f ∈ L.inf (innerSpace hℓ F D Φ) ∧ f ∈ outerSpace hℓ F D Φ L) ↔ _
  constructor
  · rintro ⟨hin,hout⟩
    have hin' := (mem_finset_inf L (innerSpace hℓ F D Φ) f).mp hin
    have hout' := (FiniteErrorFamilies.mem_space hℓ F L (Φ.P L) Φ.A f (D := D)).mp hout
    refine ⟨hout'.1,?_,hout'.2⟩
    intro T hT
    exact ((FiniteErrorFamilies.mem_space hℓ F T (Φ.A T) (fun u => 1+u) f (D := D)).mp (hin' T hT)).2
  · rintro ⟨hf,hin,hout⟩
    refine ⟨(mem_finset_inf L (innerSpace hℓ F D Φ) f).mpr ?_,?_⟩
    · intro T hT
      exact (FiniteErrorFamilies.mem_space hℓ F T (Φ.A T) (fun u => 1+u) f (D := D)).mpr ⟨hf,hin T hT⟩
    · exact (FiniteErrorFamilies.mem_space hℓ F L (Φ.P L) Φ.A f (D := D)).mpr ⟨hf,hout⟩

lemma mem_common {n ℓ D Q K tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (π : List (Line (Fin n × Fin ℓ)))
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    f ∈ common hℓ F D Q K Φ π ↔ f ∈ Vdeg (Fin n × Fin ℓ) K ∧ f ∈ WQ n ℓ Q ∧
      InnerErr F ℓ D Φ π f ∧ OuterErr F ℓ D Φ π f := by
  change ((f ∈ SemAC02.Ble (Fin n × Fin ℓ) K ∧ f ∈ goodSpace n ℓ Q) ∧
    f ∈ π.toFinset.inf (lineConstraints hℓ F D Φ)) ↔ _
  constructor
  · rintro ⟨⟨hfB,hfG⟩,hfC⟩
    have hb := (SemAC02.BooleanDegreeSpaces.mem_Ble_iff K f).mp hfB
    have hg := (mem_goodSpace hℓ f).mp hfG
    have hall := (mem_finset_inf π.toFinset (lineConstraints hℓ F D Φ) f).mp hfC
    refine ⟨hb,hg.2,?_,?_⟩
    · intro L hL
      exact ((mem_lineConstraints hℓ F Φ L f (D := D)).mp (hall L (List.mem_toFinset.mpr hL))).2.1
    · intro L hL
      exact ((mem_lineConstraints hℓ F Φ L f (D := D)).mp (hall L (List.mem_toFinset.mpr hL))).2.2
  · rintro ⟨hfB,hfG,hin,hout⟩
    refine ⟨⟨(SemAC02.BooleanDegreeSpaces.mem_Ble_iff K f).mpr hfB,
      (mem_goodSpace hℓ f).mpr ⟨hfB.1,hfG⟩⟩,?_⟩
    apply (mem_finset_inf π.toFinset (lineConstraints hℓ F D Φ) f).mpr
    intro L hL
    have hLπ := List.mem_toFinset.mp hL
    exact (mem_lineConstraints hℓ F Φ L f (D := D)).mpr ⟨hfB.1,hin L hLπ,hout L hLπ⟩

lemma family_rank_eq_codim {n ℓ D K : ℕ} {I : Type} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (S : Finset I) (P : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (x : I → MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    FiniteErrorFamilies.rank hℓ F D K S P x = codim (SemAC02.Ble (Fin n × Fin ℓ) K)
      (FiniteErrorFamilies.space hℓ F D S P x) := by
  unfold FiniteErrorFamilies.rank codim
  have hB : finrank (ZMod 2) (SemAC02.Ble (Fin n × Fin ℓ) K) = monoCount (n*ℓ) K := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using BooleanDegreeCounts.finrank_Ble (V := Fin n × Fin ℓ) K
  rw [hB]

theorem line_codim_bound {n ℓ D K tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (L : Line (Fin n × Fin ℓ)) (Ci Co : ℝ)
    (hi : ∀ T ∈ L, (FiniteErrorFamilies.rank hℓ F D K T (Φ.A T) (fun u => 1+u) : ℝ) ≤ Ci)
    (ho : (FiniteErrorFamilies.rank hℓ F D K L (Φ.P L) Φ.A : ℝ) ≤ (L.card : ℝ)*Co) :
    (codim (SemAC02.Ble (Fin n × Fin ℓ) K) (lineConstraints hℓ F D Φ L) : ℝ) ≤
      (L.card : ℝ)*(Ci+Co) := by
  classical
  let B := SemAC02.Ble (Fin n × Fin ℓ) K
  have hn := (codim_inf B (L.inf (innerSpace hℓ F D Φ)) (outerSpace hℓ F D Φ L)).trans
    (Nat.add_le_add_right (codim_finset B L (innerSpace hℓ F D Φ)) _)
  have hn' : (codim B (lineConstraints hℓ F D Φ L) : ℝ) ≤
      (∑ T ∈ L, (codim B (innerSpace hℓ F D Φ T) : ℝ))+(codim B (outerSpace hℓ F D Φ L) : ℝ) := by
    exact_mod_cast hn
  have hsum : (∑ T ∈ L, (codim B (innerSpace hℓ F D Φ T) : ℝ)) ≤ (L.card : ℝ)*Ci := by
    calc
      _ ≤ ∑ _T ∈ L, Ci := Finset.sum_le_sum (fun T hT => by
        simpa only [family_rank_eq_codim,innerSpace] using hi T hT)
      _ = _ := by simp
  have hout : (codim B (outerSpace hℓ F D Φ L) : ℝ) ≤ (L.card : ℝ)*Co := by
    simpa only [family_rank_eq_codim,outerSpace] using ho
  nlinarith

end AC02Frege.TwoLevelErrorSpaces
end

section
-- Inlined Solutions.TwoLevelCombinedRank

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.TwoLevelCombinedRank

open Module MvPolynomial LiftSAParity GoodCoefficientSpace TwoLevelErrorSpaces
open ProofComplexity.FiniteCodimensionLoss

lemma toFinset_sum_le {I : Type} [DecidableEq I] (xs : List I) (f : I → ℕ) :
    xs.toFinset.sum f ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.toFinset_cons,List.map_cons,List.sum_cons]
    by_cases hi : i ∈ xs.toFinset
    · rw [Finset.insert_eq_of_mem hi]
      exact ih.trans (by omega)
    · rw [Finset.sum_insert hi]
      exact Nat.add_le_add_left ih (f i)

lemma term_occurrences_le_size {V : Type} [DecidableEq V] (π : List (Line V)) :
    π.toFinset.sum Finset.card ≤ totalSize π := by
  apply (toFinset_sum_le π Finset.card).trans
  induction π with
  | nil => simp [totalSize]
  | cons L π ih =>
    have hL : L.card ≤ ∑ T ∈ L, (1+∑ u ∈ T, u.support.card) := by
      calc
        _ = ∑ _T ∈ L, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun T hT => by omega)
    simpa only [totalSize,List.map_cons,List.sum_cons] using Nat.add_le_add hL ih

theorem combined_rank_bound {n ℓ D Q K tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (π : List (Line (Fin n × Fin ℓ))) (Ci Co : ℝ)
    (hCi : 0 ≤ Ci) (hCo : 0 ≤ Co)
    (hi : ∀ L ∈ π, ∀ T ∈ L,
      (FiniteErrorFamilies.rank hℓ F D K T (Φ.A T) (fun u => 1+u) : ℝ) ≤ Ci)
    (ho : ∀ L ∈ π, (FiniteErrorFamilies.rank hℓ F D K L (Φ.P L) Φ.A : ℝ) ≤ (L.card : ℝ)*Co) :
    (monoCount (n*ℓ) K : ℝ)-(finrank (ZMod 2) (common hℓ F D Q K Φ π) : ℝ) ≤
      (totalSize π : ℝ)*(Ci+Co)+(Eexcl n ℓ Q K : ℝ) := by
  classical
  let B := SemAC02.Ble (Fin n × Fin ℓ) K
  let G := goodSpace n ℓ Q
  let S := π.toFinset
  let C := lineConstraints hℓ F D Φ
  have hloss := finset_loss B S C (B ⊓ G) inf_le_left
  have hexcl := excluded_codimension n ℓ Q K
  have hB : finrank (ZMod 2) B = monoCount (n*ℓ) K := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using BooleanDegreeCounts.finrank_Ble (V := Fin n × Fin ℓ) K
  have hn : monoCount (n*ℓ) K ≤ finrank (ZMod 2) (common hℓ F D Q K Φ π)+
      (∑ L ∈ S, codim B (C L))+Eexcl n ℓ Q K := by
    change finrank (ZMod 2) B = finrank (ZMod 2) ↥(B ⊓ G : Submodule _ _)+Eexcl n ℓ Q K at hexcl
    change finrank (ZMod 2) ↥(B ⊓ G : Submodule _ _) ≤
      finrank (ZMod 2) (common hℓ F D Q K Φ π)+(∑ L ∈ S, codim B (C L)) at hloss
    omega
  have hn' : (monoCount (n*ℓ) K : ℝ) ≤ (finrank (ZMod 2) (common hℓ F D Q K Φ π) : ℝ)+
      (∑ L ∈ S, (codim B (C L) : ℝ))+(Eexcl n ℓ Q K : ℝ) := by exact_mod_cast hn
  have hsum : (∑ L ∈ S, (codim B (C L) : ℝ)) ≤ (totalSize π : ℝ)*(Ci+Co) := by
    calc
      _ ≤ ∑ L ∈ S, (L.card : ℝ)*(Ci+Co) := by
        apply Finset.sum_le_sum
        intro L hL
        have hLπ : L ∈ π := List.mem_toFinset.mp hL
        exact line_codim_bound hℓ F Φ L Ci Co (hi L hLπ) (ho L hLπ)
      _ = ((S.sum Finset.card : ℕ) : ℝ)*(Ci+Co) := by rw [Nat.cast_sum,Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast term_occurrences_le_size π) (add_nonneg hCi hCo)
  linarith

lemma dimSpan_common {n ℓ D Q K tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (π : List (Line (Fin n × Fin ℓ))) :
    dimSpan {f | f ∈ Vdeg (Fin n × Fin ℓ) K ∧ f ∈ WQ n ℓ Q ∧
      InnerErr F ℓ D Φ π f ∧ OuterErr F ℓ D Φ π f} =
        finrank (ZMod 2) (common hℓ F D Q K Φ π) := by
  have hs : {f | f ∈ Vdeg (Fin n × Fin ℓ) K ∧ f ∈ WQ n ℓ Q ∧
      InnerErr F ℓ D Φ π f ∧ OuterErr F ℓ D Φ π f} =
      (↑(common hℓ F D Q K Φ π) : Set (MvPolynomial (Fin n × Fin ℓ) (ZMod 2))) := by
    ext f
    exact (mem_common hℓ F Φ π f).symm
  unfold dimSpan
  rw [hs,Submodule.span_eq]

end AC02Frege.TwoLevelCombinedRank
end

section
-- Inlined Solutions.ApproximantRelations

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ApproximantRelations

open MvPolynomial LiftSAParity BooleanAlgebra BooleanFlip ApproximantBounds WeightedConsequence

lemma multiply_certificate {V I : Type} [Finite V] (S : Finset I)
    (p q : MvPolynomial V (ZMod 2)) (x v : I → MvPolynomial V (ZMod 2))
    (he : ML q = ML (∑ i ∈ S, v i*x i)) :
    ML (p*q) = ML (∑ i ∈ S, v i*(p*x i)) := by
  calc
    _ = ML (p*ML q) := (ml_mul_right _ _).symm
    _ = ML (p*ML (∑ i ∈ S, v i*x i)) := by rw [he]
    _ = ML (p*(∑ i ∈ S, v i*x i)) := ml_mul_right _ _
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

variable {n ℓ D Q b tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout)
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))

include hℓ

lemma term_projection (htin : 1 ≤ tin) (T U : Term (Fin n × Fin ℓ)) (hUT : U ⊆ T)
    (hT : ∀ u ∈ T, u.totalDegree ≤ b) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hinner : ∀ u ∈ T, Valid F D f (Φ.A T*(1+u))) (hD : Q+2*(b*tin) ≤ D) :
    Valid F D f (Φ.A T*(1+Φ.A U)) := by
  obtain ⟨v,hv,hdv⟩ := A_certificate Φ U (fun u hu => hT u (hUT hu))
  have hAT := A_degree Φ htin T hT
  have hbR : b ≤ b*tin := by nlinarith
  apply valid_certificate hℓ F f U hf _ (fun u => Φ.A T*(1+u)) v
    (multiply_certificate U (Φ.A T) _ _ _ hv)
  · intro u hu
    exact hinner u (hUT hu)
  · intro u hu
    exact (totalDegree_mul _ _).trans (Nat.add_le_add hAT
      ((totalDegree_add _ _).trans (max_le (by simp) (hT u (hUT hu)))))
  · intro u hu
    exact hdv u
  · omega

lemma term_conjunction (htin : 1 ≤ tin) (T U : Term (Fin n × Fin ℓ))
    (hT : ∀ u ∈ T, u.totalDegree ≤ b) (hU : ∀ u ∈ U, u.totalDegree ≤ b)
    (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hinnerT : ∀ u ∈ T, Valid F D f (Φ.A T*(1+u)))
    (hinnerU : ∀ u ∈ U, Valid F D f (Φ.A U*(1+u)))
    (hinnerV : ∀ u ∈ T ∪ U, Valid F D f (Φ.A (T ∪ U)*(1+u)))
    (hD : Q+3*(b*tin) ≤ D) :
    Valid F D f (Φ.A (T ∪ U)+Φ.A T*Φ.A U) := by
  classical
  let R := b*tin
  let V := T ∪ U
  have hbR : b ≤ R := by dsimp [R]; nlinarith
  have hAT : (Φ.A T).totalDegree ≤ R := A_degree Φ htin T hT
  have hAU : (Φ.A U).totalDegree ≤ R := A_degree Φ htin U hU
  have hV : ∀ u ∈ V, u.totalDegree ≤ b := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hT u hu
    · exact hU u hu
  have hAV : (Φ.A V).totalDegree ≤ R := A_degree Φ htin V hV
  have hpart : Valid F D f ((Φ.A T*Φ.A U)*(1+Φ.A V)) := by
    obtain ⟨v,hv,hdv⟩ := A_certificate Φ V hV
    apply valid_certificate hℓ F f V hf _ (fun u => (Φ.A T*Φ.A U)*(1+u)) v
      (multiply_certificate V (Φ.A T*Φ.A U) _ _ _ hv)
    · intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · have hdx : (Φ.A T*(1+u)).totalDegree ≤ R+b :=
          (totalDegree_mul _ _).trans (Nat.add_le_add hAT
            ((totalDegree_add _ _).trans (max_le (by simp) (hT u hu))))
        have hh := valid_mul hℓ F f hf (hinnerT u hu) hdx hAU
          (show Q+(R+b)+R ≤ D by dsimp [R]; omega)
        have heq : (Φ.A T*Φ.A U)*(1+u) = (Φ.A T*(1+u))*Φ.A U := by ring
        rw [heq]
        exact hh
      · have hdx : (Φ.A U*(1+u)).totalDegree ≤ R+b :=
          (totalDegree_mul _ _).trans (Nat.add_le_add hAU
            ((totalDegree_add _ _).trans (max_le (by simp) (hU u hu))))
        have hh := valid_mul hℓ F f hf (hinnerU u hu) hdx hAT
          (show Q+(R+b)+R ≤ D by dsimp [R]; omega)
        have heq : (Φ.A T*Φ.A U)*(1+u) = (Φ.A U*(1+u))*Φ.A T := by ring
        rw [heq]
        exact hh
    · intro u hu
      exact (totalDegree_mul _ _).trans (Nat.add_le_add
        ((totalDegree_mul _ _).trans (Nat.add_le_add hAT hAU))
        ((totalDegree_add _ _).trans (max_le (by simp) (hV u hu))))
    · intro u hu
      exact hdv u
    · dsimp [R] at *
      omega
  have hVT := term_projection hℓ F Φ f htin V T Finset.subset_union_left hV hf hinnerV
    (show Q+2*(b*tin) ≤ D by omega)
  have hVU := term_projection hℓ F Φ f htin V U Finset.subset_union_right hV hf hinnerV
    (show Q+2*(b*tin) ≤ D by omega)
  have hdx : (Φ.A V*(1+Φ.A U)).totalDegree ≤ R+R :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hAV
      ((totalDegree_add _ _).trans (max_le (by simp) hAU)))
  have hVU' := valid_mul hℓ F f hf hVU hdx hAT
    (show Q+(R+R)+R ≤ D by dsimp [R]; omega)
  have hsum := valid_add hℓ F f (valid_add hℓ F f hVT hVU') hpart
  have heq : Φ.A (T ∪ U)+Φ.A T*Φ.A U =
      Φ.A V*(1+Φ.A T)+(Φ.A V*(1+Φ.A U))*Φ.A T+
        (Φ.A T*Φ.A U)*(1+Φ.A V) := by
    dsimp [V]
    ring_nf
    simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]
  rw [heq]
  exact hsum

end AC02Frege.ApproximantRelations
end

section
-- Inlined Solutions.ApproximantLineTransport

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ApproximantLineTransport

open MvPolynomial LiftSAParity BooleanAlgebra BooleanFlip ApproximantBounds
open WeightedConsequence ApproximantRelations

variable {n ℓ D Q b tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout)
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))

include hℓ

/-- A bounded telescoping calculation transports a known premise through a chosen multiplier. -/
lemma line_absorb (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (L₀ L : Line (Fin n × Fin ℓ)) (m : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hL₀ : ∀ T ∈ L₀, ∀ u ∈ T, u.totalDegree ≤ b)
    (hL : ∀ T ∈ L, ∀ u ∈ T, u.totalDegree ≤ b)
    (hm : m.totalDegree ≤ b*tin) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hprem : Valid F D f (Φ.P L₀))
    (hx : ∀ T ∈ L₀, Valid F D f ((m*Φ.P L)*Φ.A T))
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D) : Valid F D f (m*Φ.P L) := by
  let R := b*tin
  let S := R*tout
  have hRS : R ≤ S := by dsimp [S]; nlinarith
  have hP₀ : (Φ.P L₀).totalDegree ≤ S := P_degree Φ htin L₀ hL₀
  have hP : (Φ.P L).totalDegree ≤ S := P_degree Φ htin L hL
  have hmP : (m*Φ.P L).totalDegree ≤ R+S :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hm hP)
  have hfirst := valid_mul hℓ F f hf hprem hP₀ hmP
    (show Q+S+(R+S) ≤ D by dsimp [S,R] at *; omega)
  have hsecond : Valid F D f ((m*Φ.P L)*(1+Φ.P L₀)) := by
    obtain ⟨v,hv,hdv⟩ := P_certificate Φ htin L₀ hL₀
    apply valid_certificate hℓ F f L₀ hf _ (fun T => (m*Φ.P L)*Φ.A T) v
      (multiply_certificate L₀ (m*Φ.P L) _ _ _ hv)
    · exact hx
    · intro T hT
      exact (totalDegree_mul _ _).trans (Nat.add_le_add hmP (A_degree Φ htin T (hL₀ T hT)))
    · intro T hT
      exact hdv T
    · dsimp [S,R] at *
      omega
  have hsum := valid_add hℓ F f hfirst hsecond
  have heq : m*Φ.P L = Φ.P L₀*(m*Φ.P L)+(m*Φ.P L)*(1+Φ.P L₀) := by
    ring_nf
    simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]
  rw [heq]
  exact hsum

lemma remove_term (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (L₀ L : Line (Fin n × Fin ℓ)) (T : Term (Fin n × Fin ℓ))
    (hL₀ : ∀ U ∈ L₀, ∀ u ∈ U, u.totalDegree ≤ b)
    (hL : ∀ U ∈ L, ∀ u ∈ U, u.totalDegree ≤ b)
    (hT : ∀ u ∈ T, u.totalDegree ≤ b)
    (hkeep : ∀ U ∈ L₀, U ∈ L ∨ U = T) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hprem : Valid F D f (Φ.P L₀))
    (houter : ∀ U ∈ L, Valid F D f (Φ.P L*Φ.A U))
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D) :
    Valid F D f ((1+Φ.A T)*Φ.P L) := by
  have hAT := A_degree Φ htin T hT
  have hm : (1+Φ.A T).totalDegree ≤ b*tin :=
    (totalDegree_add _ _).trans (max_le (by simp) hAT)
  apply line_absorb hℓ F Φ f htin htout L₀ L _ hL₀ hL hm hf hprem _ hD
  intro U hU
  rcases hkeep U hU with hUL | rfl
  · have hdx : (Φ.P L*Φ.A U).totalDegree ≤ b*tin*tout+b*tin :=
      (totalDegree_mul _ _).trans (Nat.add_le_add (P_degree Φ htin L hL)
        (A_degree Φ htin U (hL U hUL)))
    have hh := valid_mul hℓ F f hf (houter U hUL) hdx hm
      (show Q+(b*tin*tout+b*tin)+b*tin ≤ D by omega)
    have heq : ((1+Φ.A T)*Φ.P L)*Φ.A U = (Φ.P L*Φ.A U)*(1+Φ.A T) := by ring
    rw [heq]
    exact hh
  · exact valid_complement hℓ F f (Φ.A U) (Φ.P L)

end AC02Frege.ApproximantLineTransport
end

section
-- Inlined Solutions.ApproximantStructuralRules

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ApproximantStructuralRules

open MvPolynomial LiftSAParity BooleanFlip ApproximantBounds WeightedConsequence
open ApproximantRelations ApproximantLineTransport

def Good {V : Type} (b : ℕ) (L : Line V) : Prop := ∀ T ∈ L, ∀ u ∈ T, u.totalDegree ≤ b

variable {n ℓ D Q b tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout)
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))

include hℓ

lemma weakening (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (L₀ L : Line (Fin n × Fin ℓ)) (hsub : L₀ ⊆ L)
    (hL₀ : Good b L₀) (hL : Good b L) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hprem : Valid F D f (Φ.P L₀)) (houter : ∀ T ∈ L, Valid F D f (Φ.P L*Φ.A T))
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D) : Valid F D f (Φ.P L) := by
  have hh := line_absorb hℓ F Φ f htin htout L₀ L 1 hL₀ hL (by simp) hf hprem
    (fun T hT => by simpa only [one_mul] using houter T (hsub hT)) hD
  simpa only [one_mul] using hh

lemma projection (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (A : Line (Fin n × Fin ℓ)) (T U : Term (Fin n × Fin ℓ)) (hsub : U ⊆ T)
    (hL₀ : Good b (insert T A)) (hL : Good b (insert U A))
    (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hprem : Valid F D f (Φ.P (insert T A)))
    (hinner : ∀ u ∈ T, Valid F D f (Φ.A T*(1+u)))
    (houter : ∀ W ∈ insert U A, Valid F D f (Φ.P (insert U A)*Φ.A W))
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D) : Valid F D f (Φ.P (insert U A)) := by
  classical
  let L := insert U A
  have hT := hL₀ T (Finset.mem_insert_self _ _)
  have hU := hL U (Finset.mem_insert_self _ _)
  have hAT := A_degree Φ htin T hT
  have hAU := A_degree Φ htin U hU
  have hP : (Φ.P L).totalDegree ≤ b*tin*tout := P_degree Φ htin L hL
  have hrem := remove_term hℓ F Φ f htin htout (insert T A) L T hL₀ hL hT
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact Or.inr rfl
      · exact Or.inl (Finset.mem_insert_of_mem hW)) hf hprem houter hD
  have hrel := term_projection hℓ F Φ f htin T U hsub hT hf hinner (by omega)
  have hdrel : (Φ.A T*(1+Φ.A U)).totalDegree ≤ b*tin+b*tin :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hAT
      ((totalDegree_add _ _).trans (max_le (by simp) hAU)))
  have hrelP := valid_mul hℓ F f hf hrel hdrel hP (by omega)
  have hdouter : (Φ.P L*Φ.A U).totalDegree ≤ b*tin*tout+b*tin :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hP hAU)
  have hlast := valid_mul hℓ F f hf (houter U (Finset.mem_insert_self _ _)) hdouter hAT (by omega)
  have hh := valid_add hℓ F f (valid_add hℓ F f hrem hrelP) hlast
  have heq : Φ.P L = (1+Φ.A T)*Φ.P L+(Φ.A T*(1+Φ.A U))*Φ.P L+
      (Φ.P L*Φ.A U)*Φ.A T := by
    ring_nf
    simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]
  rw [heq]
  exact hh

lemma conjunction (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (A B : Line (Fin n × Fin ℓ)) (T U : Term (Fin n × Fin ℓ))
    (hL₁ : Good b (insert T A)) (hL₂ : Good b (insert U B))
    (hL : Good b (insert (T ∪ U) (A ∪ B))) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hprem₁ : Valid F D f (Φ.P (insert T A)))
    (hprem₂ : Valid F D f (Φ.P (insert U B)))
    (hinnerT : ∀ u ∈ T, Valid F D f (Φ.A T*(1+u)))
    (hinnerU : ∀ u ∈ U, Valid F D f (Φ.A U*(1+u)))
    (hinnerV : ∀ u ∈ T ∪ U, Valid F D f (Φ.A (T ∪ U)*(1+u)))
    (houter : ∀ W ∈ insert (T ∪ U) (A ∪ B),
      Valid F D f (Φ.P (insert (T ∪ U) (A ∪ B))*Φ.A W))
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D) :
    Valid F D f (Φ.P (insert (T ∪ U) (A ∪ B))) := by
  classical
  let L := insert (T ∪ U) (A ∪ B)
  have hT := hL₁ T (Finset.mem_insert_self _ _)
  have hU := hL₂ U (Finset.mem_insert_self _ _)
  have hV := hL (T ∪ U) (Finset.mem_insert_self _ _)
  have hAT := A_degree Φ htin T hT
  have hAU := A_degree Φ htin U hU
  have hAV := A_degree Φ htin (T ∪ U) hV
  have hP : (Φ.P L).totalDegree ≤ b*tin*tout := P_degree Φ htin L hL
  have hRS : b*tin ≤ b*tin*tout := by nlinarith
  have hrem₁ := remove_term hℓ F Φ f htin htout (insert T A) L T hL₁ hL hT
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact Or.inr rfl
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_left _ hW))) hf hprem₁ houter hD
  have hrem₂ := remove_term hℓ F Φ f htin htout (insert U B) L U hL₂ hL hU
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact Or.inr rfl
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_union_right _ hW))) hf hprem₂ houter hD
  have hdrem₂ : ((1+Φ.A U)*Φ.P L).totalDegree ≤ b*tin+b*tin*tout :=
    (totalDegree_mul _ _).trans (Nat.add_le_add
      ((totalDegree_add _ _).trans (max_le (by simp) hAU)) hP)
  have hrem₂' := valid_mul hℓ F f hf hrem₂ hdrem₂ hAT (by omega)
  have hrel := term_conjunction hℓ F Φ f htin T U hT hU hf hinnerT hinnerU hinnerV (by omega)
  have hdrel : (Φ.A (T ∪ U)+Φ.A T*Φ.A U).totalDegree ≤ 2*(b*tin) :=
    (totalDegree_add _ _).trans (max_le (hAV.trans (by omega))
      ((totalDegree_mul _ _).trans ((Nat.add_le_add hAT hAU).trans (by omega))))
  have hrelP := valid_mul hℓ F f hf hrel hdrel hP (by omega)
  have hlast := houter (T ∪ U) (Finset.mem_insert_self _ _)
  have hh := valid_add hℓ F f (valid_add hℓ F f (valid_add hℓ F f hrem₁ hrem₂') hrelP) hlast
  have heq : Φ.P L = (1+Φ.A T)*Φ.P L+((1+Φ.A U)*Φ.P L)*Φ.A T+
      (Φ.A (T ∪ U)+Φ.A T*Φ.A U)*Φ.P L+Φ.P L*Φ.A (T ∪ U) := by
    ring_nf
    simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]
  rw [heq]
  exact hh

end AC02Frege.ApproximantStructuralRules
end

section
-- Inlined Solutions.ApproximantPolynomialRules

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ApproximantPolynomialRules

open MvPolynomial LiftSAParity BooleanAlgebra BooleanFlip MajorityQuotient ApproximantBounds
open WeightedConsequence ApproximantRelations ApproximantLineTransport ApproximantStructuralRules

variable {n ℓ D Q b tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout)
    (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))

include hℓ

lemma singleton_removal (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (A L : Line (Fin n × Fin ℓ)) (u : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hL₀ : Good b (insert {u} A)) (hL : Good b L) (hkeep : A ⊆ L)
    (hf : coeffDeg f ≤ (Q : WithBot ℕ)) (hprem : Valid F D f (Φ.P (insert {u} A)))
    (houter : ∀ T ∈ L, Valid F D f (Φ.P L*Φ.A T))
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D) : Valid F D f ((1+u)*Φ.P L) := by
  classical
  have hh := remove_term (b := b) (Q := Q) hℓ F Φ f htin htout
    (insert ({u} : Term (Fin n × Fin ℓ)) A) L ({u} : Term (Fin n × Fin ℓ)) hL₀ hL
    (hL₀ _ (Finset.mem_insert_self _ _))
    (fun T hT => by
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact Or.inr rfl
      · exact Or.inl (hkeep hT)) hf hprem houter hD
  simpa only [A_singleton] using hh

lemma linear_combination (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (A B : Line (Fin n × Fin ℓ)) (u v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hL₁ : Good b (insert {u} A)) (hL₂ : Good b (insert {v} B))
    (hL : Good b (insert {1+u+v} (A ∪ B))) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hprem₁ : Valid F D f (Φ.P (insert {u} A)))
    (hprem₂ : Valid F D f (Φ.P (insert {v} B)))
    (houter : ∀ T ∈ insert {1+u+v} (A ∪ B),
      Valid F D f (Φ.P (insert {1+u+v} (A ∪ B))*Φ.A T))
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D) :
    Valid F D f (Φ.P (insert {1+u+v} (A ∪ B))) := by
  classical
  let L := insert {1+u+v} (A ∪ B)
  have hrem₁ := singleton_removal hℓ F Φ f htin htout A L u hL₁ hL
    (fun T hT => Finset.mem_insert_of_mem (Finset.mem_union_left _ hT)) hf hprem₁ houter hD
  have hrem₂ := singleton_removal hℓ F Φ f htin htout B L v hL₂ hL
    (fun T hT => Finset.mem_insert_of_mem (Finset.mem_union_right _ hT)) hf hprem₂ houter hD
  have hlast : Valid F D f (Φ.P L*(1+u+v)) := by
    simpa only [A_singleton] using houter {1+u+v} (Finset.mem_insert_self _ _)
  have hh := valid_add hℓ F f (valid_add hℓ F f hrem₁ hrem₂) hlast
  have heq : Φ.P L = (1+u)*Φ.P L+(1+v)*Φ.P L+Φ.P L*(1+u+v) := by
    have hthree : (3 : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) = 1 := by
      calc
        (3 : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) = 2+1 := by ring
        _ = 1 := by
          rw [CharTwo.two_eq_zero (R := MvPolynomial (Fin n × Fin ℓ) (ZMod 2)),zero_add]
    ring_nf
    simp only [CharTwo.two_eq_zero,hthree,mul_zero,mul_one,add_zero,zero_add]
  rw [heq]
  exact hh

/-- The unrestricted multiplier is removed algebraically; only the displayed conclusion is used
in the degree estimate. -/
lemma multiplication (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (A : Line (Fin n × Fin ℓ)) (u v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hL₀ : Good b (insert {u} A))
    (hL : Good b (insert {1+ML ((1+u)*v)} A)) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hprem : Valid F D f (Φ.P (insert {u} A)))
    (houter : ∀ T ∈ insert {1+ML ((1+u)*v)} A,
      Valid F D f (Φ.P (insert {1+ML ((1+u)*v)} A)*Φ.A T))
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D) :
    Valid F D f (Φ.P (insert {1+ML ((1+u)*v)} A)) := by
  classical
  let w := 1+ML ((1+u)*v)
  let L := insert {w} A
  have hrem := singleton_removal hℓ F Φ f htin htout A L u hL₀ hL
    (Finset.subset_insert _ _) hf hprem houter hD
  have hu : u.totalDegree ≤ b := hL₀ _ (Finset.mem_insert_self _ _) u (Finset.mem_singleton_self _)
  have hw : w.totalDegree ≤ b := hL _ (Finset.mem_insert_self _ _) w (Finset.mem_singleton_self _)
  have hP : (Φ.P L).totalDegree ≤ b*tin*tout := P_degree Φ htin L hL
  have hbR : b ≤ b*tin := by nlinarith
  have hdrem : ((1+u)*Φ.P L).totalDegree ≤ b+b*tin*tout :=
    (totalDegree_mul _ _).trans (Nat.add_le_add
      ((totalDegree_add _ _).trans (max_le (by simp) hu)) hP)
  have hcw : (1+w).totalDegree ≤ b := (totalDegree_add _ _).trans (max_le (by simp) hw)
  have hmult := valid_mul hℓ F f hf hrem hdrem hcw (by omega)
  have hcomp : 1+w = ML ((1+u)*v) := by
    dsimp [w]
    rw [← add_assoc,CharTwo.add_self_eq_zero,zero_add]
  have hab : ML ((1+u)*(1+w)) = ML (1+w) := by
    rw [hcomp,ml_mul_right]
    calc
      _ = ML (((1+u)*(1+u))*v) := by congr 1; ring
      _ = ML (ML ((1+u)*(1+u))*v) := (ml_mul_left _ _).symm
      _ = _ := by rw [ml_square,ml_idempotent,ml_mul_left]
  have he : ML (((1+u)*Φ.P L)*(1+w)) = ML (Φ.P L*(1+w)) := by
    calc
      _ = ML (Φ.P L*((1+u)*(1+w))) := by congr 1; ring
      _ = ML (Φ.P L*ML ((1+u)*(1+w))) := (ml_mul_right _ _).symm
      _ = _ := by rw [hab,ml_mul_right]
  have hfirst := (valid_congr hℓ F f _ _ he).mp hmult
  have hlast : Valid F D f (Φ.P L*w) := by
    simpa only [A_singleton] using houter {w} (Finset.mem_insert_self _ _)
  have hh := valid_add hℓ F f hfirst hlast
  have heq : Φ.P L = Φ.P L*(1+w)+Φ.P L*w := by
    ring_nf
    simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]
  rw [heq]
  exact hh

end AC02Frege.ApproximantPolynomialRules
end

section
-- Inlined Solutions.ApproximantCutRule

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ApproximantCutRule

open MvPolynomial LiftSAParity BooleanFlip ApproximantBounds WeightedConsequence
open ApproximantRelations ApproximantLineTransport ApproximantStructuralRules

theorem conjunction_cut {n ℓ D Q b tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (A B : Line (Fin n × Fin ℓ)) (T : Term (Fin n × Fin ℓ))
    (hL₁ : Good b (insert T A))
    (hL₂ : Good b (B ∪ T.image (fun u => ({1+u} : Term (Fin n × Fin ℓ)))))
    (hL : Good b (A ∪ B)) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (hprem₁ : Valid F D f (Φ.P (insert T A)))
    (hprem₂ : Valid F D f (Φ.P (B ∪ T.image (fun u => ({1+u} : Term (Fin n × Fin ℓ))))))
    (hinner : ∀ u ∈ T, Valid F D f (Φ.A T*(1+u)))
    (houter : ∀ U ∈ A ∪ B, Valid F D f (Φ.P (A ∪ B)*Φ.A U))
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D) : Valid F D f (Φ.P (A ∪ B)) := by
  classical
  let L := A ∪ B
  let L₂ := B ∪ T.image (fun u => ({1+u} : Term (Fin n × Fin ℓ)))
  have hT := hL₁ T (Finset.mem_insert_self _ _)
  have hAT := A_degree Φ htin T hT
  have hP : (Φ.P L).totalDegree ≤ b*tin*tout := P_degree Φ htin L hL
  have hbR : b ≤ b*tin := by nlinarith
  have hrem := remove_term hℓ F Φ f htin htout (insert T A) L T hL₁ hL hT
    (fun U hU => by
      rcases Finset.mem_insert.mp hU with rfl | hU
      · exact Or.inr rfl
      · exact Or.inl (Finset.mem_union_left _ hU)) hf hprem₁ houter hD
  have hsecond : Valid F D f (Φ.A T*Φ.P L) := by
    apply line_absorb hℓ F Φ f htin htout L₂ L (Φ.A T) hL₂ hL hAT hf hprem₂ _ hD
    intro U hU
    rcases Finset.mem_union.mp hU with hU | hU
    · have hUL : U ∈ L := Finset.mem_union_right _ hU
      have hAU := A_degree Φ htin U (hL U hUL)
      have hdx : (Φ.P L*Φ.A U).totalDegree ≤ b*tin*tout+b*tin :=
        (totalDegree_mul _ _).trans (Nat.add_le_add hP hAU)
      have hh := valid_mul hℓ F f hf (houter U hUL) hdx hAT (by omega)
      have heq : (Φ.A T*Φ.P L)*Φ.A U = (Φ.P L*Φ.A U)*Φ.A T := by ring
      rw [heq]
      exact hh
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hU
      have hdx : (Φ.A T*(1+u)).totalDegree ≤ b*tin+b :=
        (totalDegree_mul _ _).trans (Nat.add_le_add hAT
          ((totalDegree_add _ _).trans (max_le (by simp) (hT u hu))))
      have hh := valid_mul hℓ F f hf (hinner u hu) hdx hP (by omega)
      rw [A_singleton]
      have heq : (Φ.A T*Φ.P L)*(1+u) = (Φ.A T*(1+u))*Φ.P L := by ring
      rw [heq]
      exact hh
  have hh := valid_add hℓ F f hrem hsecond
  have heq : Φ.P L = (1+Φ.A T)*Φ.P L+Φ.A T*Φ.P L := by
    ring_nf
    simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]
  rw [heq]
  exact hh

end AC02Frege.ApproximantCutRule
end

section
-- Inlined Solutions.LiftedClauseBasics

open Module MvPolynomial AC02Frege LiftSAParity
open AC02Frege.BooleanAlgebra AC02Frege.BooleanRestrictions AC02Frege.MajorityFoundation

namespace AC02Frege.LiftedClauseBasics

theorem litPoly_degree {V : Type} (l : V × Bool) : (litPoly l).totalDegree ≤ 1 := by
  cases l with
  | mk i b =>
    cases b
    · change (1 + X i : MvPolynomial V (ZMod 2)).totalDegree ≤ 1
      exact (totalDegree_add _ _).trans (by simp)
    · simp [litPoly]

theorem complement_factor_degree {V : Type} (l : V × Bool) :
    (1 + litPoly l).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (by simpa using litPoly_degree l)

theorem clauseCompl_degree {V : Type} (J : Clause V) : (clauseCompl J).totalDegree ≤ J.card := by
  classical
  apply (totalDegree_finsetProd J _).trans
  calc
    (∑ l ∈ J, (1 + litPoly l).totalDegree) ≤ ∑ _l ∈ J, 1 :=
      Finset.sum_le_sum (fun l _ => complement_factor_degree l)
    _ = J.card := by simp

theorem complement_factor_vars {V : Type} (l : V × Bool) :
    (1 + litPoly l).vars ⊆ {l.1} := by
  classical
  apply (vars_add_subset _ _).trans
  simp only [vars_one, Finset.empty_union]
  cases l with
  | mk i b =>
    cases b
    · change (1 + X i : MvPolynomial V (ZMod 2)).vars ⊆ {i}
      simpa using vars_add_subset (1 : MvPolynomial V (ZMod 2)) (X i)
    · simp [litPoly]

theorem clauseCompl_vars {V : Type} [DecidableEq V] (J : Clause V) : (clauseCompl J).vars ⊆ J.image Prod.fst := by
  classical
  intro v hv
  have hv' : v ∈ J.biUnion (fun l => (1 + litPoly l).vars) := vars_prod _ hv
  obtain ⟨l, hl, hvl⟩ := Finset.mem_biUnion.mp hv'
  have heq := Finset.mem_singleton.mp (complement_factor_vars l hvl)
  exact Finset.mem_image.mpr ⟨l, hl, heq.symm⟩

theorem lifted_clause_origin {n ℓ : ℕ} (F : CNF (Fin n)) (C : Clause (Fin n × Fin ℓ))
    (hC : C ∈ lift F ℓ) :
    ∃ J ∈ F, C ∈ liftClause ℓ J ∧ ∀ l ∈ C, l.1.1 ∈ J.image Prod.fst := by
  classical
  obtain ⟨J, hJ, hCJ⟩ := Finset.mem_biUnion.mp hC
  refine ⟨J, hJ, hCJ, ?_⟩
  obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hCJ
  intro l hl
  obtain ⟨j, _, hlj⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hlj
  exact Finset.mem_image.mpr ⟨j.1, j.2, rfl⟩

theorem lifted_clause_blocks {n ℓ : ℕ} (F : CNF (Fin n)) (C : Clause (Fin n × Fin ℓ))
    (hC : C ∈ lift F ℓ) : blocksOf (clauseCompl C) ≤ width F := by
  classical
  obtain ⟨J, hJ, _, horigin⟩ := lifted_clause_origin F C hC
  have hsub : (ML (clauseCompl C)).vars.image Prod.fst ⊆ J.image Prod.fst := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    have hv' := clauseCompl_vars C (ml_vars_subset _ hv)
    obtain ⟨l, hl, hvl⟩ := Finset.mem_image.mp hv'
    rw [← hvl]
    exact horigin l hl
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
    (show J.card ≤ width F from Finset.le_sup (f := Finset.card) hJ))

theorem clauseCompl_nonzero_literals {V : Type} (C : Clause V) (x : V → ZMod 2)
    (hC : eval x (clauseCompl C) ≠ 0) : ∀ l ∈ C, eval x (litPoly l) = 0 := by
  classical
  have hp : (∏ l ∈ C, (1 + eval x (litPoly l))) ≠ 0 := by
    simpa only [clauseCompl, map_prod, map_add, map_one] using hC
  intro l hl
  have hf := Finset.prod_ne_zero_iff.mp hp l hl
  rcases eq_zero_or_one (eval x (litPoly l)) with h0 | h1
  · exact h0
  · exact False.elim (hf (by rw [h1, CharTwo.add_self_eq_zero]))

end AC02Frege.LiftedClauseBasics
end

section
-- Inlined Solutions.ClauseComplementCertificate

set_option maxHeartbeats 2000000

namespace AC02Frege.ClauseComplementCertificate

open MvPolynomial LiftSAParity

lemma finite_product_certificate {V I : Type} (S : Finset I)
    (x : I → MvPolynomial V (ZMod 2)) {r : ℕ} (hx : ∀ i ∈ S, (x i).totalDegree ≤ r) :
    ∃ v : I → MvPolynomial V (ZMod 2),
      1+(∏ i ∈ S, (1+x i)) = ∑ i ∈ S, v i*x i ∧
      ∀ i, (v i).totalDegree ≤ (S.card-1)*r := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0,?_,fun _ => by simp⟩
    simp [CharTwo.add_self_eq_zero]
  | @insert j S hj ih =>
    obtain ⟨v,hv,hdv⟩ := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    let p := ∏ i ∈ S, (1+x i)
    have hp : p.totalDegree ≤ S.card*r := by
      apply (totalDegree_finsetProd _ _).trans
      calc
        _ ≤ ∑ _i ∈ S, r := by
          apply Finset.sum_le_sum
          intro i hi
          exact (totalDegree_add _ _).trans (max_le (by simp)
            (hx i (Finset.mem_insert_of_mem hi)))
        _ = _ := by simp
    refine ⟨fun i => if i=j then p else v i,?_,?_⟩
    · rw [Finset.sum_insert hj,Finset.prod_insert hj]
      simp only [ite_true]
      have hsum : (∑ i ∈ S, (if i=j then p else v i)*x i) = ∑ i ∈ S, v i*x i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_neg (by intro he; subst i; exact hj hi)]
      rw [hsum,← hv]
      change 1+(1+x j)*p = p*x j+(1+p)
      ring
    · intro i
      rw [Finset.card_insert_of_notMem hj,Nat.add_sub_cancel]
      dsimp only
      split_ifs
      · exact hp
      · exact (hdv i).trans (Nat.mul_le_mul_right r (by omega))

end AC02Frege.ClauseComplementCertificate
end

section
-- Inlined Solutions.LiftedClauseSemantics

open Module MvPolynomial AC02Frege LiftSAParity
open AC02Frege.BooleanAlgebra AC02Frege.MajorityFoundation AC02Frege.MajorityCoordinateBasis
open AC02Frege.LiftedClauseBasics

namespace AC02Frege.LiftedClauseSemantics

theorem majority_literal_false {n ℓ : ℕ} (hℓ : Odd ℓ) (x : Fin n × Fin ℓ → ZMod 2)
    (i : Fin n) (b : Bool) (A : Finset (Fin ℓ)) (hA : A.card = ℓ / 2 + 1)
    (hx : ∀ a ∈ A, eval x (litPoly ((i, a), b)) = 0) :
    eval (fun j => eval x (hBlock (ℓ := ℓ) j)) (litPoly (i, b)) = 0 := by
  classical
  let W := Finset.univ.filter (fun a => x (i, a) = 1)
  cases b
  · have hsub : A ⊆ W := by
      intro a ha
      have hz := hx a ha
      simp only [litPoly, Bool.false_eq_true, ↓reduceIte, map_add, map_one, eval_X] at hz
      have he := congrArg (fun r : ZMod 2 => 1 + r) hz
      have h1 : x (i, a) = 1 := by
        simpa only [CharTwo.add_cancel_left, add_zero] using he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, h1⟩
    have hh : ℓ / 2 < W.card := by have hc := Finset.card_le_card hsub; omega
    simp only [litPoly, Bool.false_eq_true, ↓reduceIte, map_add, map_one, eval_X]
    rw [hBlock_eval, majOne_eval, if_pos hh, CharTwo.add_self_eq_zero]
  · have hsub : W ⊆ Aᶜ := by
      intro a ha
      apply Finset.mem_compl.mpr
      intro hAa
      have hz := hx a hAa
      simp only [litPoly, ↓reduceIte, eval_X] at hz
      have h1 := (Finset.mem_filter.mp ha).2
      exact zero_ne_one (hz.symm.trans h1)
    have hh : ¬ ℓ / 2 < W.card := by
      have hc := Finset.card_le_card hsub
      rw [Finset.card_compl, Fintype.card_fin, hA] at hc
      rcases hℓ with ⟨k, hk⟩
      omega
    simp only [litPoly, ↓reduceIte, eval_X]
    rw [hBlock_eval, majOne_eval, if_neg hh]

theorem lifted_clause_base_false {n ℓ : ℕ} (hℓ : Odd ℓ) (J : Clause (Fin n))
    (C : Clause (Fin n × Fin ℓ)) (hC : C ∈ liftClause ℓ J) (x : Fin n × Fin ℓ → ZMod 2)
    (hx : eval x (clauseCompl C) ≠ 0) :
    eval (fun i => eval x (hBlock (ℓ := ℓ) i)) (clauseCompl J) = 1 := by
  classical
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
  have hbits := clauseCompl_nonzero_literals _ x hx
  simp only [clauseCompl, map_prod]
  apply Finset.prod_eq_one
  intro l hl
  have hcard : (A l hl).card = ℓ / 2 + 1 :=
    (Finset.mem_powersetCard.mp (Finset.mem_pi.mp hA l hl)).2
  have hfalse : eval (fun i => eval x (hBlock (ℓ := ℓ) i)) (litPoly l) = 0 := by
    apply majority_literal_false hℓ x l.1 l.2 (A l hl) hcard
    intro a ha
    apply hbits
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨l, hl⟩, Finset.mem_attach J ⟨l, hl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  rw [map_add, map_one, hfalse, add_zero]

theorem lifted_clause_absorbs_base {n ℓ : ℕ} (hℓ : Odd ℓ) (J : Clause (Fin n))
    (C : Clause (Fin n × Fin ℓ)) (hC : C ∈ liftClause ℓ J) :
    ML (bind₁ (fun i => hBlock (ℓ := ℓ) i) (ML (clauseCompl J)) * clauseCompl C) =
      ML (clauseCompl C) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  rw [eval_ml, eval_ml, map_mul, eval_bind_majority, eval_ml]
  by_cases hx : eval x (clauseCompl C) = 0
  · rw [hx, mul_zero]
  · rw [lifted_clause_base_false hℓ J C hC x hx, one_mul]

end AC02Frege.LiftedClauseSemantics
end

section
-- Inlined Solutions.LiftedInputClauses

open Module MvPolynomial AC02Frege LiftSAParity
open AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip AC02Frege.Support
open AC02Frege.MajorityTensorIndex AC02Frege.MajorityCoefficientDegree AC02Frege.MajorityCoefficientFibres
open AC02Frege.MajorityCoefficientAlgebra AC02Frege.MajorityMultiplication
open AC02Frege.LiftedClauseBasics AC02Frege.LiftedClauseSemantics

namespace AC02Frege.LiftedInputClauses

theorem lifted_input_clauses {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n)) (D Q : ℕ)
    (C : Clause (Fin n × Fin ℓ)) (hC : C ∈ lift F ℓ) (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hf : coeffDeg f ≤ (Q : WithBot ℕ)) (hD : Q + 2 * width F ≤ D) :
    f * clauseCompl C ∈ CHat F ℓ D := by
  classical
  obtain ⟨J, hJ, hCJ, _⟩ := lifted_clause_origin F C hC
  let a := clauseCompl C
  let R := ML (clauseCompl J)
  let P := f * a
  have hwJ : J.card ≤ width F := Finset.le_sup (f := Finset.card) hJ
  have hRdeg : R.totalDegree ≤ width F :=
    (ml_totalDegree_le _).trans ((clauseCompl_degree J).trans hwJ)
  have hR : R ∈ CD F D := by
    refine ⟨ml_multilinear _, ?_⟩
    apply pc_multilinearization F D
    exact pc_axiom F D (clauseCompl J) (Or.inl ⟨J, hJ, rfl⟩)
      ((clauseCompl_degree J).trans (by omega))
  have hbeta : coeffDeg P ≤ ((Q + width F : ℕ) : WithBot ℕ) := by
    have hmul := multiplication_estimate hℓ a (blocksOf a)
      (fun B A => (light_product_function_bounds hℓ B A a).2) f
    have hb := lifted_clause_blocks F C hC
    calc
      coeffDeg P ≤ coeffDeg f + ((blocksOf a : ℕ) : WithBot ℕ) := hmul
      _ ≤ (Q : WithBot ℕ) + ((width F : ℕ) : WithBot ℕ) :=
        add_le_add hf (WithBot.coe_le_coe.mpr hb)
      _ = ((Q + width F : ℕ) : WithBot ℕ) := (WithBot.coe_add Q (width F)).symm
  have habs : ML (bind₁ (fun i => hBlock (ℓ := ℓ) i) R * a) = ML a :=
    lifted_clause_absorbs_base hℓ J C hCJ
  have hP : ML (bind₁ (fun i => hBlock (ℓ := ℓ) i) R * P) = ML P := by
    calc
      ML (bind₁ (fun i => hBlock (ℓ := ℓ) i) R * P) =
          ML (f * (bind₁ (fun i => hBlock (ℓ := ℓ) i) R * a)) := by
        congr 1
        dsimp only [P]
        ring
      _ = ML (f * ML (bind₁ (fun i => hBlock (ℓ := ℓ) i) R * a)) := (ml_mul_right _ _).symm
      _ = ML (f * ML a) := by rw [habs]
      _ = ML P := ml_mul_right f a
  intro A hA
  let A' : GlobalLight n ℓ := ⟨A, hA⟩
  have hmap : coefficientMap hℓ A' (bind₁ (fun i => hBlock (ℓ := ℓ) i) R * P) =
      coefficientMap hℓ A' P := congrFun (coeffPoly_congr hℓ _ _ hP) A
  have heq : coefficientMap hℓ A' P = ML (R * coefficientMap hℓ A' P) :=
    hmap.symm.trans (coefficientMap_mul_base hℓ A' R P)
  change coefficientMap hℓ A' P ∈ CD F D
  rw [heq]
  apply consequence_mul F D _ _ hR
  have hpdeg := coefficient_degree_le_beta P (Q + width F) hbeta A'
  change (coefficientMap hℓ A' P).totalDegree ≤ Q + width F at hpdeg
  omega

end AC02Frege.LiftedInputClauses
end

section
-- Inlined Solutions.ApproximantInputRule

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ApproximantInputRule

open MvPolynomial LiftSAParity BooleanFlip ApproximantBounds WeightedConsequence
open ApproximantRelations ApproximantStructuralRules ClauseComplementCertificate LiftedClauseBasics

theorem input_clause {n ℓ D Q b tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (htin : 1 ≤ tin) (C : Clause (Fin n × Fin ℓ)) (hC : C ∈ lift F ℓ)
    (hL : Good b (inputLine C)) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (houter : ∀ T ∈ inputLine C, Valid F D f (Φ.P (inputLine C)*Φ.A T))
    (hD : Q+b*tin*tout+width (lift F ℓ) ≤ D) (hD' : Q+2*width F ≤ D) :
    Valid F D f (Φ.P (inputLine C)) := by
  classical
  let L := inputLine C
  have hP : (Φ.P L).totalDegree ≤ b*tin*tout := P_degree Φ htin L hL
  have hwidth : C.card ≤ width (lift F ℓ) := Finset.le_sup (f := Finset.card) hC
  have hc : Valid F D f (clauseCompl C) := LiftedInputClauses.lifted_input_clauses hℓ F D Q C hC f hf hD'
  have hfirst := valid_mul hℓ F f hf hc (clauseCompl_degree C) hP (by omega)
  by_cases hC0 : C = ∅
  · subst C
    simpa only [clauseCompl,Finset.prod_empty,one_mul] using hfirst
  have hCpos : 1 ≤ C.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC0)
  obtain ⟨v,hv,hdv⟩ := finite_product_certificate C litPoly (fun l hl => litPoly_degree l)
  have hsecond : Valid F D f (Φ.P L*(1+clauseCompl C)) := by
    apply valid_certificate hℓ F f C hf _ (fun l => Φ.P L*litPoly l) v
      (multiply_certificate C (Φ.P L) _ _ _ (congrArg ML hv))
    · intro l hl
      have hmem : ({litPoly l} : Term (Fin n × Fin ℓ)) ∈ L :=
        Finset.mem_image.mpr ⟨l,hl,rfl⟩
      simpa only [A_singleton] using houter _ hmem
    · intro l hl
      exact (totalDegree_mul _ _).trans (Nat.add_le_add hP (litPoly_degree l))
    · intro l hl
      simpa only [Nat.mul_one] using hdv l
    · omega
  have hh := valid_add hℓ F f hfirst hsecond
  have heq : Φ.P L = clauseCompl C*Φ.P L+Φ.P L*(1+clauseCompl C) := by
    ring_nf
    simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]
  rw [heq]
  exact hh

end AC02Frege.ApproximantInputRule
end

section
-- Inlined Solutions.ApproximantRulePreservation

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.ApproximantRulePreservation

open MvPolynomial LiftSAParity ApproximantBounds WeightedConsequence
open ApproximantLineTransport ApproximantStructuralRules ApproximantPolynomialRules

theorem inference {n ℓ D Q b tin tout : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (htin : 1 ≤ tin) (htout : 1 ≤ tout) (π : List (Line (Fin n × Fin ℓ)))
    (hgood : ∀ L ∈ π, Good b L) (hf : coeffDeg f ≤ (Q : WithBot ℕ))
    (h39 : InnerErr F ℓ D Φ π f) (h40 : OuterErr F ℓ D Φ π f)
    (hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D)
    (hinput : Q+b*tin*tout+width (lift F ℓ) ≤ D) (hbase : Q+2*width F ≤ D)
    {E : Line (Fin n × Fin ℓ) → Prop} {L : Line (Fin n × Fin ℓ)}
    (hL : L ∈ π) (hi : Infers (lift F ℓ) E L)
    (hEπ : ∀ L, E L → L ∈ π) (hEp : ∀ L, E L → Valid F D f (Φ.P L)) :
    Valid F D f (Φ.P L) := by
  classical
  have inner (L) (hL : L ∈ π) (T) (hT : T ∈ L) :
      ∀ u ∈ T, Valid F D f (Φ.A T*(1+u)) := by
    intro u hu
    simpa only [Valid,mul_assoc] using h39 L hL T hT u hu
  have outer (L) (hL : L ∈ π) : ∀ T ∈ L, Valid F D f (Φ.P L*Φ.A T) := by
    intro T hT
    simpa only [Valid,mul_assoc] using h40 L hL T hT
  cases hi with
  | axOne =>
    have hh := outer _ hL ({1} : Term (Fin n × Fin ℓ)) (by simp)
    simpa only [A_singleton,mul_one] using hh
  | axTop =>
    have hh := outer _ hL (∅ : Term (Fin n × Fin ℓ)) (by simp)
    simpa only [A_empty,mul_one] using hh
  | axEM u =>
    have h₁ : Valid F D f (Φ.P {{u},{1+u}}*u) := by
      simpa only [A_singleton] using outer _ hL ({u} : Term (Fin n × Fin ℓ)) (by simp)
    have h₂ : Valid F D f (Φ.P {{u},{1+u}}*(1+u)) := by
      simpa only [A_singleton] using outer _ hL ({1+u} : Term (Fin n × Fin ℓ)) (by simp)
    have hh := valid_add hℓ F f h₁ h₂
    have heq : Φ.P {{u},{1+u}} = Φ.P {{u},{1+u}}*u+Φ.P {{u},{1+u}}*(1+u) := by
      ring_nf
      simp only [CharTwo.two_eq_zero,mul_zero,add_zero,zero_add]
    rw [heq]
    exact hh
  | input C hC =>
    exact ApproximantInputRule.input_clause hℓ F Φ f htin C hC (hgood _ hL) hf
      (outer _ hL) hinput hbase
  | weaken L L₀ hE hsub =>
    exact weakening hℓ F Φ f htin htout L₀ L hsub (hgood _ (hEπ _ hE)) (hgood _ hL)
      hf (hEp _ hE) (outer _ hL) hD
  | proj A T U hE hsub =>
    exact projection hℓ F Φ f htin htout A T U hsub (hgood _ (hEπ _ hE)) (hgood _ hL)
      hf (hEp _ hE) (inner _ (hEπ _ hE) T (Finset.mem_insert_self _ _)) (outer _ hL) hD
  | conj A B T U hE₁ hE₂ =>
    exact conjunction hℓ F Φ f htin htout A B T U
      (hgood _ (hEπ _ hE₁)) (hgood _ (hEπ _ hE₂)) (hgood _ hL) hf (hEp _ hE₁) (hEp _ hE₂)
      (inner _ (hEπ _ hE₁) T (Finset.mem_insert_self _ _))
      (inner _ (hEπ _ hE₂) U (Finset.mem_insert_self _ _))
      (inner _ hL (T ∪ U) (Finset.mem_insert_self _ _)) (outer _ hL) hD
  | cut A B T hE₁ hE₂ =>
    exact ApproximantCutRule.conjunction_cut hℓ F Φ f htin htout A B T
      (hgood _ (hEπ _ hE₁)) (hgood _ (hEπ _ hE₂)) (hgood _ hL) hf (hEp _ hE₁) (hEp _ hE₂)
      (inner _ (hEπ _ hE₁) T (Finset.mem_insert_self _ _)) (outer _ hL) hD
  | lin A B u v hE₁ hE₂ =>
    exact linear_combination hℓ F Φ f htin htout A B u v
      (hgood _ (hEπ _ hE₁)) (hgood _ (hEπ _ hE₂)) (hgood _ hL) hf (hEp _ hE₁) (hEp _ hE₂)
      (outer _ hL) hD
  | mul A u v hE =>
    exact multiplication hℓ F Φ f htin htout A u v
      (hgood _ (hEπ _ hE)) (hgood _ hL) hf (hEp _ hE) (outer _ hL) hD
  | del A hE =>
    have hh := singleton_removal hℓ F Φ f htin htout L L 0
      (hgood _ (hEπ _ hE)) (hgood _ hL) (Finset.Subset.refl _) hf (hEp _ hE) (outer _ hL) hD
    simpa only [add_zero,one_mul] using hh

end AC02Frege.ApproximantRulePreservation
end

section
-- Inlined Solutions.Depth35Preservation

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.Depth35Preservation

open MvPolynomial LiftSAParity WeightedConsequence ApproximantStructuralRules

theorem preservation {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (b D Q tin tout : ℕ) (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (π : List (Line (Fin n × Fin ℓ))) (hπ : IsRefutation b (lift F ℓ) π)
    (Φ : Approx (Fin n × Fin ℓ) tin tout) (f : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (hf : coeffDeg f ≤ (Q : WithBot ℕ)) (h39 : InnerErr F ℓ D Φ π f)
    (h40 : OuterErr F ℓ D Φ π f)
    (h41a : Q + max (2 * (b * tin) * tout + 2 * (b * tin)) (b * tin * tout + width (lift F ℓ)) ≤ D)
    (h41b : Q + 2 * width F ≤ D) :
    (∀ L ∈ π, f * Φ.P L ∈ CHat F ℓ D) ∧ f ∈ CHat F ℓ D := by
  rcases hπ with ⟨hb,hallowed,hinfers,hlast⟩
  have hgood : ∀ L ∈ π, Good b L := by
    intro L hL T hT u hu
    exact (hallowed L hL T hT u hu).2
  have hD : Q+2*(b*tin*tout)+2*(b*tin) ≤ D := by
    have hh : Q+(2*(b*tin)*tout+2*(b*tin)) ≤ D :=
      (add_le_add (le_refl Q) (le_max_left _ _)).trans h41a
    nlinarith
  have hinput : Q+b*tin*tout+width (lift F ℓ) ≤ D := by
    have hh : Q+(b*tin*tout+width (lift F ℓ)) ≤ D :=
      (add_le_add (le_refl Q) (le_max_right _ _)).trans h41a
    omega
  have hindex : ∀ k (hk : k < π.length), Valid F D f (Φ.P π[k]) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      apply ApproximantRulePreservation.inference hℓ F Φ f htin htout π hgood hf h39 h40 hD hinput h41b
        (List.getElem_mem hk) (hinfers k hk)
      · intro L hE
        obtain ⟨j,hjk,hj⟩ := hE
        exact List.mem_of_getElem? hj
      · intro L hE
        obtain ⟨j,hjk,hj⟩ := hE
        obtain ⟨hjlen,hjval⟩ := List.getElem?_eq_some_iff.mp hj
        simpa only [hjval] using ih j hjk hjlen
  have hall : ∀ L ∈ π, Valid F D f (Φ.P L) := by
    intro L hL
    obtain ⟨k,hk,hval⟩ := List.mem_iff_getElem.mp hL
    simpa only [hval] using hindex k hk
  refine ⟨hall,?_⟩
  have hh := hall ∅ (List.mem_of_getLast? hlast)
  simpa only [Valid,ApproximantBounds.P_empty,mul_one] using hh

end AC02Frege.Depth35Preservation
end

section
-- Inlined Solutions.CombinedRankCriterion

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.CombinedRankCriterion

open Module MvPolynomial LiftSAParity FiniteSetApproximation TwoLevelErrorSpaces TwoLevelCombinedRank

theorem compact {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (b D Q K tin tout : ℕ) (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (π : List (Line (Fin n × Fin ℓ))) (hπ : IsRefutation b (lift F ℓ) π)
    (hRK : b*tin ≤ K) (hKN : 2*K < n*ℓ)
    (h41a : Q+max (2*(b*tin)*tout+2*(b*tin)) (b*tin*tout+width (lift F ℓ)) ≤ D)
    (h41b : Q+2*width F ≤ D) :
    let Bnd := (totalSize π : ℝ)*(errorBound F ℓ D Q K b tin+errorBound F ℓ D Q K (b*tin) tout)+
      (Eexcl n ℓ Q K : ℝ)
    (∃ Φ : Approx (Fin n × Fin ℓ) tin tout,
      (monoCount (n*ℓ) K : ℝ)-(dimSpan {f | f ∈ Vdeg (Fin n × Fin ℓ) K ∧ f ∈ WQ n ℓ Q ∧
        InnerErr F ℓ D Φ π f ∧ OuterErr F ℓ D Φ π f} : ℝ) ≤ Bnd) ∧
    (hThresh F ℓ D K : ℝ) ≤ Bnd := by
  classical
  dsimp only
  have hb := hπ.1
  have hbR : b ≤ b*tin := by nlinarith
  have hRS : b*tin ≤ b*tin*tout := by nlinarith
  have hsim : Q+2*(b*tin)*tout+2*(b*tin) ≤ D := by
    have hh : Q+(2*(b*tin)*tout+2*(b*tin)) ≤ D :=
      (add_le_add (le_refl Q) (le_max_left _ _)).trans h41a
    omega
  have hDin : Q+(tin+2)*b ≤ D := by nlinarith
  have hDout : Q+(tout+2)*(b*tin) ≤ D := by nlinarith
  obtain ⟨Φ,hi,ho⟩ := TwoLevelApproximationChoice.choose_both hℓ F htin htout hb hRK hKN hDin hDout
  let Ci := errorBound F ℓ D Q K b tin
  let Co := errorBound F ℓ D Q K (b*tin) tout
  have hrank := combined_rank_bound (D := D) (Q := Q) (K := K) hℓ F Φ π Ci Co
    (errorBound_nonneg F ℓ D Q K b tin) (errorBound_nonneg F ℓ D Q K (b*tin) tout)
    (fun L hL T hT => hi T (fun u hu => hπ.2.1 L hL T hT u hu))
    (fun L hL => ho L (fun T hT u hu => hπ.2.1 L hL T hT u hu))
  have hspan := dimSpan_common hℓ F Φ π (D := D) (Q := Q) (K := K)
  refine ⟨⟨Φ,?_⟩,?_⟩
  · rw [hspan]
    exact hrank
  · let B := SemAC02.Ble (Fin n × Fin ℓ) K
    let U := common hℓ F D Q K Φ π
    let C := B ⊓ MajorityLightSeparation.chatSpace hℓ F D
    have hUC : U ≤ C := by
      intro f hf
      have hs := (mem_common hℓ F Φ π f (D := D) (Q := Q) (K := K)).mp hf
      have hβ : coeffDeg f ≤ (Q : WithBot ℕ) := hs.2.1
      have hc := (Depth35Preservation.preservation hℓ F b D Q tin tout htin htout π hπ Φ f
        hβ hs.2.2.1 hs.2.2.2 h41a h41b).2
      exact ⟨(SemAC02.BooleanDegreeSpaces.mem_Ble_iff K f).mpr hs.1,
        (MajorityLightSeparation.mem_chatSpace hℓ F f).mpr hc⟩
    have hdim : finrank (ZMod 2) U ≤ finrank (ZMod 2) C := Submodule.finrank_mono hUC
    have hn := ErrorSpaceDimensions.threshold_rank_nullity hℓ F (D := D) (K := K)
    have hB : finrank (ZMod 2) B = monoCount (n*ℓ) K := by
      simpa only [Fintype.card_prod,Fintype.card_fin] using BooleanDegreeCounts.finrank_Ble (V := Fin n × Fin ℓ) K
    change hThresh F ℓ D K+finrank (ZMod 2) C = finrank (ZMod 2) B at hn
    rw [hB] at hn
    have hn' : (hThresh F ℓ D K : ℝ)+(finrank (ZMod 2) C : ℝ) = (monoCount (n*ℓ) K : ℝ) := by exact_mod_cast hn
    have hdim' : (finrank (ZMod 2) U : ℝ) ≤ (finrank (ZMod 2) C : ℝ) := by exact_mod_cast hdim
    change (monoCount (n*ℓ) K : ℝ)-(finrank (ZMod 2) U : ℝ) ≤ _ at hrank
    linarith

end AC02Frege.CombinedRankCriterion
end

section
-- Inlined Solutions.MajorityCombinedRank

set_option maxHeartbeats 2000000

namespace AC02Frege.MajorityCombinedRank

open MvPolynomial LiftSAParity

theorem rank_criterion {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (b D Q K tin tout : ℕ) (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (π : List (Line (Fin n × Fin ℓ))) (hπ : IsRefutation b (lift F ℓ) π)
    (hRK : b * tin ≤ K) (hKN : 2 * K < n * ℓ)
    (h41a : Q + max (2 * (b * tin) * tout + 2 * (b * tin)) (b * tin * tout + width (lift F ℓ))
      ≤ D)
    (h41b : Q + 2 * width F ≤ D) :
    let N := n * ℓ
    let T : ℝ := (totalSize π : ℝ)
    let h : ℝ := (hThresh F ℓ D K : ℝ)
    let ε : ℝ := epsExcl n ℓ Q K
    let M : ℝ := (monoCount N K : ℝ)
    let ηb : ℝ := etaFrac N K b
    let ηR : ℝ := etaFrac N K (b * tin)
    let bound : ℝ := T * (Real.exp (-(ηb * tin)) + Real.exp (-(ηR * tout))) * (h + ε * M)
      + 2 * T * (N : ℝ) ^ 2 * ε * M * (ηb⁻¹ + ηR⁻¹) + (Eexcl n ℓ Q K : ℝ)
    (∃ Φ : Approx (Fin n × Fin ℓ) tin tout,
      M - (dimSpan {f | f ∈ Vdeg (Fin n × Fin ℓ) K ∧ f ∈ WQ n ℓ Q ∧
        InnerErr F ℓ D Φ π f ∧ OuterErr F ℓ D Φ π f} : ℝ) ≤ bound) ∧
    h ≤ bound  := by
  dsimp only
  have hc := CombinedRankCriterion.compact hℓ F b D Q K tin tout htin htout π hπ hRK hKN h41a h41b
  dsimp only at hc
  have hformula :
      (totalSize π : ℝ)*(FiniteSetApproximation.errorBound F ℓ D Q K b tin+
        FiniteSetApproximation.errorBound F ℓ D Q K (b*tin) tout)+(Eexcl n ℓ Q K : ℝ) =
      (totalSize π : ℝ)*(Real.exp (-(etaFrac (n*ℓ) K b*tin))+Real.exp (-(etaFrac (n*ℓ) K (b*tin)*tout)))*
        ((hThresh F ℓ D K : ℝ)+epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ))+
        2*(totalSize π : ℝ)*((n*ℓ : ℕ) : ℝ)^2*epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ)*
          ((etaFrac (n*ℓ) K b)⁻¹+(etaFrac (n*ℓ) K (b*tin))⁻¹)+(Eexcl n ℓ Q K : ℝ) := by
    unfold FiniteSetApproximation.errorBound
    ring
  rw [hformula] at hc
  exact hc

end AC02Frege.MajorityCombinedRank
end

open AC02Frege LiftSAParity

theorem solution {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (b D Q K tin tout : ℕ) (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (π : List (Line (Fin n × Fin ℓ))) (hπ : IsRefutation b (lift F ℓ) π)
    (hRK : b * tin ≤ K) (hKN : 2 * K < n * ℓ)
    (h41a : Q + max (2 * (b * tin) * tout + 2 * (b * tin)) (b * tin * tout + width (lift F ℓ))
      ≤ D)
    (h41b : Q + 2 * width F ≤ D) :
    let N := n * ℓ
    let T : ℝ := (totalSize π : ℝ)
    let h : ℝ := (hThresh F ℓ D K : ℝ)
    let ε : ℝ := epsExcl n ℓ Q K
    let M : ℝ := (monoCount N K : ℝ)
    let ηb : ℝ := etaFrac N K b
    let ηR : ℝ := etaFrac N K (b * tin)
    let bound : ℝ := T * (Real.exp (-(ηb * tin)) + Real.exp (-(ηR * tout))) * (h + ε * M)
      + 2 * T * (N : ℝ) ^ 2 * ε * M * (ηb⁻¹ + ηR⁻¹) + (Eexcl n ℓ Q K : ℝ)
    (∃ Φ : Approx (Fin n × Fin ℓ) tin tout,
      M - (dimSpan {f | f ∈ Vdeg (Fin n × Fin ℓ) K ∧ f ∈ WQ n ℓ Q ∧
        InnerErr F ℓ D Φ π f ∧ OuterErr F ℓ D Φ π f} : ℝ) ≤ bound) ∧
    h ≤ bound  := by
  exact AC02Frege.MajorityCombinedRank.rank_criterion hℓ F b D Q K tin tout htin htout π hπ hRK hKN h41a h41b
