-- Prove2me | solution 1 for AC02Frege.Supplement.theorem_6_3
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T07:19:51.91659+00:00
-- url     : https://prove2.me/submissions/36a3e54d-2369-4983-9585-f78879bccf7d

import Definitions.Def_AC02Frege_Supplement_selector
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_Supplement_ResPC
import Mathlib

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
-- Inlined Solutions.SelectorRestrictionBasics

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorRestrictionBasics

open MvPolynomial AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

variable {V : Type} {q : ℕ} (A : V → Bool → Fin q)

lemma rho_degree (x : V×Bool×Fin q) : (selRho A x).totalDegree≤1 := by
  unfold selRho
  split_ifs <;> try simp
  exact (totalDegree_add _ _).trans (by simp)

@[simp] lemma restrict_zero : restrictPoly A 0=0 := by simp [restrictPoly]

@[simp] lemma restrict_one : restrictPoly A 1=1 := by
  rw [restrictPoly,map_one]
  exact ml_of_multilinear _ (by simpa [xMon] using xMon_multilinear (∅ : Finset V))

@[simp] lemma restrict_add (p u : MvPolynomial (V×Bool×Fin q) (ZMod 2)) :
    restrictPoly A (p+u)=restrictPoly A p+restrictPoly A u := by
  simp only [restrictPoly,map_add]

@[simp] lemma restrict_smul (a : ZMod 2) (p : MvPolynomial (V×Bool×Fin q) (ZMod 2)) :
    restrictPoly A (a • p)=a • restrictPoly A p := by
  simp only [restrictPoly,map_smul]

lemma rho_multilinear (x : V×Bool×Fin q) : IsMultilinear (selRho A x) := by
  unfold selRho
  split_ifs
  · simpa [xMon] using xMon_multilinear ({x.1} : Finset V)
  · have h1 : ML (1 : MvPolynomial V (ZMod 2))=1 :=
        ml_of_multilinear _ (by simpa [xMon] using xMon_multilinear (∅ : Finset V))
    have hx : ML (X x.1 : MvPolynomial V (ZMod 2))=X x.1 :=
        ml_of_multilinear _ (by simpa [xMon] using xMon_multilinear ({x.1} : Finset V))
    have he : ML (1+X x.1 : MvPolynomial V (ZMod 2))=1+X x.1 := by rw [map_add,h1,hx]
    rw [← he]
    exact ml_multilinear _
  · simpa using (ml_multilinear (0 : MvPolynomial V (ZMod 2)))

@[simp] lemma restrict_X (x : V×Bool×Fin q) : restrictPoly A (X x)=selRho A x := by
  rw [restrictPoly,aeval_X]
  exact ml_of_multilinear _ (rho_multilinear A x)

lemma restrict_mul [Finite V] (p u : MvPolynomial (V×Bool×Fin q) (ZMod 2)) :
    restrictPoly A (p*u)=ML (restrictPoly A p*restrictPoly A u) := by
  unfold restrictPoly
  rw [map_mul,ml_mul_left,ml_mul_right]

lemma restrict_multilinear (p : MvPolynomial (V×Bool×Fin q) (ZMod 2)) :
    IsMultilinear (restrictPoly A p) := ml_multilinear _

lemma eval_restrict (x : V → ZMod 2) (p : MvPolynomial (V×Bool×Fin q) (ZMod 2)) :
    eval x (restrictPoly A p)=eval (fun y => eval x (selRho A y)) p := by
  rw [restrictPoly,eval_ml,map_aeval]
  have he : (eval x).comp (algebraMap (ZMod 2) (MvPolynomial V (ZMod 2)))=RingHom.id (ZMod 2) := by
    ext a
    simp
  rw [he]
  rfl

lemma f2_pow_of_pos (a : ZMod 2) (k : ℕ) (hk : 0<k) : a^k=a := by
  have ha : a=0 ∨ a=1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl <;> simp [ne_of_gt hk]

lemma monomial_unchosen [Fintype V] (s : (V×Bool×Fin q) →₀ ℕ) (c : ZMod 2)
    (y : V×Bool×Fin q) (hy : y∈s.support) (hcol : y.2.2≠A y.1 y.2.1) :
    restrictPoly A (monomial s c)=0 := by
  apply multilinear_ext (restrict_multilinear A _) (by simpa using ml_multilinear (0 : MvPolynomial V (ZMod 2)))
  intro x
  rw [eval_restrict,eval_monomial,map_zero]
  have hpow : (eval x (selRho A y))^(s y)=0 := by
    have hs : s y≠0 := Finsupp.mem_support_iff.mp hy
    simp only [selRho,if_neg hcol,map_zero,zero_pow hs]
  have hp : s.prod (fun z k => (eval x (selRho A z))^k)=0 :=
    Finset.prod_eq_zero hy hpow
  rw [hp,mul_zero]

end AC02Frege.Supplement.SelectorRestrictionBasics
end

section
-- Inlined Solutions.ResDerivation

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.ResDerivation

open MvPolynomial LiftSAParity

def Valid {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ) (π : List (RLine V)) : Prop :=
  (∀ L∈π, ∀ u∈L, u.totalDegree≤D) ∧
  ∀ k (hk : k<π.length), ResInfers Γ (fun L => ∃ j<k, π[j]?=some L) π[k]

def Derives {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ) (L : RLine V) (k : ℕ) : Prop :=
  ∃ π : List (RLine V), Valid Γ D π ∧ L∈π ∧ π.length≤k

lemma inference_mono {V : Type} [DecidableEq V] (Γ : CNF V) {E E' : RLine V → Prop}
    (hE : ∀ L, E L → E' L) {L : RLine V} (h : ResInfers Γ E L) : ResInfers Γ E' L := by
  cases h with
  | axOne => exact ResInfers.axOne
  | axBool v => exact ResInfers.axBool v
  | input J hJ => exact ResInfers.input J hJ
  | weaken L L₀ hp hs => exact ResInfers.weaken L L₀ (hE L₀ hp) hs
  | del A hp => exact ResInfers.del L (hE _ hp)
  | lin A B u v hp hq => exact ResInfers.lin A B u v (hE _ hp) (hE _ hq)
  | mul A u v hp => exact ResInfers.mul A u v (hE _ hp)

lemma valid_append {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ)
    {π ρ : List (RLine V)} (hπ : Valid Γ D π) (hρ : Valid Γ D ρ) : Valid Γ D (π++ρ) := by
  constructor
  · intro L hL u hu
    rcases List.mem_append.mp hL with hL | hL
    · exact hπ.1 L hL u hu
    · exact hρ.1 L hL u hu
  · intro k hk
    by_cases hkπ : k<π.length
    · rw [List.getElem_append_left hkπ]
      apply inference_mono Γ _ (hπ.2 k hkπ)
      intro L hL
      obtain ⟨j,hjk,hj⟩ := hL
      refine ⟨j,hjk,?_⟩
      rw [List.getElem?_append_left (by omega : j<π.length),hj]
    · obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hkπ)
      have hi : i<ρ.length := by simp only [List.length_append] at hk; omega
      have he : (π++ρ)[π.length+i]=ρ[i] := by
        simpa only [Nat.add_comm] using (List.getElem_append_right' π hi).symm
      rw [he]
      apply inference_mono Γ _ (hρ.2 i hi)
      intro L hL
      obtain ⟨j,hji,hj⟩ := hL
      refine ⟨π.length+j,by omega,?_⟩
      rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,hj]

lemma valid_snoc {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ)
    {π : List (RLine V)} (hπ : Valid Γ D π) (L : RLine V)
    (hL : ∀ u∈L, u.totalDegree≤D) (hinf : ResInfers Γ (fun M => M∈π) L) :
    Valid Γ D (π++[L]) := by
  constructor
  · intro M hM u hu
    rcases List.mem_append.mp hM with hM | hM
    · exact hπ.1 M hM u hu
    · have he : M=L := List.mem_singleton.mp hM
      subst M
      exact hL u hu
  · intro k hk
    by_cases hkπ : k<π.length
    · rw [List.getElem_append_left hkπ]
      apply inference_mono Γ _ (hπ.2 k hkπ)
      intro M hM
      obtain ⟨j,hjk,hj⟩ := hM
      exact ⟨j,hjk,by rw [List.getElem?_append_left (by omega : j<π.length),hj]⟩
    · have hkEq : k=π.length := by simp only [List.length_append,List.length_singleton] at hk; omega
      subst k
      have he : (π++[L])[π.length]=L := by
        simpa using (List.getElem_append_right' (l₂ := [L]) (i := 0) π (by simp)).symm
      rw [he]
      apply inference_mono Γ _ hinf
      intro M hM
      obtain ⟨j,hj,hval⟩ := List.mem_iff_getElem.mp hM
      refine ⟨j,hj,?_⟩
      rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj,hval]

end AC02Frege.Supplement.ResDerivation
end

section
-- Inlined Solutions.ResDerivationOperations

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.ResDerivation

open MvPolynomial LiftSAParity

lemma mono_size {V : Type} [DecidableEq V] {Γ : CNF V} {D m k : ℕ} {L : RLine V}
    (h : Derives Γ D L m) (hm : m≤k) : Derives Γ D L k := by
  obtain ⟨π,hπ,hL,hlen⟩ := h
  exact ⟨π,hπ,hL,hlen.trans hm⟩

lemma initial {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ) (L : RLine V)
    (hL : ∀ u∈L, u.totalDegree≤D) (hinf : ResInfers Γ (fun _ => False) L) : Derives Γ D L 1 := by
  refine ⟨[L],⟨by simpa using hL,?_⟩,by simp,by simp⟩
  intro k hk
  have he : k=0 := by simpa using hk
  subst k
  exact inference_mono Γ (fun _ h => h.elim) hinf

lemma unary {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ)
    {L P : RLine V} {m : ℕ} (hL : Derives Γ D L m)
    (hP : ∀ u∈P, u.totalDegree≤D) (hinf : ResInfers Γ (fun M => M=L) P) :
    Derives Γ D P (m+1) := by
  obtain ⟨π,hπ,hmem,hlen⟩ := hL
  have hi : ResInfers Γ (fun M => M∈π) P := inference_mono Γ (by
    intro M hM
    rwa [hM]) hinf
  refine ⟨π++[P],valid_snoc Γ D hπ P hP hi,by simp,?_⟩
  simp only [List.length_append,List.length_singleton]
  omega

lemma binary {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ)
    {L M P : RLine V} {m k : ℕ} (hL : Derives Γ D L m) (hM : Derives Γ D M k)
    (hP : ∀ u∈P, u.totalDegree≤D) (hinf : ResInfers Γ (fun N => N=L ∨ N=M) P) :
    Derives Γ D P (m+k+1) := by
  obtain ⟨π,hπ,hLmem,hπlen⟩ := hL
  obtain ⟨ρ,hρ,hMmem,hρlen⟩ := hM
  have hi : ResInfers Γ (fun N => N∈π++ρ) P := inference_mono Γ (by
    intro N hN
    rcases hN with rfl | rfl
    · exact List.mem_append_left ρ hLmem
    · exact List.mem_append_right π hMmem) hinf
  refine ⟨(π++ρ)++[P],valid_snoc Γ D (valid_append Γ D hπ hρ) P hP hi,by simp,?_⟩
  simp only [List.length_append,List.length_singleton]
  omega

lemma one {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ) : Derives Γ D {1} 1 :=
  initial Γ D {1} (by intro u hu; have he : u=1 := Finset.mem_singleton.mp hu; subst u; simp) ResInfers.axOne

lemma add_units {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ)
    {p u : MvPolynomial V (ZMod 2)} {m k : ℕ}
    (hp : Derives Γ D {1+p} m) (hu : Derives Γ D {1+u} k)
    (hdeg : (p+u).totalDegree≤D) : Derives Γ D {1+(p+u)} (m+k+1) := by
  apply binary Γ D hp hu
  · intro v hv
    have he : v=1+(p+u) := Finset.mem_singleton.mp hv
    subst v
    exact (totalDegree_add _ _).trans (max_le (by simp) hdeg)
  · have hi := ResInfers.lin (Γ := Γ) (E := fun N => N={1+p} ∨ N={1+u}) ∅ ∅ (1+p) (1+u)
      (by simp) (by simp)
    have he : 1+(1+p)+(1+u)=1+(p+u) := by
      rw [CharTwo.add_cancel_left]
      ring
    simpa only [Finset.empty_union,Finset.insert_empty,he] using hi

lemma multiply_unit {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ)
    {p u : MvPolynomial V (ZMod 2)} {m : ℕ} (hp : Derives Γ D {1+p} m)
    (hdeg : (p*u).totalDegree≤D) : Derives Γ D {1+p*u} (m+1) := by
  apply unary Γ D hp
  · intro v hv
    have he : v=1+p*u := Finset.mem_singleton.mp hv
    subst v
    exact (totalDegree_add _ _).trans (max_le (by simp) hdeg)
  · have hi := ResInfers.mul (Γ := Γ) (E := fun N => N={1+p}) ∅ (1+p) u (by simp)
    simpa only [CharTwo.add_cancel_left,Finset.insert_empty] using hi

end AC02Frege.Supplement.ResDerivation
end

section
-- Inlined Solutions.SelectorInputLines

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorInputLines

open MvPolynomial LiftSAParity SelectorRestrictionBasics

lemma selected_positive {V : Type} {q : ℕ} (A : V → Bool → Fin q) (i : V) (b : Bool) :
    restrictPoly A (litPoly ((i,b,A i b),true))=litPoly (i,b) := by
  simp only [litPoly,↓reduceIte,restrict_X,selRho,if_pos rfl]

lemma unchosen_negative {V : Type} {q : ℕ} (A : V → Bool → Fin q) (i : V) (b : Bool)
    (a : Fin q) (ha : a≠A i b) : restrictPoly A (litPoly ((i,b,a),false))=1 := by
  simp only [litPoly,Bool.false_eq_true,↓reduceIte,restrict_add,restrict_one,restrict_X,
    selRho,if_neg ha,add_zero]

lemma selected_negative {V : Type} {q : ℕ} (A : V → Bool → Fin q) (i : V) (b : Bool) :
    restrictPoly A (litPoly ((i,b,A i b),false))=litPoly (i,!b) := by
  cases b <;> simp [litPoly,restrict_add,restrict_one,restrict_X,selRho,CharTwo.add_cancel_left]

lemma original_clause_subset {V : Type} [DecidableEq V] {q : ℕ} (A : V → Bool → Fin q)
    (J : Clause V) : J.image litPoly ⊆ restrictLine A ((selClause q J).image litPoly) := by
  intro p hp
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hp
  apply Finset.mem_image.mpr
  refine ⟨litPoly ((l.1,l.2,A l.1 l.2),true), ?_, selected_positive A l.1 l.2⟩
  apply Finset.mem_image.mpr
  refine ⟨((l.1,l.2,A l.1 l.2),true), ?_, rfl⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨l,hl,Finset.mem_image.mpr ⟨A l.1 l.2,Finset.mem_univ _,rfl⟩⟩

lemma at_least_one_subset {V : Type} [DecidableEq V] {q : ℕ} (A : V → Bool → Fin q) (i : V) :
    ({X i,1+X i} : RLine V) ⊆ restrictLine A
      (Finset.image litPoly ((Finset.univ : Finset (Bool×Fin q)).image (fun x => ((i,x.1,x.2),true)))) := by
  have hmem (b : Bool) : litPoly (i,b) ∈ restrictLine A
      (Finset.image litPoly ((Finset.univ : Finset (Bool×Fin q)).image (fun x => ((i,x.1,x.2),true)))) := by
    apply Finset.mem_image.mpr
    refine ⟨litPoly ((i,b,A i b),true),?_,selected_positive A i b⟩
    apply Finset.mem_image.mpr
    exact ⟨((i,b,A i b),true),Finset.mem_image.mpr ⟨(b,A i b),Finset.mem_univ _,rfl⟩,rfl⟩
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · simpa [litPoly] using hmem true
  · have he : p=1+X i := Finset.mem_singleton.mp hp
    subst p
    simpa [litPoly] using hmem false

lemma exclusion_origin {V : Type} [DecidableEq V] {q : ℕ} (A : V → Bool → Fin q) (i : V)
    (x y : Bool×Fin q) (hne : x≠y) :
    let L := restrictLine A (({((i,x.1,x.2),false),((i,y.1,y.2),false)} : Clause (V×Bool×Fin q)).image litPoly)
    (1 : MvPolynomial V (ZMod 2))∈L ∨ ({X i,1+X i} : RLine V)⊆L := by
  intro L
  have hleft : restrictPoly A (litPoly ((i,x.1,x.2),false))∈L := by
    exact Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨_,Finset.mem_insert_self _ _,rfl⟩,rfl⟩
  have hright : restrictPoly A (litPoly ((i,y.1,y.2),false))∈L := by
    exact Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨_,Finset.mem_insert_of_mem (Finset.mem_singleton_self _),rfl⟩,rfl⟩
  by_cases hx : x.2=A i x.1
  · by_cases hy : y.2=A i y.1
    · have hrow : x.1≠y.1 := by
        intro he
        apply hne
        exact Prod.ext he (by rw [hx,hy,he])
      right
      rw [hx,selected_negative] at hleft
      rw [hy,selected_negative] at hright
      rcases x with ⟨b,a⟩
      rcases y with ⟨b',a'⟩
      cases b <;> cases b' <;> simp_all [litPoly,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · left
      rwa [unchosen_negative A i y.1 y.2 hy] at hright
  · left
    rwa [unchosen_negative A i x.1 x.2 hx] at hleft

theorem input_origin {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (A : V → Bool → Fin q) (F : CNF V) (J : Clause (V×Bool×Fin q)) (hJ : J∈selSubst F q) :
    (∃ C∈F, C.image litPoly⊆restrictLine A (J.image litPoly)) ∨
      (1 : MvPolynomial V (ZMod 2))∈restrictLine A (J.image litPoly) ∨
      ∃ i : V, ({X i,1+X i} : RLine V)⊆restrictLine A (J.image litPoly) := by
  rcases Finset.mem_union.mp hJ with hsel | hhot
  · obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hsel
    exact Or.inl ⟨C,hC,original_clause_subset A C⟩
  · obtain ⟨i,hi,hJi⟩ := Finset.mem_biUnion.mp hhot
    rcases Finset.mem_insert.mp hJi with rfl | hpair
    · exact Or.inr (Or.inr ⟨i,at_least_one_subset A i⟩)
    · obtain ⟨xy,hxy,rfl⟩ := Finset.mem_image.mp hpair
      have hne := (Finset.mem_filter.mp hxy).2
      rcases exclusion_origin A i xy.1 xy.2 hne with hone | hbool
      · exact Or.inr (Or.inl hone)
      · exact Or.inr (Or.inr ⟨i,hbool⟩)

lemma literal_line_degree {V : Type} [DecidableEq V] (C : Clause V) (D : ℕ) (hD : 1≤D) :
    ∀ p∈C.image litPoly, p.totalDegree≤D := by
  intro p hp
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hp
  have h : (litPoly l).totalDegree≤1 := by
    rcases l with ⟨i,b⟩
    cases b
    · exact (totalDegree_add _ _).trans (by simp [litPoly])
    · simp [litPoly]
  exact h.trans hD

lemma boolean_line_degree {V : Type} [DecidableEq V] (i : V) (D : ℕ) (hD : 1≤D) :
    ∀ p∈({X i,1+X i} : RLine V), p.totalDegree≤D := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · simpa using hD
  · have he : p=1+X i := Finset.mem_singleton.mp hp
    subst p
    exact (totalDegree_add _ _).trans (by simpa using hD)

theorem initial_derivation {V : Type} [Fintype V] [DecidableEq V] (F : CNF V) (D : ℕ) (hD : 1≤D)
    (L : RLine V) (hL : ∀ p∈L, p.totalDegree≤D)
    (horigin : (∃ C∈F, C.image litPoly⊆L) ∨ (1 : MvPolynomial V (ZMod 2))∈L ∨
      ∃ i : V, ({X i,1+X i} : RLine V)⊆L) : ResDerivation.Derives F D L 2 := by
  rcases horigin with ⟨C,hC,hsub⟩ | hone | ⟨i,hsub⟩
  · have hb := ResDerivation.initial F D (C.image litPoly) (literal_line_degree C D hD)
      (ResInfers.input C hC)
    exact ResDerivation.unary F D hb hL (ResInfers.weaken L (C.image litPoly) rfl hsub)
  · exact ResDerivation.unary F D (ResDerivation.one F D) hL
      (ResInfers.weaken L {1} rfl (Finset.singleton_subset_iff.mpr hone))
  · have hb := ResDerivation.initial F D ({X i,1+X i} : RLine V) (boolean_line_degree i D hD)
      (ResInfers.axBool i)
    exact ResDerivation.unary F D hb hL (ResInfers.weaken L {X i,1+X i} rfl hsub)

theorem restricted_input_derivation {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (A : V → Bool → Fin q) (F : CNF V) (D : ℕ) (hD : 1≤D)
    (J : Clause (V×Bool×Fin q)) (hJ : J∈selSubst F q)
    (hdeg : ∀ p∈restrictLine A (J.image litPoly), p.totalDegree≤D) :
    ResDerivation.Derives F D (restrictLine A (J.image litPoly)) 2 :=
  initial_derivation F D hD _ hdeg (input_origin A F J hJ)

theorem default_origin {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (A : V → Bool → Fin q) (x : V×Bool×Fin q) :
    (1 : MvPolynomial V (ZMod 2))∈restrictLine A {X x,1+X x} ∨
      ({X x.1,1+X x.1} : RLine V)⊆restrictLine A {X x,1+X x} := by
  have he : restrictLine A ({X x,1+X x} : RLine (V×Bool×Fin q))=
      {selRho A x,1+selRho A x} := by
    simp only [restrictLine,Finset.image_insert,Finset.image_singleton,restrict_add,restrict_one,restrict_X]
  rw [he]
  by_cases hc : x.2.2=A x.1 x.2.1
  · right
    unfold selRho
    rw [if_pos hc]
    cases hb : x.2.1 <;> simp [CharTwo.add_cancel_left,Finset.pair_comm]
  · left
    simp only [selRho,if_neg hc,add_zero]
    simp

end AC02Frege.Supplement.SelectorInputLines
end

section
-- Inlined Solutions.ResBooleanUnits

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.ResDerivation

open MvPolynomial LiftSAParity

lemma boolean_unit {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ) (hD : 2≤D) (v : V) :
    Derives Γ D {1+(X v^2+X v)} 3 := by
  classical
  let x : MvPolynomial V (ZMod 2) := X v
  let w := 1+(x^2+x)
  have hx : x.totalDegree≤D := by dsimp [x]; simpa using (show 1≤D by omega)
  have hxb : (1+x).totalDegree≤D := (totalDegree_add _ _).trans (max_le (by simp) hx)
  have hwd : w.totalDegree≤D := by
    apply (totalDegree_add _ _).trans
    apply max_le (by simp)
    exact (totalDegree_add _ _).trans (by dsimp [x]; simp only [totalDegree_X_pow,totalDegree_X]; omega)
  have hax : Derives Γ D {x,1+x} 1 := initial Γ D _ (by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hx
    · have he : u=1+x := Finset.mem_singleton.mp hu
      subst u
      exact hxb) (ResInfers.axBool v)
  let L := insert w ({1+x} : RLine V)
  have hw₁ : 1+(1+x)*x=w := by dsimp [w]; ring
  have hfirst : Derives Γ D L 2 := by
    apply unary Γ D hax
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hwd
      · have he : u=1+x := Finset.mem_singleton.mp hu
        subst u
        exact hxb
    · have hi := ResInfers.mul (Γ := Γ) (E := fun M => M={x,1+x}) {1+x} x x (by rfl)
      simpa only [hw₁] using hi
  have hw₂ : 1+x*(1+x)=w := by dsimp [w]; ring
  apply unary Γ D hfirst
  · intro u hu
    have he : u=w := Finset.mem_singleton.mp hu
    subst u
    exact hwd
  · have hi := ResInfers.mul (Γ := Γ) (E := fun M => M=L) {w} (1+x) (1+x) (by
      dsimp only [L]
      ext z
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact or_comm)
    simpa only [CharTwo.add_cancel_left,hw₂,Finset.insert_eq_of_mem (Finset.mem_singleton_self w)] using hi

end AC02Frege.Supplement.ResDerivation
end

section
-- Inlined Solutions.ResMonomialReduction

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.ResDerivation

open MvPolynomial LiftSAParity AC02Frege.BooleanAlgebra

theorem monomial_difference {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ) (hD : 2≤D)
    (s : V →₀ ℕ) (c : ZMod 2) (hdeg : s.sum (fun _ e => e)≤D) :
    Derives Γ D {1+(monomial s c+monomial (sqfree s) c)} (5*s.sum (fun _ e => e)+1) := by
  classical
  induction hs : s.sum (fun _ e => e) using Nat.strong_induction_on generalizing s with
  | h k ih =>
    by_cases hsq : ∀ i, s i≤1
    · have he : sqfree s=s := sqfree_eq_self s hsq
      rw [he,CharTwo.add_self_eq_zero,add_zero]
      exact mono_size (one Γ D) (by omega)
    obtain ⟨i,hi⟩ := not_forall.mp hsq
    have hi2 : 2 ≤ s i := by omega
    let r := s-Finsupp.single i 2
    have hle : Finsupp.single i 2 ≤ s := by
      intro j
      by_cases hj : j=i
      · subst j; simpa using hi2
      · simp [Finsupp.single_apply,hj]
    have heq : r+Finsupp.single i 2=s := tsub_add_cancel_of_le hle
    let t := r+Finsupp.single i 1
    have hsum : r.sum (fun _ e => e)+2=s.sum (fun _ e => e) := by
      have hh := congrArg (fun z : V →₀ ℕ => z.sum (fun _ e => e)) heq
      simpa [Finsupp.sum_add_index'] using hh
    have htsum : t.sum (fun _ e => e)=r.sum (fun _ e => e)+1 := by
      simp [t,Finsupp.sum_add_index']
    have hsqeq : sqfree t=sqfree s := by
      rw [← heq]
      ext j
      by_cases hj : j=i
      · subst j
        simp only [sqfree,Finsupp.mapRange_apply,t,Finsupp.add_apply,Finsupp.single_eq_same]
        omega
      · simp [sqfree,Finsupp.mapRange_apply,t,Finsupp.single_apply,hj]
    have hBdeg : (X i^2+X i : MvPolynomial V (ZMod 2)).totalDegree≤2 :=
      (totalDegree_add _ _).trans (by simp)
    have hrdeg : (monomial r c : MvPolynomial V (ZMod 2)).totalDegree≤r.sum (fun _ e => e) :=
      totalDegree_monomial_le r c
    have hproddeg : ((X i^2+X i)*monomial r c : MvPolynomial V (ZMod 2)).totalDegree≤D :=
      (totalDegree_mul _ _).trans (by omega)
    have hfactor : monomial s c+monomial t c=(X i^2+X i)*monomial r c := by
      calc
        _ = monomial (r+Finsupp.single i 2) c+monomial (r+Finsupp.single i 1) c := by rw [heq]
        _ = _ := by simp only [monomial_add_single,pow_one,mul_add]; ring
    have hstep : Derives Γ D {1+(monomial s c+monomial t c)} 4 := by
      rw [hfactor]
      exact multiply_unit Γ D (boolean_unit Γ D hD i) hproddeg
    have htdeg : t.sum (fun _ e => e)≤D := by omega
    have htlt : t.sum (fun _ e => e)<k := by omega
    have hrec := ih _ htlt t htdeg rfl
    have hsd : (monomial s c : MvPolynomial V (ZMod 2)).totalDegree≤D :=
      (totalDegree_monomial_le _ _).trans hdeg
    have htd : (monomial t c : MvPolynomial V (ZMod 2)).totalDegree≤D :=
      (totalDegree_monomial_le _ _).trans htdeg
    have hsqdeg : (monomial (sqfree t) c : MvPolynomial V (ZMod 2)).totalDegree≤D := by
      rw [← ml_monomial]
      exact (AC02Frege.BooleanFlip.ml_totalDegree_le _).trans htd
    have hadddeg : ((monomial s c+monomial t c)+(monomial t c+monomial (sqfree t) c) :
        MvPolynomial V (ZMod 2)).totalDegree≤D :=
      (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le hsd htd))
        ((totalDegree_add _ _).trans (max_le htd hsqdeg)))
    have hres := add_units Γ D hstep hrec hadddeg
    have hres' : Derives Γ D {1+(monomial s c+monomial (sqfree s) c)}
        (4+(5*t.sum (fun _ e => e)+1)+1) := by
      simpa only [hsqeq,add_assoc,CharTwo.add_cancel_left] using hres
    exact mono_size hres' (by omega)

end AC02Frege.Supplement.ResDerivation
end

section
-- Inlined Solutions.ResPolynomialReduction

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.ResDerivation

open MvPolynomial LiftSAParity AC02Frege.BooleanAlgebra AC02Frege.BooleanFlip

theorem polynomial_difference {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ) (hD : 2≤D)
    (p : MvPolynomial V (ZMod 2)) (hdeg : p.totalDegree≤D) :
    Derives Γ D {1+(p+ML p)} ((5*D+2)*p.support.card+1) := by
  classical
  let term := fun s => monomial s (coeff s p)+monomial (sqfree s) (coeff s p)
  have hterm (s) (hs : s∈p.support) : (term s).totalDegree≤D := by
    have hm : (monomial s (coeff s p)).totalDegree≤D :=
      (totalDegree_monomial_le _ _).trans ((le_totalDegree hs).trans hdeg)
    have hml : (monomial (sqfree s) (coeff s p)).totalDegree≤D := by
      rw [← ml_monomial]
      exact (ml_totalDegree_le _).trans hm
    exact (totalDegree_add _ _).trans (max_le hm hml)
  have hproof (s) (hs : s∈p.support) : Derives Γ D {1+term s} (5*D+1) := by
    have hd := (le_totalDegree hs).trans hdeg
    exact mono_size (monomial_difference Γ D hD s (coeff s p) hd) (by omega)
  have hsum : ∀ S : Finset (V →₀ ℕ), S⊆p.support →
      Derives Γ D {1+∑ s∈S, term s} ((5*D+2)*S.card+1) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro hS; simpa using one Γ D
    | @insert s S hs ih =>
      intro hS
      have hsP := hS (Finset.mem_insert_self _ _)
      have hSP : S⊆p.support := fun t ht => hS (Finset.mem_insert_of_mem ht)
      have hd : (term s+∑ t∈S, term t).totalDegree≤D :=
        (totalDegree_add _ _).trans (max_le (hterm s hsP)
          (totalDegree_finsetSum_le (fun t ht => hterm t (hSP ht))))
      have hh := add_units Γ D (hproof s hsP) (ih hSP) hd
      rw [Finset.sum_insert hs,Finset.card_insert_of_notMem hs]
      exact mono_size hh (by nlinarith)
  have he : p+ML p=∑ s∈p.support, term s := by
    dsimp only [term]
    rw [Finset.sum_add_distrib,support_sum_monomial_coeff]
    congr 1
    conv_lhs => rw [p.as_sum]
    simp only [map_sum,ml_monomial]
  rw [he]
  exact hsum p.support (fun _ h => h)

theorem boolean_zero_unit {V : Type} [DecidableEq V] (Γ : CNF V) (D : ℕ) (hD : 2≤D)
    (p : MvPolynomial V (ZMod 2)) (hdeg : p.totalDegree≤D) (hzero : ML p=0) :
    Derives Γ D {1+p} ((5*D+2)*p.support.card+1) := by
  simpa only [hzero,add_zero] using polynomial_difference Γ D hD p hdeg

end AC02Frege.Supplement.ResDerivation
end

section
-- Inlined Solutions.BoundedMonomialCount

set_option maxHeartbeats 2000000

namespace ProofComplexity.BoundedMonomialCount

open MvPolynomial

noncomputable def word {V : Type} (s : V →₀ ℕ) : List (Option V) :=
  s.support.toList.flatMap (fun i => List.replicate (s i) (some i))

lemma word_length {V : Type} (s : V →₀ ℕ) : (word s).length=s.sum (fun _ e => e) := by
  classical
  simp only [word,List.length_flatMap,List.length_replicate]
  rw [Finset.sum_map_toList]
  rfl

lemma word_count {V : Type} [DecidableEq V] (s : V →₀ ℕ) (i : V) :
    (word s).count (some i)=s i := by
  simp only [word,List.count_flatMap,Function.comp_def,List.count_replicate,beq_iff_eq,Option.some.injEq]
  rw [Finset.sum_map_toList]
  by_cases hi : i∈s.support
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp only [if_neg hji]
    · exact fun h => (h hi).elim
  · have hs : s i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hi
    rw [hs]
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j≠i := by intro he; subst j; exact hi hj
    simp only [if_neg hji]

noncomputable def padded {V : Type} (D : ℕ) (s : V →₀ ℕ)
    (hs : s.sum (fun _ e => e)≤D) : List.Vector (Option V) D :=
  ⟨word s++List.replicate (D-s.sum (fun _ e => e)) none, by
    rw [List.length_append,word_length,List.length_replicate]
    omega⟩

lemma padded_count {V : Type} [DecidableEq V] (D : ℕ) (s : V →₀ ℕ)
    (hs : s.sum (fun _ e => e)≤D) (i : V) :
    (padded D s hs).1.count (some i)=s i := by
  simp [padded,List.count_append,word_count,List.count_replicate]

theorem support_card_le {V : Type} [Fintype V] [DecidableEq V] {R : Type} [CommSemiring R]
    (p : MvPolynomial V R) (D : ℕ) (hD : p.totalDegree≤D) :
    p.support.card≤(Fintype.card V+1)^D := by
  let f : p.support → List.Vector (Option V) D := fun s => padded D s.1 ((le_totalDegree s.2).trans hD)
  have hinj : Function.Injective f := by
    intro s t he
    apply Subtype.ext
    ext i
    have hh := congrArg (fun v : List.Vector (Option V) D => v.1.count (some i)) he
    simpa only [f,padded_count] using hh
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe,card_vector,Fintype.card_option,Nat.add_comm] using hc

end ProofComplexity.BoundedMonomialCount
end

section
-- Inlined Solutions.ResReductionSize

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.ResDerivation

open MvPolynomial LiftSAParity

lemma reduction_overhead (n d : ℕ) (hn : 2≤n) (hd : 2≤d) :
    (10*d+2)*(n+1)^(2*d)+1≤n^(8*d) := by
  have hdPow : d≤n^d := (show d<2^d from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hn d)
  have h12 : 12≤n^(2*d) := by
    have h16 : 16≤n^4 := by exact_mod_cast (Nat.pow_le_pow_left hn 4)
    have hm : n^4≤n^(2*d) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hfactor : 10*d+2≤n^(3*d) := by
    calc
      _ ≤ 12*d := by omega
      _ ≤ n^(2*d)*n^d := Nat.mul_le_mul h12 hdPow
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hbase : n+1≤n^2 := by nlinarith
  have hpower : (n+1)^(2*d)≤n^(4*d) := by
    calc
      _ ≤ (n^2)^(2*d) := Nat.pow_le_pow_left hbase _
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hmain : (10*d+2)*(n+1)^(2*d)≤n^(7*d) := by
    calc
      _ ≤ n^(3*d)*n^(4*d) := Nat.mul_le_mul hfactor hpower
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hnd : 2≤n^d := by
    have hm : n^1≤n^d := Nat.pow_le_pow_right (by omega) (by omega)
    exact hn.trans (by simpa only [pow_one] using hm)
  have hpos : 1≤n^(7*d) := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ n^(7*d)+1 := Nat.add_le_add_right hmain 1
    _ ≤ 2*n^(7*d) := by omega
    _ ≤ n^d*n^(7*d) := Nat.mul_le_mul_right _ hnd
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem boolean_zero_unit_bound {V : Type} [Fintype V] [DecidableEq V]
    (Γ : CNF V) (d : ℕ) (hn : 2≤Fintype.card V) (hd : 2≤d)
    (p : MvPolynomial V (ZMod 2)) (hdeg : p.totalDegree≤2*d) (hzero : ML p=0) :
    Derives Γ (2*d) {1+p} ((Fintype.card V)^(8*d)) := by
  have hp := boolean_zero_unit Γ (2*d) (by omega) p hdeg hzero
  have hs := ProofComplexity.BoundedMonomialCount.support_card_le p (2*d) hdeg
  have hcount : (5*(2*d)+2)*p.support.card+1≤(10*d+2)*(Fintype.card V+1)^(2*d)+1 := by
    have hh := Nat.add_le_add_right (Nat.mul_le_mul_left (10*d+2) hs) 1
    convert hh using 1 <;> ring
  exact mono_size hp (hcount.trans (reduction_overhead (Fintype.card V) d hn hd))

end AC02Frege.Supplement.ResDerivation
end

section
-- Inlined Solutions.ResMultiplicationRepair

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.ResDerivation

open MvPolynomial LiftSAParity AC02Frege.BooleanAlgebra

theorem repair {V : Type} [Fintype V] [DecidableEq V] (Γ : CNF V) (d : ℕ)
    (hn : 2≤Fintype.card V) (hd : 2≤d)
    (a b : MvPolynomial V (ZMod 2)) (ha : a.totalDegree<d) (hb : b.totalDegree<d)
    (hrel : ML (b+a*b)=0) (A : RLine V) (hA : ∀ u∈A, u.totalDegree≤2*d)
    (π : List (RLine V)) (hπ : Valid Γ (2*d) π) (hprem : insert (1+a) A∈π) :
    ∃ ρ : List (RLine V), Valid Γ (2*d) ρ ∧ π.IsPrefix ρ ∧
      insert (1+b) A∈ρ ∧ ρ.length≤π.length+(Fintype.card V)^(8*d)+2 := by
  classical
  have hab : (a*b).totalDegree≤2*d := (totalDegree_mul _ _).trans (by omega)
  have hpdeg : (b+a*b).totalDegree≤2*d :=
    (totalDegree_add _ _).trans (max_le (by omega) hab)
  obtain ⟨σ,hσ,hunit,hσlen⟩ := boolean_zero_unit_bound Γ d hn hd (b+a*b) hpdeg hrel
  let M := insert (1+a*b) A
  let L := insert (1+b) A
  have hM : ∀ u∈M, u.totalDegree≤2*d := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact (totalDegree_add _ _).trans (max_le (by simp) hab)
    · exact hA u hu
  have hL : ∀ u∈L, u.totalDegree≤2*d := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact (totalDegree_add _ _).trans (max_le (by simp) (by omega))
    · exact hA u hu
  have hmid : Valid Γ (2*d) ((π++σ)++[M]) := by
    apply valid_snoc Γ (2*d) (valid_append Γ (2*d) hπ hσ) M hM
    have hi := ResInfers.mul (Γ := Γ) (E := fun N => N∈π++σ) A (1+a) b
      (List.mem_append_left σ hprem)
    simpa only [CharTwo.add_cancel_left] using hi
  have hlast : Valid Γ (2*d) (((π++σ)++[M])++[L]) := by
    apply valid_snoc Γ (2*d) hmid L hL
    have hi := ResInfers.lin (Γ := Γ) (E := fun N => N∈(π++σ)++[M]) A ∅
      (1+a*b) (1+(b+a*b)) (by simp [M]) (by simpa using List.mem_append_left [M] (List.mem_append_right π hunit))
    have he : 1+(1+a*b)+(1+(b+a*b))=1+b := by
      rw [CharTwo.add_cancel_left]
      have hh : a*b+(1+(b+a*b))=1+b := by
        calc
          _ = (a*b+(a*b+(1+b))) := by ring
          _ = _ := CharTwo.add_cancel_left _ _
      exact hh
    simpa only [he,Finset.union_empty,Finset.insert_empty] using hi
  refine ⟨((π++σ)++[M])++[L],hlast,?_,by simp [L],?_⟩
  · exact ⟨σ++[M]++[L],by simp only [List.append_assoc]⟩
  · simp only [List.length_append,List.length_singleton]
    omega

end AC02Frege.Supplement.ResDerivation
end

section
-- Inlined Solutions.FinitePinningCount

set_option maxHeartbeats 2000000

namespace ProofComplexity.FinitePinningCount

noncomputable def restrictionEquiv {I A : Type} [DecidableEq I]
    (S : Finset I) (f : I → A) :
    {g : I → A // ∀ i∈S, g i=f i} ≃ ({i : I // i∉S} → A) where
  toFun g i := g.1 i.1
  invFun h := ⟨fun i => if hi : i∈S then f i else h ⟨i,hi⟩, by
    intro i hi
    simp only [dif_pos hi]⟩
  left_inv g := by
    apply Subtype.ext
    funext i
    by_cases hi : i∈S
    · simp only [dif_pos hi]
      exact (g.2 i hi).symm
    · simp only [dif_neg hi]
  right_inv h := by
    funext i
    simp only [dif_neg i.2]

theorem pinned_card {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (S : Finset I) (f : I → A) :
    Fintype.card {g : I → A // ∀ i∈S, g i=f i} =
      Fintype.card A^(Fintype.card I-S.card) := by
  classical
  rw [Fintype.card_congr (restrictionEquiv S f),Fintype.card_fun]
  congr 1
  have he : (Finset.univ.filter (fun i : I => i∉S))=Finset.univ\S := by ext i; simp
  rw [Fintype.card_subtype,he,Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ]

theorem filter_card {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (S : Finset I) (f : I → A) :
    ((Finset.univ : Finset (I → A)).filter (fun (g : I → A) => ∀ i∈S, g i=f i)).card =
      Fintype.card A^(Fintype.card I-S.card) := by
  classical
  rw [← Fintype.card_subtype]
  exact pinned_card S f

theorem probability_bound {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (S : Finset I) (f : I → A) (d : ℕ) (hd : d≤S.card) (hA : 1≤Fintype.card A) :
    (((Finset.univ : Finset (I → A)).filter (fun (g : I → A) => ∀ i∈S, g i=f i)).card : ℝ) ≤
      (Fintype.card A : ℝ)^(Fintype.card I)/(Fintype.card A : ℝ)^d := by
  classical
  rw [filter_card]
  have hS : S.card≤Fintype.card I := Finset.card_le_univ S
  have hle : Fintype.card I-S.card≤Fintype.card I-d := by omega
  have hApos : (0 : ℝ)<(Fintype.card A : ℝ) := by exact_mod_cast (show 0<Fintype.card A by omega)
  have hAone : (1 : ℝ)≤(Fintype.card A : ℝ) := by exact_mod_cast hA
  push_cast
  calc
    _ ≤ (Fintype.card A : ℝ)^(Fintype.card I-d) := pow_le_pow_right₀ hAone hle
    _ = _ := by rw [pow_sub₀ (Fintype.card A : ℝ) hApos.ne' (by omega : d≤Fintype.card I),div_eq_mul_inv]

end ProofComplexity.FinitePinningCount
end

section
-- Inlined Solutions.SelectorMonomials

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorMonomials

open MvPolynomial AC02Frege.BooleanAlgebra SelectorRestrictionBasics

lemma zero_or_one (a : ZMod 2) : a=0 ∨ a=1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma rho_pair_zero {V : Type} {q : ℕ} (A : V → Bool → Fin q)
    (x y : V×Bool×Fin q) (hblock : x.1=y.1) (hne : x≠y) (z : V → ZMod 2) :
    eval z (selRho A x)=0 ∨ eval z (selRho A y)=0 := by
  by_cases hx : x.2.2=A x.1 x.2.1
  · by_cases hy : y.2.2=A y.1 y.2.1
    · have hrow : x.2.1≠y.2.1 := by
        intro he
        apply hne
        apply Prod.ext hblock
        apply Prod.ext he
        rw [hx,hy,hblock,he]
      have hv := zero_or_one (z x.1)
      rcases x with ⟨i,b,a⟩
      rcases y with ⟨j,b',a'⟩
      dsimp only at hblock hrow hx hy hv ⊢
      subst j
      rcases hv with hv | hv <;> cases b <;> cases b' <;>
        simp_all [selRho,CharTwo.add_self_eq_zero]
    · exact Or.inr (by simp only [selRho,if_neg hy,map_zero])
  · exact Or.inl (by simp only [selRho,if_neg hx,map_zero])

lemma monomial_collision {V : Type} [Fintype V] {q : ℕ} (A : V → Bool → Fin q)
    (s : (V×Bool×Fin q) →₀ ℕ) (c : ZMod 2) (x y : V×Bool×Fin q)
    (hx : x∈s.support) (hy : y∈s.support) (hblock : x.1=y.1) (hne : x≠y) :
    restrictPoly A (monomial s c)=0 := by
  apply multilinear_ext (restrict_multilinear A _) (by simpa using ml_multilinear (0 : MvPolynomial V (ZMod 2)))
  intro z
  rw [eval_restrict,eval_monomial,map_zero]
  have hp : s.prod (fun a k => (eval z (selRho A a))^k)=0 := by
    rcases rho_pair_zero A x y hblock hne z with hz | hz
    · exact Finset.prod_eq_zero hx (by
        change (eval z (selRho A x))^(s x)=0
        rw [hz,zero_pow (Finsupp.mem_support_iff.mp hx)])
    · exact Finset.prod_eq_zero hy (by
        change (eval z (selRho A y))^(s y)=0
        rw [hz,zero_pow (Finsupp.mem_support_iff.mp hy)])
  rw [hp,mul_zero]

lemma monomial_product {V : Type} [Fintype V] {q : ℕ} (A : V → Bool → Fin q)
    (s : (V×Bool×Fin q) →₀ ℕ) (c : ZMod 2) :
    restrictPoly A (monomial s c)=ML (C c*∏ y∈s.support, selRho A y) := by
  apply multilinear_ext (restrict_multilinear A _) (ml_multilinear _)
  intro z
  rw [eval_restrict,eval_monomial,eval_ml,map_mul,eval_C,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro y hy
  exact f2_pow_of_pos _ _ (by exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hy))

lemma monomial_degree {V : Type} [Fintype V] {q : ℕ} (A : V → Bool → Fin q)
    (s : (V×Bool×Fin q) →₀ ℕ) (c : ZMod 2) :
    (restrictPoly A (monomial s c)).totalDegree ≤ s.support.card := by
  rw [monomial_product]
  apply (AC02Frege.BooleanFlip.ml_totalDegree_le _).trans
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C,zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _y∈s.support, 1 := Finset.sum_le_sum (fun y hy => rho_degree A y)
    _ = _ := by simp

noncomputable def rows {V : Type} [DecidableEq V] {q : ℕ}
    (s : (V×Bool×Fin q) →₀ ℕ) : Finset (V×Bool) :=
  s.support.image (fun x => (x.1,x.2.1))

lemma nonzero_requirements {V : Type} [Fintype V] {q : ℕ} (A : V → Bool → Fin q)
    (s : (V×Bool×Fin q) →₀ ℕ) (c : ZMod 2) (hn : restrictPoly A (monomial s c)≠0) :
    (∀ y∈s.support, y.2.2=A y.1 y.2.1) ∧
      Set.InjOn (fun y : V×Bool×Fin q => y.1) (s.support : Set (V×Bool×Fin q)) := by
  constructor
  · intro y hy
    by_contra hbad
    exact hn (monomial_unchosen A s c y hy hbad)
  · intro x hx y hy hblock
    by_contra hne
    exact hn (monomial_collision A s c x y hx hy hblock hne)

lemma rows_card {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (A : V → Bool → Fin q)
    (s : (V×Bool×Fin q) →₀ ℕ) (c : ZMod 2) (hn : restrictPoly A (monomial s c)≠0) :
    (rows s).card=s.support.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  exact (nonzero_requirements A s c hn).2 hx hy (congrArg (fun z : V×Bool => z.1) he)

theorem monomial_tail {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (hq : 2≤q)
    (s : (V×Bool×Fin q) →₀ ℕ) (c : ZMod 2) (d : ℕ) (hd : 1≤d) :
    (((Finset.univ : Finset ((V×Bool) → Fin q)).filter (fun g =>
      d≤(restrictPoly (fun v b => g (v,b)) (monomial s c)).totalDegree)).card : ℝ) ≤
      (q : ℝ)^(2*Fintype.card V)/(q : ℝ)^d := by
  let Bad := fun g : (V×Bool) → Fin q =>
    d≤(restrictPoly (fun v b => g (v,b)) (monomial s c)).totalDegree
  by_cases hsome : ∃ g, Bad g
  · obtain ⟨g₀,hg₀⟩ := hsome
    have hnon (g) (hg : Bad g) : restrictPoly (fun v b => g (v,b)) (monomial s c)≠0 := by
      intro hz
      change d≤(restrictPoly (fun v b => g (v,b)) (monomial s c)).totalDegree at hg
      rw [hz,totalDegree_zero] at hg
      omega
    have hrows : d≤(rows s).card := by
      rw [rows_card (fun v b => g₀ (v,b)) s c (hnon g₀ hg₀)]
      exact hg₀.trans (monomial_degree (fun v b => g₀ (v,b)) s c)
    have hsub : (Finset.univ.filter Bad)⊆Finset.univ.filter (fun g : (V×Bool) → Fin q =>
        ∀ i∈rows s, g i=g₀ i) := by
      intro g hg
      have hb := (Finset.mem_filter.mp hg).2
      have hp := (nonzero_requirements (fun v b => g (v,b)) s c (hnon g hb)).1
      have hp₀ := (nonzero_requirements (fun v b => g₀ (v,b)) s c (hnon g₀ hg₀)).1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro i hi
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hi
      exact (hp y hy).symm.trans (hp₀ y hy)
    have hcount := ProofComplexity.FinitePinningCount.probability_bound (rows s) g₀ d hrows
      (by simpa using (show 1≤q by omega) : 1≤Fintype.card (Fin q))
    have hcard : ((Finset.univ.filter Bad).card : ℝ) ≤
        ((Finset.univ.filter (fun g : (V×Bool) → Fin q => ∀ i∈rows s, g i=g₀ i)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hh := hcard.trans hcount
    simpa only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Nat.mul_comm] using hh
  · have he : (Finset.univ.filter Bad)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hg
      exact hsome ⟨g,(Finset.mem_filter.mp hg).2⟩
    change ((Finset.univ.filter Bad).card : ℝ)≤_
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end AC02Frege.Supplement.SelectorMonomials
end

section
-- Inlined Solutions.SelectorMultiplicationRelation

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorMultiplicationRelation

open MvPolynomial AC02Frege.BooleanAlgebra SelectorRestrictionBasics

lemma product_relation {V : Type} [Fintype V] {q : ℕ} (A : V → Bool → Fin q)
    (p v : MvPolynomial (V×Bool×Fin q) (ZMod 2)) :
    ML (restrictPoly A (p*v)+restrictPoly A p*restrictPoly A (p*v))=0 := by
  apply multilinear_ext (ml_multilinear _) (by simpa using ml_multilinear (0 : MvPolynomial V (ZMod 2)))
  intro z
  rw [eval_ml,map_add,map_mul,map_zero]
  have he : eval z (restrictPoly A (p*v))=eval z (restrictPoly A p)*eval z (restrictPoly A v) := by
    have hh := congrArg (eval z) (restrict_mul A p v)
    simpa only [eval_ml,map_mul] using hh
  rw [he]
  rcases SelectorMonomials.zero_or_one (eval z (restrictPoly A p)) with ha | ha <;>
    simp [ha,CharTwo.add_self_eq_zero]

theorem complement_relation {V : Type} [Fintype V] {q : ℕ} (A : V → Bool → Fin q)
    (p v : MvPolynomial (V×Bool×Fin q) (ZMod 2)) :
    ML ((1+restrictPoly A (1+(1+p)*v))+
      (1+restrictPoly A p)*(1+restrictPoly A (1+(1+p)*v)))=0 := by
  have hh := product_relation A (1+p) v
  simpa only [restrict_add,restrict_one,CharTwo.add_cancel_left] using hh

end AC02Frege.Supplement.SelectorMultiplicationRelation
end

section
-- Inlined Solutions.SelectorInferenceRepair

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorInferenceRepair

open MvPolynomial LiftSAParity SelectorRestrictionBasics

lemma append_derived {V : Type} [DecidableEq V] (F : CNF V) (D : ℕ)
    (π : List (RLine V)) (hπ : ResDerivation.Valid F D π) (L : RLine V) (k : ℕ)
    (hL : ResDerivation.Derives F D L k) :
    ∃ ρ : List (RLine V), ResDerivation.Valid F D ρ ∧ π.IsPrefix ρ ∧ L∈ρ ∧ ρ.length≤π.length+k := by
  obtain ⟨σ,hσ,hmem,hlen⟩ := hL
  exact ⟨π++σ,ResDerivation.valid_append F D hπ hσ,⟨σ,rfl⟩,
    List.mem_append_right π hmem,by simpa only [List.length_append] using Nat.add_le_add_left hlen π.length⟩

lemma append_inference {V : Type} [DecidableEq V] (F : CNF V) (D : ℕ)
    (π : List (RLine V)) (hπ : ResDerivation.Valid F D π) (L : RLine V)
    (hL : ∀ p∈L, p.totalDegree≤D) (hinf : ResInfers F (fun M => M∈π) L) :
    ∃ ρ : List (RLine V), ResDerivation.Valid F D ρ ∧ π.IsPrefix ρ ∧ L∈ρ ∧ ρ.length≤π.length+1 := by
  exact ⟨π++[L],ResDerivation.valid_snoc F D hπ L hL hinf,⟨[L],rfl⟩,by simp,by simp⟩

lemma small_to_bound {V : Type} [Fintype V] [DecidableEq V] (F : CNF V) (d k : ℕ)
    (π : List (RLine V)) (L : RLine V) (hk : k≤(Fintype.card V)^(8*d)+2)
    (h : ∃ ρ : List (RLine V), ResDerivation.Valid F (2*d) ρ ∧ π.IsPrefix ρ ∧ L∈ρ ∧
      ρ.length≤π.length+k) :
    ∃ ρ : List (RLine V), ResDerivation.Valid F (2*d) ρ ∧ π.IsPrefix ρ ∧ L∈ρ ∧
      ρ.length≤π.length+(Fintype.card V)^(8*d)+2 := by
  obtain ⟨ρ,hρ,hpre,hL,hlen⟩ := h
  exact ⟨ρ,hρ,hpre,hL,by omega⟩

theorem inference {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (A : V → Bool → Fin q) (F : CNF V) (d : ℕ) (hn : 2≤Fintype.card V) (hd : 2≤d)
    (π : List (RLine V)) (hπ : ResDerivation.Valid F (2*d) π)
    (E : RLine (V×Bool×Fin q) → Prop)
    (hE : ∀ L, E L → restrictLine A L∈π)
    (hdegE : ∀ L, E L → ∀ p∈L, (restrictPoly A p).totalDegree<d)
    (L : RLine (V×Bool×Fin q)) (hL : ∀ p∈L, (restrictPoly A p).totalDegree<d)
    (hinf : ResInfers (selSubst F q) E L) :
    ∃ ρ : List (RLine V), ResDerivation.Valid F (2*d) ρ ∧ π.IsPrefix ρ ∧
      restrictLine A L∈ρ ∧ ρ.length≤π.length+(Fintype.card V)^(8*d)+2 := by
  have hLd : ∀ p∈restrictLine A L, p.totalDegree≤2*d := by
    intro p hp
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
    have hh := hL u hu
    omega
  cases hinf with
  | axOne =>
    apply small_to_bound F d 1 π _ (by omega)
    apply append_derived F (2*d) π hπ _ 1
    simpa [restrictLine] using ResDerivation.one F (2*d)
  | axBool x =>
    apply small_to_bound F d 2 π _ (by omega)
    apply append_derived F (2*d) π hπ _ 2
    apply SelectorInputLines.initial_derivation F (2*d) (by omega) _ hLd
    rcases SelectorInputLines.default_origin A x with hone | hbool
    · exact Or.inr (Or.inl hone)
    · exact Or.inr (Or.inr ⟨x.1,hbool⟩)
  | input J hJ =>
    exact small_to_bound F d 2 π _ (by omega) (append_derived F (2*d) π hπ _ 2
      (SelectorInputLines.restricted_input_derivation A F (2*d) (by omega) J hJ hLd))
  | weaken L L₀ hprev hsub =>
    apply small_to_bound F d 1 π _ (by omega)
    apply append_inference F (2*d) π hπ _ hLd
    exact ResInfers.weaken _ _ (hE L₀ hprev) (Finset.image_subset_image hsub)
  | del B hprev =>
    apply small_to_bound F d 1 π _ (by omega)
    apply append_inference F (2*d) π hπ _ hLd
    have hp := hE (insert 0 L) hprev
    simp only [restrictLine,Finset.image_insert,restrict_zero] at hp
    exact ResInfers.del _ hp
  | lin B C u v hprev hprev' =>
    apply small_to_bound F d 1 π _ (by omega)
    apply append_inference F (2*d) π hπ _ hLd
    have hp := hE (insert u B) hprev
    have hq := hE (insert v C) hprev'
    simp only [restrictLine,Finset.image_insert] at hp hq
    have hi := ResInfers.lin (Γ := F) (E := fun M => M∈π)
      (restrictLine A B) (restrictLine A C) (restrictPoly A u) (restrictPoly A v) hp hq
    simpa only [restrictLine,Finset.image_insert,Finset.image_union,restrict_add,restrict_one] using hi
  | mul B u v hprev =>
    let a := 1+restrictPoly A u
    let b := 1+restrictPoly A (1+(1+u)*v)
    have hu := hdegE (insert u B) hprev u (Finset.mem_insert_self _ _)
    have hw := hL (1+(1+u)*v) (Finset.mem_insert_self _ _)
    have ha : a.totalDegree<d := lt_of_le_of_lt (totalDegree_add _ _) (max_lt (by simp; omega) hu)
    have hb : b.totalDegree<d := lt_of_le_of_lt (totalDegree_add _ _) (max_lt (by simp; omega) hw)
    have hB : ∀ p∈restrictLine A B, p.totalDegree≤2*d := by
      intro p hp
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
      have hh := hdegE (insert u B) hprev z (Finset.mem_insert_of_mem hz)
      omega
    have hp := hE (insert u B) hprev
    have hp' : insert (1+a) (restrictLine A B)∈π := by
      simpa only [restrictLine,Finset.image_insert,a,CharTwo.add_cancel_left] using hp
    obtain ⟨ρ,hρ,hpre,hmem,hlen⟩ := ResDerivation.repair F d hn hd a b ha hb
      (SelectorMultiplicationRelation.complement_relation A u v) (restrictLine A B) hB π hπ hp'
    refine ⟨ρ,hρ,hpre,?_,hlen⟩
    simpa only [restrictLine,Finset.image_insert,b,CharTwo.add_cancel_left] using hmem

end AC02Frege.Supplement.SelectorInferenceRepair
end

section
-- Inlined Solutions.ResDistinctLineCount

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.ResDistinctLineCount

open MvPolynomial

noncomputable def cost {V : Type} (L : RLine V) : ℕ := ∑ p∈L, p.support.card

lemma zero_cost {V : Type} (L : RLine V) (h : cost L=0) : L=∅ ∨ L={0} := by
  classical
  have hsub : L⊆{0} := by
    intro p hp
    have hc : p.support.card≤cost L := Finset.single_le_sum
      (f := fun p : MvPolynomial V (ZMod 2) => p.support.card) (fun _ _ => Nat.zero_le _) hp
    have hpz : p=0 := MvPolynomial.support_eq_empty.mp (Finset.card_eq_zero.mp (by omega))
    simpa using hpz
  by_cases hz : (0 : MvPolynomial V (ZMod 2))∈L
  · exact Or.inr (Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hz))
  · apply Or.inl
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have he : p=0 := Finset.mem_singleton.mp (hsub hp)
    exact hz (he ▸ hp)

lemma sum_toFinset_le {I : Type} [DecidableEq I] (xs : List I) (f : I → ℕ) :
    xs.toFinset.sum f≤(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.toFinset_cons,List.map_cons,List.sum_cons]
    by_cases hi : i∈xs.toFinset
    · rw [Finset.insert_eq_of_mem hi]
      exact ih.trans (by omega)
    · rw [Finset.sum_insert hi]
      exact Nat.add_le_add_left ih (f i)

theorem distinct_le {V : Type} [DecidableEq V] (π : List (RLine V)) : π.toFinset.card≤totalSize π+2 := by
  classical
  let Z := π.toFinset.filter (fun L => cost L=0)
  have hZ : Z⊆({∅,{0}} : Finset (RLine V)) := by
    intro L hL
    rcases zero_cost L (Finset.mem_filter.mp hL).2 with rfl | rfl <;> simp
  have hZc : Z.card≤2 := (Finset.card_le_card hZ).trans (by simp)
  have hpos : (π.toFinset.filter (fun L => ¬cost L=0)).card≤π.toFinset.sum cost := by
    calc
      _ = ∑ L∈π.toFinset.filter (fun L => ¬cost L=0), 1 := by simp
      _ ≤ ∑ L∈π.toFinset.filter (fun L => ¬cost L=0), cost L :=
        Finset.sum_le_sum (fun L hL => Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hL).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
  have hc := Finset.card_filter_add_card_filter_not (s := π.toFinset) (p := fun L : RLine V => cost L=0)
  have hs := sum_toFinset_le π cost
  have ht : (π.map cost).sum≤totalSize π := Nat.le_max_right _ _
  change (π.toFinset.filter (fun L => cost L=0)).card≤2 at hZc
  omega

end AC02Frege.Supplement.ResDistinctLineCount
end

section
-- Inlined Solutions.SelectorCompletion

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorCompletion

open LiftSAParity

theorem valid_completion {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (A : V → Bool → Fin q) (F : CNF V) (d : ℕ) (hn : 2≤Fintype.card V) (hd : 2≤d)
    (π : List (RLine (V×Bool×Fin q)))
    (hinf : ∀ k (hk : k<π.length), ResInfers (selSubst F q)
      (fun L => ∃ j<k, π[j]?=some L) π[k])
    (hdeg : ∀ L∈π, ∀ p∈L, (restrictPoly A p).totalDegree<d) :
    ∃ ρ : List (RLine V), ResDerivation.Valid F (2*d) ρ ∧
      (∀ L∈π, restrictLine A L∈ρ) ∧
      ρ.length≤((Fintype.card V)^(8*d)+2)*π.toFinset.card := by
  induction π using List.reverseRecOn with
  | nil => exact ⟨[],⟨by simp,by simp⟩,by simp,by simp⟩
  | append_singleton π L ih =>
    have hi : ∀ k (hk : k<π.length), ResInfers (selSubst F q)
        (fun M => ∃ j<k, π[j]?=some M) π[k] := by
      intro k hk
      have hh := hinf k (by simp; omega)
      rw [List.getElem_append_left hk] at hh
      apply ResDerivation.inference_mono _ _ hh
      rintro M ⟨j,hjk,hj⟩
      exact ⟨j,hjk,by rwa [List.getElem?_append_left (by omega)] at hj⟩
    have hdπ : ∀ M∈π, ∀ p∈M, (restrictPoly A p).totalDegree<d := by
      intro M hM
      exact hdeg M (List.mem_append_left [L] hM)
    obtain ⟨ρ,hρ,hmem,hlen⟩ := ih hi hdπ
    by_cases hL : L∈π
    · refine ⟨ρ,hρ,?_,?_⟩
      · intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · exact hmem M hM
        · exact (List.mem_singleton.mp hM) ▸ hmem L hL
      · simpa only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
          Finset.insert_empty,Finset.union_singleton,Finset.insert_eq_of_mem (List.mem_toFinset.mpr hL)] using hlen
    · have hlast := hinf π.length (by simp)
      have he : (π++[L])[π.length]=L := by
        simpa using (List.getElem_append_right' (l₂ := [L]) (i := 0) π (by simp)).symm
      rw [he] at hlast
      have hprev (M : RLine (V×Bool×Fin q))
          (hM : ∃ j<π.length, (π++[L])[j]?=some M) : M∈π := by
        obtain ⟨j,hj,hval⟩ := hM
        rw [List.getElem?_append_left hj] at hval
        exact List.mem_of_getElem? hval
      obtain ⟨σ,hσ,hpre,hnew,hslen⟩ := SelectorInferenceRepair.inference A F d hn hd ρ hρ
        (fun M => ∃ j<π.length, (π++[L])[j]?=some M)
        (fun M hM => hmem M (hprev M hM)) (fun M hM => hdπ M (hprev M hM))
        L (hdeg L (by simp)) hlast
      refine ⟨σ,hσ,?_,?_⟩
      · intro M hM
        rcases List.mem_append.mp hM with hM | hM
        · exact hpre.subset (hmem M hM)
        · exact (List.mem_singleton.mp hM) ▸ hnew
      · have hc : (π++[L]).toFinset.card=π.toFinset.card+1 := by
          simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
            Finset.insert_empty,Finset.union_singleton]
          exact Finset.card_insert_of_notMem (by simpa only [List.mem_toFinset] using hL)
        rw [hc,mul_add,mul_one]
        omega

end AC02Frege.Supplement.SelectorCompletion
end

section
-- Inlined Solutions.SelectorCompletionSize

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorCompletion

open LiftSAParity

lemma size_budget (n d T : ℕ) (hn : 2≤n) (hd : 2≤d) (hT : 1≤T) :
    (n^(8*d)+2)*(T+2)+1≤T*n^(32*d) := by
  have hN : 1≤n^(8*d) := Nat.one_le_pow _ _ (by omega)
  have h16 : 16≤n^(24*d) := by
    have hbase : 16≤n^4 := Nat.pow_le_pow_left hn 4
    exact hbase.trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    _ ≤ 10*T*n^(8*d) := by nlinarith
    _ ≤ n^(24*d)*T*n^(8*d) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega : 10≤n^(24*d)))
    _ = _ := by rw [show 32*d=24*d+8*d by omega,pow_add]; ring

theorem refutation {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (A : V → Bool → Fin q) (F : CNF V) (d : ℕ) (hn : 2≤Fintype.card V) (hd : 2≤d)
    (π : List (RLine (V×Bool×Fin q))) (hπ : IsResRefutation ⊤ (selSubst F q) π)
    (hdeg : ∀ L∈π, ∀ p∈L, (restrictPoly A p).totalDegree<d) :
    ∃ ρ : List (RLine V), IsResRefutation ((2*d : ℕ) : ℕ∞) F ρ ∧
      (∀ L∈π, restrictLine A L∈ρ) ∧ ρ.length≤totalSize π*(Fintype.card V)^(32*d) := by
  obtain ⟨ρ,hρ,hmem,hlen⟩ := valid_completion A F d hn hd π hπ.2.1 hdeg
  have he : (∅ : RLine V)∈ρ := by
    have hh := hmem ∅ (List.mem_of_getLast? hπ.2.2)
    simpa [restrictLine] using hh
  have hv := ResDerivation.valid_snoc F (2*d) hρ ∅ (by simp)
    (ResInfers.weaken ∅ ∅ he (by rfl))
  refine ⟨ρ++[∅],⟨?_,hv.2,by simp⟩,?_,?_⟩
  · intro L hL p hp
    exact_mod_cast hv.1 L hL p hp
  · intro L hL
    exact List.mem_append_left [∅] (hmem L hL)
  · have hc := ResDistinctLineCount.distinct_le π
    have hlen' := hlen.trans (Nat.mul_le_mul_left ((Fintype.card V)^(8*d)+2) hc)
    simp only [List.length_append,List.length_singleton]
    exact (Nat.add_le_add_right hlen' 1).trans
      (size_budget (Fintype.card V) d (totalSize π) hn hd (Nat.le_max_left _ _))

end AC02Frege.Supplement.SelectorCompletion
end

section
-- Inlined Solutions.SelectorPolynomialTail

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorPolynomialTail

open MvPolynomial SelectorRestrictionBasics SelectorMonomials

theorem polynomial_tail {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (hq : 2≤q)
    (p : MvPolynomial (V×Bool×Fin q) (ZMod 2)) (d : ℕ) (hd : 1≤d) :
    (((Finset.univ : Finset ((V×Bool) → Fin q)).filter (fun g =>
      d≤(restrictPoly (fun v b => g (v,b)) p).totalDegree)).card : ℝ) ≤
      (p.support.card : ℝ)*((q : ℝ)^(2*Fintype.card V)/(q : ℝ)^d) := by
  let bad := fun s : (V×Bool×Fin q) →₀ ℕ => (Finset.univ : Finset ((V×Bool) → Fin q)).filter
    (fun g => d≤(restrictPoly (fun v b => g (v,b)) (monomial s (coeff s p))).totalDegree)
  have hsub : ((Finset.univ : Finset ((V×Bool) → Fin q)).filter (fun g =>
      d≤(restrictPoly (fun v b => g (v,b)) p).totalDegree)) ⊆ p.support.biUnion bad := by
    intro g hg
    have hdeg := (Finset.mem_filter.mp hg).2
    by_cases he : ∃ s∈p.support, d≤(restrictPoly (fun v b => g (v,b)) (monomial s (coeff s p))).totalDegree
    · obtain ⟨s,hs,hbad⟩ := he
      exact Finset.mem_biUnion.mpr ⟨s,hs,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad⟩⟩
    · have hall (s) (hs : s∈p.support) :
          (restrictPoly (fun v b => g (v,b)) (monomial s (coeff s p))).totalDegree≤d-1 := by
        have hn : ¬ d≤(restrictPoly (fun v b => g (v,b)) (monomial s (coeff s p))).totalDegree :=
          fun hh => he ⟨s,hs,hh⟩
        omega
      have heq : restrictPoly (fun v b => g (v,b)) p =
          ∑ s∈p.support, restrictPoly (fun v b => g (v,b)) (monomial s (coeff s p)) := by
        conv_lhs => rw [p.as_sum]
        simp only [restrictPoly,map_sum]
      have hpd : (restrictPoly (fun v b => g (v,b)) p).totalDegree≤d-1 := by
        rw [heq]
        exact totalDegree_finsetSum_le hall
      omega
  have hcard : (((Finset.univ : Finset ((V×Bool) → Fin q)).filter (fun g =>
      d≤(restrictPoly (fun v b => g (v,b)) p).totalDegree)).card : ℝ) ≤
      ((∑ s∈p.support, (bad s).card : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  apply hcard.trans
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _s∈p.support, (q : ℝ)^(2*Fintype.card V)/(q : ℝ)^d :=
      Finset.sum_le_sum (fun s hs => monomial_tail hq s (coeff s p) d hd)
    _ = _ := by simp

end AC02Frege.Supplement.SelectorPolynomialTail
end

section
-- Inlined Solutions.SelectorProofTail

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorProofTail

open MvPolynomial SelectorPolynomialTail

noncomputable def badPoly {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (d : ℕ)
    (p : MvPolynomial (V×Bool×Fin q) (ZMod 2)) : Finset ((V×Bool) → Fin q) :=
  Finset.univ.filter (fun g => d≤(restrictPoly (fun v b => g (v,b)) p).totalDegree)

noncomputable def badLine {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (d : ℕ)
    (L : RLine (V×Bool×Fin q)) : Finset ((V×Bool) → Fin q) := L.biUnion (badPoly d)

noncomputable def badProof {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (d : ℕ)
    (π : List (RLine (V×Bool×Fin q))) : Finset ((V×Bool) → Fin q) :=
  π.foldr (fun L S => badLine d L∪S) ∅

lemma mem_badProof {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (d : ℕ)
    (π : List (RLine (V×Bool×Fin q))) (g : (V×Bool) → Fin q) :
    g∈badProof d π ↔ ∃ L∈π, ∃ p∈L, d≤(restrictPoly (fun v b => g (v,b)) p).totalDegree := by
  induction π with
  | nil => simp [badProof]
  | cons L π ih =>
    simp only [badProof,List.foldr_cons,Finset.mem_union,badLine,Finset.mem_biUnion,
      badPoly,Finset.mem_filter,Finset.mem_univ,true_and]
    simp only [badProof,badLine] at ih
    rw [ih]
    simp only [List.mem_cons,exists_eq_or_imp,or_assoc]

theorem bad_card {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (hq : 2≤q)
    (π : List (RLine (V×Bool×Fin q))) (d : ℕ) (hd : 1≤d) :
    ((badProof d π).card : ℝ) ≤ (totalSize π : ℝ)*
      ((q : ℝ)^(2*Fintype.card V)/(q : ℝ)^d) := by
  let E := (q : ℝ)^(2*Fintype.card V)/(q : ℝ)^d
  have hline (L : RLine (V×Bool×Fin q)) : ((badLine d L).card : ℝ)≤
      ((∑ p∈L, p.support.card : ℕ) : ℝ)*E := by
    have hcard : ((badLine d L).card : ℝ)≤((∑ p∈L, (badPoly d p).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le (s := L) (t := badPoly d)
    apply hcard.trans
    rw [Nat.cast_sum,Nat.cast_sum,Finset.sum_mul]
    exact Finset.sum_le_sum (fun p hp => polynomial_tail hq p d hd)
  have hsum : ((badProof d π).card : ℝ)≤
      (((π.map (fun L => ∑ p∈L, p.support.card)).sum : ℕ) : ℝ)*E := by
    induction π with
    | nil => simp [badProof]
    | cons L π ih =>
      have hu : ((badLine d L∪badProof d π).card : ℝ)≤
          ((badLine d L).card : ℝ)+((badProof d π).card : ℝ) := by
        exact_mod_cast Finset.card_union_le (badLine d L) (badProof d π)
      have hh := add_le_add (hline L) ih
      simpa only [badProof,List.foldr_cons,List.map_cons,List.sum_cons,Nat.cast_add,add_mul] using hu.trans hh
  have he : (0 : ℝ)≤E := by dsimp [E]; positivity
  exact hsum.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast (Nat.le_max_right 1 _)) he)

theorem good_card_uncurried {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (hq : 2≤q)
    (π : List (RLine (V×Bool×Fin q))) (d : ℕ) (hd : 1≤d) :
    (1-(totalSize π : ℝ)/(q : ℝ)^d)*(q : ℝ)^(2*Fintype.card V) ≤
      (((Finset.univ : Finset ((V×Bool) → Fin q)).filter (fun g =>
        ∀ L∈π, ∀ p∈L, (restrictPoly (fun v b => g (v,b)) p).totalDegree<d)).card : ℝ) := by
  let Good := fun g : (V×Bool) → Fin q => ∀ L∈π, ∀ p∈L,
    (restrictPoly (fun v b => g (v,b)) p).totalDegree<d
  have hbad : badProof d π=Finset.univ.filter (fun g => ¬ Good g) := by
    ext g
    simp only [mem_badProof,Finset.mem_filter,Finset.mem_univ,true_and,Good,
      not_forall,_root_.not_imp,Nat.not_lt]
    constructor
    · rintro ⟨L,hL,p,hp,hdeg⟩
      exact ⟨L,hL,p,hp,hdeg⟩
    · rintro ⟨L,hL,p,hp,hdeg⟩
      exact ⟨L,hL,p,hp,hdeg⟩
  have hcard : (Finset.univ.filter Good).card+(badProof d π).card=q^(2*Fintype.card V) := by
    rw [hbad,Finset.card_filter_add_card_filter_not]
    simp [Fintype.card_fun,Fintype.card_prod,Nat.mul_comm]
  have hcR : (((Finset.univ.filter Good).card : ℕ) : ℝ)+((badProof d π).card : ℝ)=
      (q : ℝ)^(2*Fintype.card V) := by exact_mod_cast hcard
  have hb := bad_card hq π d hd
  change _≤((Finset.univ.filter Good).card : ℝ)
  have he : (1-(totalSize π : ℝ)/(q : ℝ)^d)*(q : ℝ)^(2*Fintype.card V) =
      (q : ℝ)^(2*Fintype.card V)-(totalSize π : ℝ)*((q : ℝ)^(2*Fintype.card V)/(q : ℝ)^d) := by ring
  rw [he]
  linarith

def curryEquiv (V : Type) (q : ℕ) : ((V×Bool) → Fin q) ≃ (V → Bool → Fin q) where
  toFun g v b := g (v,b)
  invFun A y := A y.1 y.2
  left_inv g := by funext y; cases y; rfl
  right_inv A := rfl

theorem good_card {V : Type} [Fintype V] [DecidableEq V] {q : ℕ} (hq : 2≤q)
    (π : List (RLine (V×Bool×Fin q))) (d : ℕ) (hd : 1≤d) :
    (1-(totalSize π : ℝ)/(q : ℝ)^d)*(q : ℝ)^(2*Fintype.card V) ≤
      (((Finset.univ : Finset (V → Bool → Fin q)).filter (fun A =>
        ∀ L∈π, ∀ p∈L, (restrictPoly A p).totalDegree<d)).card : ℝ) := by
  let P := fun g : (V×Bool) → Fin q => ∀ L∈π, ∀ p∈L,
    (restrictPoly (fun v b => g (v,b)) p).totalDegree<d
  let Q := fun A : V → Bool → Fin q => ∀ L∈π, ∀ p∈L, (restrictPoly A p).totalDegree<d
  have hcompat (g) : P g ↔ Q (curryEquiv V q g) := Iff.rfl
  have hcard : (Finset.univ.filter P).card=(Finset.univ.filter Q).card := by
    have h := Fintype.card_congr ((curryEquiv V q).subtypeEquiv hcompat)
    simpa only [Fintype.card_subtype] using h
  change _≤((Finset.univ.filter Q).card : ℝ)
  rw [← hcard]
  exact good_card_uncurried hq π d hd

end AC02Frege.Supplement.SelectorProofTail
end

section
-- Inlined Solutions.SelectorTransfer

set_option maxHeartbeats 2000000

namespace AC02Frege.Supplement.SelectorTransfer

open LiftSAParity Classical

theorem real_completion {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (A : V → Bool → Fin q) (F : CNF V) (d : ℕ) (hn : 2≤Fintype.card V) (hd : 2≤d)
    (π : List (RLine (V×Bool×Fin q))) (hπ : IsResRefutation ⊤ (selSubst F q) π)
    (hdeg : ∀ L∈π, ∀ p∈L, (restrictPoly A p).totalDegree<d) :
    ∃ ρ : List (RLine V), IsResRefutation ((2*d : ℕ) : ℕ∞) F ρ ∧
      (∀ L∈π, restrictLine A L∈ρ) ∧
      (ρ.length : ℝ)≤totalSize π*(Fintype.card V : ℝ)^((32 : ℝ)*d) := by
  obtain ⟨ρ,hρ,hmem,hlen⟩ := SelectorCompletion.refutation A F d hn hd π hπ hdeg
  refine ⟨ρ,hρ,hmem,?_⟩
  rw [show (32 : ℝ)*(d : ℝ)=((32*d : ℕ) : ℝ) by push_cast; rfl,Real.rpow_natCast]
  exact_mod_cast hlen

theorem transfer :
    ∃ C : ℝ, 0<C ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (F : CNF V) (d q : ℕ),
      2≤Fintype.card V → 2≤d → 2≤q →
      ∀ π : List (RLine (V×Bool×Fin q)), IsResRefutation ⊤ (selSubst F q) π →
        (1-(totalSize π : ℝ)/(q : ℝ)^d)*(q : ℝ)^(2*Fintype.card V)≤
          ((Finset.univ.filter (fun A : V → Bool → Fin q =>
            (∀ L∈π, ∀ p∈L, (restrictPoly A p).totalDegree<d) ∧
            ∃ ρ : List (RLine V), IsResRefutation ((2*d : ℕ) : ℕ∞) F ρ ∧
              (∀ L∈π, restrictLine A L∈ρ) ∧
              (ρ.length : ℝ)≤totalSize π*(Fintype.card V : ℝ)^(C*d))).card : ℝ) ∧
        ∀ L : ℕ, (∀ ρ : List (RLine V), IsResRefutation ((2*d : ℕ) : ℕ∞) F ρ → L≤ρ.length) →
          min ((q : ℝ)^d) ((L : ℝ)/(Fintype.card V : ℝ)^(C*d))≤totalSize π := by
  classical
  refine ⟨32,by norm_num,?_⟩
  intro V _ _ F d q hn hd hq π hπ
  have hcard := SelectorProofTail.good_card hq π d (by omega)
  constructor
  · apply hcard.trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro A hA
    have hg := (Finset.mem_filter.mp hA).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg,real_completion A F d hn hd π hπ hg⟩
  · intro L hL
    by_cases hT : (q : ℝ)^d≤totalSize π
    · exact (min_le_left _ _).trans hT
    · have hqpos : (0 : ℝ)<q := by exact_mod_cast (show 0<q by omega)
      have hpow : (0 : ℝ)<(q : ℝ)^d := pow_pos hqpos _
      have hfrac : (totalSize π : ℝ)/(q : ℝ)^d<1 := (div_lt_one hpow).mpr (lt_of_not_ge hT)
      have hpos : (0 : ℝ)<(1-(totalSize π : ℝ)/(q : ℝ)^d)*(q : ℝ)^(2*Fintype.card V) :=
        mul_pos (by linarith) (pow_pos hqpos _)
      have hcpos : 0<(Finset.univ.filter (fun A : V → Bool → Fin q =>
          ∀ M∈π, ∀ p∈M, (restrictPoly A p).totalDegree<d)).card := by
        exact_mod_cast hpos.trans_le hcard
      obtain ⟨A,hA⟩ := Finset.card_pos.mp hcpos
      obtain ⟨ρ,hρ,_,hlen⟩ := real_completion A F d hn hd π hπ (Finset.mem_filter.mp hA).2
      have hLr : (L : ℝ)≤ρ.length := by exact_mod_cast hL ρ hρ
      have hnpos : (0 : ℝ)<(Fintype.card V : ℝ) := by exact_mod_cast (show 0<Fintype.card V by omega)
      have hden : (0 : ℝ)<(Fintype.card V : ℝ)^((32 : ℝ)*d) := Real.rpow_pos_of_pos hnpos _
      exact (min_le_right _ _).trans ((div_le_iff₀ hden).mpr (hLr.trans hlen))

end AC02Frege.Supplement.SelectorTransfer
end

open AC02Frege AC02Frege.Supplement LiftSAParity Classical

theorem solution :
    ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (F' : CNF V) (d q : ℕ),
      2 ≤ Fintype.card V → 2 ≤ d → 2 ≤ q →
      ∀ π : List (RLine (V × Bool × Fin q)), IsResRefutation ⊤ (selSubst F' q) π →
        (1 - (totalSize π : ℝ) / (q : ℝ) ^ d) * (q : ℝ) ^ (2 * Fintype.card V) ≤
          ((Finset.univ.filter (fun A : V → Bool → Fin q =>
            (∀ L ∈ π, ∀ u ∈ L, (restrictPoly A u).totalDegree < d) ∧
            ∃ πr : List (RLine V), IsResRefutation ((2 * d : ℕ) : ℕ∞) F' πr ∧
              (∀ L ∈ π, restrictLine A L ∈ πr) ∧
              (πr.length : ℝ) ≤ totalSize π * (Fintype.card V : ℝ) ^ (C * d))).card : ℝ) ∧
        ∀ L : ℕ, (∀ πr : List (RLine V), IsResRefutation ((2 * d : ℕ) : ℕ∞) F' πr →
            L ≤ πr.length) →
          min ((q : ℝ) ^ d) ((L : ℝ) / (Fintype.card V : ℝ) ^ (C * d)) ≤ totalSize π  := by
  exact AC02Frege.Supplement.SelectorTransfer.transfer
