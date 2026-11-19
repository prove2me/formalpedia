-- Prove2me | solution 1 for APSCounting893.Main.epsilon_limit_set_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:34:01.474476+00:00
-- url     : https://prove2.me/submissions/c6256c7c-0dd7-421c-ab27-f9176f0ddd94

import Definitions.Def_APSCounting893_Main_Resultant
import Mathlib
import Theorems.Thm_APSCounting893_Main_normalized_resultant_foundation
import Theorems.Thm_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

noncomputable def nonnegativeHahnRing (K : Type) [Field K] : ValuationSubring (HahnSeries ℚ K) :=
  (AddValuation.toValuation (HahnSeries.addVal ℚ K)).valuationSubring

lemma hahn_coeff_zero_mul_nonnegative {K : Type} [Field K] (x y : HahnSeries ℚ K)
    (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hxo : 0 ≤ x.order := HahnSeries.zero_le_orderTop_iff.mp hx
  have hyo : 0 ≤ y.order := HahnSeries.zero_le_orderTop_iff.mp hy
  by_cases hxord : x.order = 0
  · by_cases hyord : y.order = 0
    · simpa only [HahnSeries.leadingCoeff_eq, hxord, hyord, add_zero] using HahnSeries.coeff_mul_order_add_order x y
    · have hpos : 0 < y.order := lt_of_le_of_ne hyo (Ne.symm hyord)
      rw [HahnSeries.coeff_eq_zero_of_lt_order hpos, mul_zero]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      rw [HahnSeries.order_mul hx0 hy0, hxord, zero_add]
      exact hpos
  · have hpos : 0 < x.order := lt_of_le_of_ne hxo (Ne.symm hxord)
    rw [HahnSeries.coeff_eq_zero_of_lt_order hpos, zero_mul]
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [HahnSeries.order_mul hx0 hy0]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_right hyo)

noncomputable def hahnResidueHom (K : Type) [Field K] : nonnegativeHahnRing K →+* K where
  toFun x := x.val.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := hahn_coeff_zero_mul_nonnegative x.val y.val x.property y.property

noncomputable def hahnConstantLift (K : Type) [Field K] : K →+* nonnegativeHahnRing K where
  toFun c := ⟨HahnSeries.C c, by
    change 0 ≤ (HahnSeries.C c : HahnSeries ℚ K).orderTop
    rw [HahnSeries.zero_le_orderTop_iff, HahnSeries.order_C]⟩
  map_zero' := Subtype.ext HahnSeries.C.map_zero
  map_one' := Subtype.ext HahnSeries.C.map_one
  map_add' a b := Subtype.ext (HahnSeries.C.map_add a b)
  map_mul' a b := Subtype.ext (HahnSeries.C.map_mul a b)

lemma hahnResidue_constant {K : Type} [Field K] (c : K) :
    hahnResidueHom K (hahnConstantLift K c) = c := by simp [hahnResidueHom, hahnConstantLift]

lemma hahnResidue_single_one {K : Type} [Field K] :
    ∃ x : nonnegativeHahnRing K, x.val = HahnSeries.single (1 : ℚ) (1 : K) ∧ hahnResidueHom K x = 0 := by
  refine ⟨⟨HahnSeries.single (1 : ℚ) (1 : K), ?_⟩, rfl, ?_⟩
  · change 0 ≤ (HahnSeries.single (1 : ℚ) (1 : K)).orderTop
    rw [HahnSeries.orderTop_single]
    · norm_num
    · exact one_ne_zero
  · simp [hahnResidueHom, HahnSeries.coeff_single_of_ne]

end APSCounting893.Main
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def tCoefficientHom : Polynomial ℂ →+* PuiseuxAmbient :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ))

noncomputable def tAuxHom : Aux →+* PuiseuxAmbient :=
  MvPolynomial.eval₂Hom HahnSeries.C
    (fun v : Fin 4 => if v = 2 then HahnSeries.single (1 : ℚ) (1 : ℂ) else 0)

lemma tCoefficient_C (c : ℂ) : tCoefficientHom (Polynomial.C c) = HahnSeries.C c := by
  simp [tCoefficientHom]

lemma tAux_polynomial_coefficients (p : Polynomial ℂ) :
    tAuxHom ((Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) p) =
      tCoefficientHom p := by
  have heq : tAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      tCoefficientHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [tAuxHom, tCoefficientHom]
    · simp [tAuxHom, tCoefficientHom]
  exact RingHom.congr_fun heq p

lemma equationWithAux_specializes (F : RawMap) (c alpha : Affine ℂ F.n)
    (i : Fin (F.n + (F.n + 1))) (x : Affine PuiseuxAmbient (F.n + (F.n + 1))) :
    MvPolynomial.eval₂ tAuxHom x (equationWithAux F c alpha i) =
      MvPolynomial.eval₂ tCoefficientHom x
        (affineLineEquations F c alpha (Fin.cast (Nat.add_comm _ _) i)) := by
  rw [equationWithAux, MvPolynomial.eval₂_map]
  have heq : tAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      tCoefficientHom := by
    exact RingHom.ext tAux_polynomial_coefficients
  rw [heq]

lemma affineLineEquations_iff (F : ReducedMap) (D : LineData F)
    (z : Affine PuiseuxAmbient (F.n + (F.n + 1))) :
    (∀ i, MvPolynomial.eval₂ tCoefficientHom z (affineLineEquations F D.c D.alpha i) = 0) ↔
      (∀ j : Fin (F.n + 1), z (j.natAdd F.n) =
        MvPolynomial.eval₂ HahnSeries.C (fun i => z (i.castAdd (F.n + 1))) (F.F j)) ∧
      (∀ j : Fin F.n, z (j.castSucc.natAdd F.n) - HahnSeries.C (D.c j) * z ((Fin.last F.n).natAdd F.n) =
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ)) := by
  have hcomp : tCoefficientHom.comp Polynomial.C = HahnSeries.C := by
    exact RingHom.ext tCoefficient_C
  have hout (j : Fin (F.n + 1)) :
      MvPolynomial.eval₂ tCoefficientHom z
        (affineLineEquations F D.c D.alpha (j.castAdd F.n)) =
      z (j.natAdd F.n) - MvPolynomial.eval₂ HahnSeries.C
        (fun i => z (i.castAdd (F.n + 1))) (F.F j) := by
    simp only [affineLineEquations, Fin.addCases_left, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_map, hcomp]
    rfl
  have hline (j : Fin F.n) :
      MvPolynomial.eval₂ tCoefficientHom z
        (affineLineEquations F D.c D.alpha (j.natAdd (F.n + 1))) =
      z (j.castSucc.natAdd F.n) - HahnSeries.C (D.c j) * z ((Fin.last F.n).natAdd F.n) -
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ) := by
    simp [affineLineEquations, tCoefficientHom]
  constructor
  · intro h
    exact ⟨fun j => sub_eq_zero.mp ((hout j).symm.trans (h _)),
      fun j => sub_eq_zero.mp ((hline j).symm.trans (h _))⟩
  · rintro ⟨ho, hl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [hout, ho, sub_self]
    · rw [hline, hl, sub_self]

end APSCounting893.Main
end Component_1

section Component_2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_homogenize_monomial {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (z : Fin (n + 1) → K) (e : Fin n →₀ ℕ) (c : R) (d : ℕ) :
    MvPolynomial.eval₂ f z (MvPolynomial.monomial
      (Finsupp.single 0 (d - e.sum (fun _ k => k)) + e.mapDomain Fin.succ) c) =
    f c * z 0 ^ (d - e.sum (fun _ k => k)) * e.prod (fun i k => z i.succ ^ k) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [Finsupp.prod_single_index (h := fun i k => z i ^ k) (pow_zero (z 0))]
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  ring

lemma finsupp_prod_scaled {K : Type} [Field K] {n : ℕ}
    (e : Fin n →₀ ℕ) (a : K) (x : Fin n → K) :
    e.prod (fun i k => (a * x i) ^ k) =
      a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k) := by
  classical
  rw [e.prod_fintype _ (fun _ => pow_zero _), e.prod_fintype _ (fun _ => pow_zero _),
    e.sum_fintype _ (fun _ => rfl)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma eval_homogenize_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (a : K) (x : Fin n → K) :
    MvPolynomial.eval₂ f (Fin.cases a (fun i => a * x i)) (homogenizeAll d p) =
      a ^ d * MvPolynomial.eval₂ f x p := by
  classical
  rw [homogenizeAll, MvPolynomial.eval₂_sum]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_homogenize_monomial]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [finsupp_prod_scaled]
  have hedeg : e.sum (fun _ k => k) ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  have hpow : a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k) = a ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hedeg]
  calc
    f (p.coeff e) * a ^ (d - e.sum (fun _ k => k)) *
        (a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k)) =
      (a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k)) *
        (f (p.coeff e) * e.prod (fun i k => x i ^ k)) := by ring
    _ = _ := by rw [hpow]; rfl

lemma eval_homogenize_dehomogenize {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (z : Fin (n + 1) → K) (hz : z 0 ≠ 0) :
    MvPolynomial.eval₂ f z (homogenizeAll d p) =
      z 0 ^ d * MvPolynomial.eval₂ f (fun i => z i.succ / z 0) p := by
  have heq : Fin.cases (z 0) (fun i => z 0 * (z i.succ / z 0)) = z := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [hz, mul_div_cancel₀, mul_comm]
  simpa only [heq] using eval_homogenize_scaled f p d hd (z 0) (fun i => z i.succ / z 0)

end APSCounting893.Main
end Component_2

section Component_3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma projectiveRepresentative_rescaling {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ projectiveRepresentative z = a • z := by
  classical
  have hS : (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).Nonempty := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let j := (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).min' hS
  have hj : z j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
  refine ⟨(z j)⁻¹, inv_ne_zero hj, ?_⟩
  rw [projectiveRepresentative, dif_pos hS]
  funext i
  simp only [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

lemma projectiveRepresentative_ne_zero {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) : projectiveRepresentative z ≠ 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  exact smul_ne_zero ha hz

lemma homogenizeAll_homogeneous {R : Type} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (homogenizeAll d p).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain, Finsupp.degree_eq_sum]
  have hsum : (∑ i : Fin n, e i) = e.sum (fun _ k => k) :=
    (e.sum_fintype (fun _ k => k) (fun _ => rfl)).symm
  rw [hsum]
  exact Nat.sub_add_cancel ((MvPolynomial.le_totalDegree he).trans hd)

lemma homogeneous_eval₂_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (a : K) (z : Fin n → K) :
    MvPolynomial.eval₂ f (fun i => a * z i) p = a ^ d * MvPolynomial.eval₂ f z p := by
  classical
  conv_lhs => rw [MvPolynomial.eval₂_eq]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  change f (p.coeff e) * e.prod (fun i k => (a * z i) ^ k) =
    a ^ d * (f (p.coeff e) * e.prod (fun i k => z i ^ k))
  rw [finsupp_prod_scaled]
  have hd := hp.degree_eq_sum_deg_support he
  change d = e.sum (fun _ k => k) at hd
  rw [← hd]
  ring

lemma homogeneous_root_projectiveRepresentative {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (z : Fin n → K) (hz : z ≠ 0) (hroot : MvPolynomial.eval₂ f z p = 0) :
    MvPolynomial.eval₂ f (projectiveRepresentative z) p = 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  change MvPolynomial.eval₂ f (fun i => a * z i) p = 0
  rw [homogeneous_eval₂_scaled p d hp f a z, hroot, mul_zero]

end APSCounting893.Main
end Component_3

section Component_4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def epsilonRegular : nonnegativeHahnRing PuiseuxAmbient :=
  Classical.choose (hahnResidue_single_one (K := PuiseuxAmbient))

lemma epsilonRegular_val : epsilonRegular.val = HahnSeries.single (1 : ℚ) (1 : PuiseuxAmbient) :=
  (Classical.choose_spec (hahnResidue_single_one (K := PuiseuxAmbient))).1

lemma epsilonRegular_residue : hahnResidueHom PuiseuxAmbient epsilonRegular = 0 :=
  (Classical.choose_spec (hahnResidue_single_one (K := PuiseuxAmbient))).2

noncomputable def epsilonAuxHom : Aux →+* EpsilonAmbient :=
  MvPolynomial.eval₂Hom (HahnSeries.C.comp HahnSeries.C)
    (fun v : Fin 4 => if v = 0 then HahnSeries.single (1 : ℚ) 1
      else if v = 2 then HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0)

noncomputable def epsilonAuxLift : Aux →+* nonnegativeHahnRing PuiseuxAmbient :=
  MvPolynomial.eval₂Hom ((hahnConstantLift PuiseuxAmbient).comp HahnSeries.C)
    (fun v : Fin 4 => if v = 0 then epsilonRegular
      else if v = 2 then hahnConstantLift PuiseuxAmbient (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0)

lemma epsilonAuxLift_underlying :
    (nonnegativeHahnRing PuiseuxAmbient).subtype.comp epsilonAuxLift = epsilonAuxHom := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp [epsilonAuxLift, epsilonAuxHom, hahnConstantLift]
  · intro v
    fin_cases v <;> simp [epsilonAuxLift, epsilonAuxHom, hahnConstantLift, epsilonRegular_val]

lemma epsilonAuxLift_residue :
    (hahnResidueHom PuiseuxAmbient).comp epsilonAuxLift = tAuxHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [epsilonAuxLift, tAuxHom, hahnResidue_constant]
  · intro v
    fin_cases v <;> simp [epsilonAuxLift, tAuxHom, hahnResidue_constant, epsilonRegular_residue]

lemma epsilon_specialization_homogeneous (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ)
    (q : Fin (F.n + (F.n + 1) + 1) → EpsilonAmbient)
    (hq : ∀ j, 0 ≤ (q j).orderTop)
    (hroot : ∀ i, MvPolynomial.eval₂ epsilonAuxHom q (perturbedEquation F c alpha degrees i) = 0) :
    ∀ i, MvPolynomial.eval₂ tAuxHom (fun j => (q j).coeff 0) (homogenizedEquation F c alpha degrees i) = 0 := by
  let qlift : Fin (F.n + (F.n + 1) + 1) → nonnegativeHahnRing PuiseuxAmbient := fun j => ⟨q j, hq j⟩
  intro i
  have hlift : MvPolynomial.eval₂ epsilonAuxLift qlift (perturbedEquation F c alpha degrees i) = 0 := by
    apply Subtype.val_injective
    change (nonnegativeHahnRing PuiseuxAmbient).subtype
      (MvPolynomial.eval₂ epsilonAuxLift qlift (perturbedEquation F c alpha degrees i)) = 0
    rw [MvPolynomial.hom_eval₂, epsilonAuxLift_underlying]
    exact hroot i
  have h := congrArg (hahnResidueHom PuiseuxAmbient) hlift
  rw [MvPolynomial.hom_eval₂, map_zero, epsilonAuxLift_residue] at h
  change MvPolynomial.eval₂ tAuxHom (fun j => (q j).coeff 0) (perturbedEquation F c alpha degrees i) = 0 at h
  simpa [perturbedEquation, tAuxHom] using h

lemma epsilon_limit_homogeneous (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (hdegrees : HomogenizingDegrees F c alpha degrees)
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient)
    (hz : z ∈ epsilonLimitSet F c alpha degrees) :
    z ≠ 0 ∧ ∀ i, MvPolynomial.eval₂ tAuxHom z (homogenizedEquation F c alpha degrees i) = 0 := by
  obtain ⟨q, hq, hmin, hroot, hz⟩ := hz
  have hq0 : (fun j => (q j).coeff 0) ≠ 0 := by
    obtain ⟨j, hj⟩ := hmin
    intro h
    have hh := congrFun h j
    exact HahnSeries.coeff_orderTop_ne hj hh
  have heq := epsilon_specialization_homogeneous F c alpha degrees q (fun j => (hq j).2) hroot
  rw [hz]
  refine ⟨projectiveRepresentative_ne_zero _ hq0, ?_⟩
  intro i
  apply homogeneous_root_projectiveRepresentative (homogenizedEquation F c alpha degrees i) (degrees i)
    (homogenizeAll_homogeneous _ _ (hdegrees i).2.2) tAuxHom _ hq0 (heq i)

end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial HahnSeries
open scoped LaurentSeries RatFunc
namespace APSCounting893.Main.GenericSeries

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]

def IsPuiseuxOver (s : HahnSeries ℚ K) : Prop :=
  ∃ (e : ℕ) (he : 0 < e), s ∈ HahnSeries.puiseuxRamSubfield K he

noncomputable def ramOneAlgHom : LaurentSeries K →ₐ[K] (HahnSeries ℚ K) where
  toRingHom := HahnSeries.puiseuxRamEmb (by decide : 0 < 1)
  commutes' c := by
    simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C]
    exact HahnSeries.embDomainRingHom_C (R := K)

noncomputable def rationalSeriesHom : RatFunc K →ₐ[K] (HahnSeries ℚ K) where
  toRingHom := ramOneAlgHom.toRingHom.comp (algebraMap (RatFunc K) (LaurentSeries K))
  commutes' c := by
    change ramOneAlgHom (algebraMap (RatFunc K) (LaurentSeries K) (algebraMap K (RatFunc K) c)) = _
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
      ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
    have hL : algebraMap (Polynomial K) (LaurentSeries K) (algebraMap K (Polynomial K) c) =
        algebraMap K (LaurentSeries K) c := by
      rw [HahnSeries.algebraMap_apply',
        ← IsScalarTower.algebraMap_apply K (Polynomial K) (PowerSeries K)]
      simp [HahnSeries.algebraMap_apply', HahnSeries.ofPowerSeries_C]
    rw [hL]
    exact ramOneAlgHom.commutes c

lemma rationalSeriesHom_X :
    rationalSeriesHom (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
      HahnSeries.single (1 : ℚ) (1 : K) := by
  change ramOneAlgHom (algebraMap (RatFunc K) (LaurentSeries K) RatFunc.X) = _
  rw [RatFunc.coe_X]
  change HahnSeries.embDomain _ (HahnSeries.single (1 : ℤ) (1 : K)) = _
  rw [HahnSeries.embDomain_single]
  simp [HahnSeries.ramScale]

lemma rationalSeriesHom_puiseux (r : RatFunc K) :
    HahnSeries.HasRamBound 1 (rationalSeriesHom r) := by
  apply (HahnSeries.mem_puiseuxRamSubfield_iff (by decide : 0 < 1)).mp
  exact ⟨algebraMap (RatFunc K) (LaurentSeries K) r, rfl⟩

lemma rationalSeriesHom_unique {M : Type} [Field M] [Algebra K M] [Algebra (RatFunc K) M]
    [IsScalarTower K (RatFunc K) M] (rho : M →ₐ[K] (HahnSeries ℚ K))
    (ht : rho (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : K)) :
    rho.toRingHom.comp (algebraMap (RatFunc K) M) = rationalSeriesHom.toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Polynomial K)
  have hpoly : (rho.toRingHom.comp (algebraMap (RatFunc K) M)).comp
        (algebraMap (Polynomial K) (RatFunc K)) =
      rationalSeriesHom.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      change rho (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K)
        (algebraMap K (Polynomial K) c))) =
        rationalSeriesHom (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) c))
      rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
        ← IsScalarTower.algebraMap_apply K (RatFunc K) M]
      exact (rho.commutes c).trans (rationalSeriesHom.commutes c).symm
    · change rho (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) X)) =
        rationalSeriesHom (algebraMap (Polynomial K) (RatFunc K) X)
      rw [rationalSeriesHom_X]
      exact ht
  exact fun p => RingHom.congr_fun hpoly p

lemma algebraic_image_puiseux {M : Type} [Field M] [Algebra K M] [Algebra (RatFunc K) M]
    [IsScalarTower K (RatFunc K) M] [Algebra.IsAlgebraic (RatFunc K) M]
    (rho : M →ₐ[K] (HahnSeries ℚ K))
    (ht : rho (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : K)) (z : M) : IsPuiseuxOver (rho z) := by
  classical
  have hz : IsIntegral (RatFunc K) z := (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  let q := (minpoly (RatFunc K) z).map rationalSeriesHom.toRingHom
  have hq : q ≠ 0 := (minpoly.monic hz).map rationalSeriesHom.toRingHom |>.ne_zero
  have hcoeff : ∀ i, HahnSeries.HasRamBound 1 (q.coeff i) := by
    intro i
    simpa [q] using rationalSeriesHom_puiseux ((minpoly (RatFunc K) z).coeff i)
  have hroot : q.IsRoot (rho z) := by
    have heq := rationalSeriesHom_unique rho ht
    change q.eval (rho z) = 0
    dsimp only [q]
    rw [Polynomial.eval_map]
    rw [← heq]
    rw [← Polynomial.eval₂_map]
    change Polynomial.eval₂ rho.toRingHom (rho.toRingHom z)
      ((minpoly (RatFunc K) z).map (algebraMap (RatFunc K) M)) = 0
    rw [Polynomial.eval₂_at_apply]
    simpa using congrArg rho (minpoly.aeval (RatFunc K) z)
  exact ⟨q.natDegree.factorial, Nat.factorial_pos _,
    (HahnSeries.mem_puiseuxRamSubfield_iff (Nat.factorial_pos _)).mpr
      (HahnSeries.hasRamBound_natDegree_factorial_of_isRoot hq hcoeff hroot)⟩


end APSCounting893.Main.GenericSeries
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main
lemma epsilonAux_polynomial_coefficients (p : Polynomial ℂ) :
    epsilonAuxHom ((Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) p) =
      HahnSeries.C (tCoefficientHom p) := by
  have hh : epsilonAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient).comp tCoefficientHom := by
    apply Polynomial.ringHom_ext (R := ℂ) (S := EpsilonAmbient)
    · intro c
      simp [epsilonAuxHom, tCoefficientHom]
    · simp [epsilonAuxHom, tCoefficientHom]
  exact RingHom.congr_fun hh p

lemma epsilon_equationWithAux_eval (F : RawMap) (c alpha : Affine ℂ F.n)
    (i : Fin (F.n + (F.n + 1))) (q : Fin (F.n + (F.n + 1)) → EpsilonAmbient) :
    MvPolynomial.eval₂ epsilonAuxHom q (equationWithAux F c alpha i) =
      MvPolynomial.eval₂ HahnSeries.C q (MvPolynomial.map tAuxHom (equationWithAux F c alpha i)) := by
  rw [MvPolynomial.eval₂_map, equationWithAux, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply]
  rw [epsilonAux_polynomial_coefficients, tAux_polynomial_coefficients]


end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
namespace APSCounting893.Main
lemma universalResultant_specification {n : ℕ} (d : Fin (n+1) → ℕ)
    (hd : ∀ i, 0 < d i) : ResultantVNP.IsMultivariateResultant d (universalResultant d) :=
  Classical.epsilon_spec (normalized_resultant_foundation d hd).1
end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
namespace APSCounting893.Main
lemma homogeneousResultant_zero_iff {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i)
    (G : Fin (n+1) → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i)) :
    homogeneousResultant d G = 0 ↔
      ∃ x : Fin (n+1) → K, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (G i) = 0 := by
  exact (normalized_resultant_foundation d hd).2 (universalResultant d)
    (universalResultant_specification d hd) K G hG
end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
namespace APSCounting893.Main
noncomputable def diagonalCoefficient {K : Type} [CommRing K] {n : ℕ}
    (d : Fin n → ℕ) (v : ResultantVNP.CoeffVar d) : K :=
  if v.2.1 = Finsupp.single v.1 (d v.1) then 1 else 0
end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma homogeneousResultant_pure_powers {K : Type} [CommRing K] {n : ℕ}
    (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i) :
    homogeneousResultant d (fun i => (MvPolynomial.X i : MvPolynomial (Fin (n+1)) K) ^ d i) = 1 := by
  classical
  have hcoeff (v : ResultantVNP.CoeffVar d) :
      MvPolynomial.coeff v.2.1 ((MvPolynomial.X v.1 : MvPolynomial (Fin (n+1)) K) ^ d v.1) =
        Int.castRingHom K (diagonalCoefficient (K := ℤ) d v) := by
    simp [MvPolynomial.coeff_X_pow,diagonalCoefficient,eq_comm]
  unfold homogeneousResultant
  simp_rw [hcoeff]
  have hh := MvPolynomial.eval₂_comp_left (Int.castRingHom K) (RingHom.id ℤ)
    (diagonalCoefficient (K := ℤ) d) (universalResultant d)
  simp only [RingHom.comp_id,MvPolynomial.eval₂_id] at hh
  have hh' : MvPolynomial.eval₂ (Int.castRingHom K)
      (fun v => Int.castRingHom K (diagonalCoefficient (K := ℤ) d v)) (universalResultant d) =
      Int.castRingHom K (MvPolynomial.eval (diagonalCoefficient (K := ℤ) d) (universalResultant d)) := by
    simpa only [Function.comp_def] using hh.symm
  rw [hh']
  have he := (universalResultant_specification d hd).2.1
  change MvPolynomial.eval (diagonalCoefficient (K := ℤ) d) (universalResultant d) = 1 at he
  rw [he,map_one]

lemma homogeneousResultant_map {K L : Type} [CommRing K] [CommRing L]
    (f : K →+* L) {n : ℕ} (d : Fin n → ℕ) (G : Fin n → MvPolynomial (Fin n) K) :
    f (homogeneousResultant d G) = homogeneousResultant d (fun i => MvPolynomial.map f (G i)) := by
  unfold homogeneousResultant
  rw [MvPolynomial.eval₂_comp_left]
  have hcast : f.comp (Int.castRingHom K) = Int.castRingHom L := by ext z; simp
  rw [hcast]
  apply MvPolynomial.eval₂Hom_congr rfl _ rfl
  funext v
  rw [MvPolynomial.coeff_map]
  rfl

end APSCounting893.Main
end Component_10

section Component_11

set_option autoImplicit false
namespace APSCounting893.Main

lemma polynomial_zero_of_eval_zero_off_zero {K : Type*} [Field K] [Infinite K]
    (p : Polynomial K) (hp : ∀ s : K, s ≠ 0 → p.eval s = 0) : p = 0 := by
  have hh : Polynomial.X * p = 0 := Polynomial.zero_of_eval_zero _ (by
    intro s
    by_cases hs : s = 0
    · simp [hs]
    · simp [hp s hs])
  exact (mul_eq_zero.mp hh).resolve_left Polynomial.X_ne_zero

end APSCounting893.Main
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma map_polynomial_constant_specialization {K : Type} [CommRing K] {σ : Type}
    (s : K) (p : MvPolynomial σ K) :
    MvPolynomial.map (Polynomial.evalRingHom s) (MvPolynomial.map Polynomial.C p) = p := by
  apply MvPolynomial.ext
  intro e
  rw [MvPolynomial.coeff_map,MvPolynomial.coeff_map]
  exact Polynomial.eval_C

lemma resultant_monomial_perturbation_ne_zero {K : Type} [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i)
    (G : Fin (n+1) → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i)) :
    homogeneousResultant d (fun i => MvPolynomial.map Polynomial.C (G i) +
      MvPolynomial.C Polynomial.X * MvPolynomial.X i ^ d i) ≠ (0 : Polynomial K) := by
  classical
  let A : Fin (n+1) → MvPolynomial (Fin (n+1)) (Polynomial K) := fun i =>
    MvPolynomial.C Polynomial.X * MvPolynomial.map Polynomial.C (G i) + MvPolynomial.X i ^ d i
  let P : Polynomial K := homogeneousResultant d A
  have hP0 : P.eval 0 = 1 := by
    change (Polynomial.evalRingHom 0) (homogeneousResultant d A) = 1
    rw [homogeneousResultant_map]
    have hA : (fun i => MvPolynomial.map (Polynomial.evalRingHom (0 : K)) (A i)) =
        (fun i => MvPolynomial.X i ^ d i) := by
      funext i
      simp [A,map_polynomial_constant_specialization]
    rw [hA,homogeneousResultant_pure_powers d hd]
  obtain ⟨s,hs,hPs⟩ : ∃ s : K, s ≠ 0 ∧ P.eval s ≠ 0 := by
    by_contra h
    push Not at h
    have hz := polynomial_zero_of_eval_zero_off_zero P h
    rw [hz,Polynomial.eval_zero] at hP0
    exact zero_ne_one hP0
  have hPspec : P.eval s = homogeneousResultant d (fun i => MvPolynomial.C s * G i + MvPolynomial.X i ^ d i) := by
    change (Polynomial.evalRingHom s) (homogeneousResultant d A) = _
    rw [homogeneousResultant_map]
    apply congrArg (homogeneousResultant d)
    funext i
    simp [A,map_polynomial_constant_specialization]
  intro hzero
  have hres : homogeneousResultant d (fun i => G i + MvPolynomial.C s⁻¹ * MvPolynomial.X i ^ d i) = 0 := by
    have he := congrArg (Polynomial.evalRingHom s⁻¹) hzero
    rw [map_zero,homogeneousResultant_map] at he
    have hB : (fun i : Fin (n+1) => MvPolynomial.map (Polynomial.evalRingHom s⁻¹)
        (MvPolynomial.map Polynomial.C (G i) +
          MvPolynomial.C Polynomial.X * MvPolynomial.X i ^ d i)) =
        (fun i => G i + MvPolynomial.C s⁻¹ * MvPolynomial.X i ^ d i) := by
      funext i
      simp [map_polynomial_constant_specialization]
    rw [hB] at he
    exact he
  have hhom (i : Fin (n+1)) : (G i + MvPolynomial.C s⁻¹ * MvPolynomial.X i ^ d i).IsHomogeneous (d i) := by
    apply (hG i).add
    simpa only [zero_add] using (MvPolynomial.isHomogeneous_C (Fin (n+1)) s⁻¹).mul
      (MvPolynomial.isHomogeneous_X_pow i (d i))
  obtain ⟨x,hx,hroots⟩ := (homogeneousResultant_zero_iff d hd _ hhom).mp hres
  have hsroots (i : Fin (n+1)) : MvPolynomial.eval x (MvPolynomial.C s * G i + MvPolynomial.X i ^ d i) = 0 := by
    have hh := congrArg (fun z : K => s*z) (hroots i)
    simp only [map_add,map_mul,MvPolynomial.eval_C,map_pow,MvPolynomial.eval_X,mul_zero,mul_add] at hh ⊢
    simpa only [← mul_assoc,mul_inv_cancel₀ hs,one_mul] using hh
  have hhom' (i : Fin (n+1)) : (MvPolynomial.C s * G i + MvPolynomial.X i ^ d i).IsHomogeneous (d i) := by
    apply MvPolynomial.IsHomogeneous.add _ (MvPolynomial.isHomogeneous_X_pow _ _)
    simpa only [zero_add] using (MvPolynomial.isHomogeneous_C (Fin (n+1)) s).mul (hG i)
  apply hPs
  rw [hPspec]
  exact (homogeneousResultant_zero_iff d hd _ hhom').mpr ⟨x,hx,hsroots⟩

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
open scoped RatFunc
namespace APSCounting893.Main

noncomputable def parameterSeriesHom (K : Type) [Field K] [IsAlgClosed K] [CharZero K] :
    Polynomial K →+* HahnSeries ℚ K :=
  GenericSeries.rationalSeriesHom.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K))

lemma parameterSeriesHom_injective {K : Type} [Field K] [IsAlgClosed K] [CharZero K] :
    Function.Injective (parameterSeriesHom K) :=
  (GenericSeries.rationalSeriesHom (K := K)).injective.comp (IsFractionRing.injective (Polynomial K) (RatFunc K))

lemma parameterSeriesHom_C {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (c : K) :
    parameterSeriesHom K (Polynomial.C c) = HahnSeries.C c := by
  change GenericSeries.rationalSeriesHom
    (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) c)) = HahnSeries.C c
  rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
  simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C] using
    (GenericSeries.rationalSeriesHom (K := K)).commutes c

lemma parameterSeriesHom_X {K : Type} [Field K] [IsAlgClosed K] [CharZero K] :
    parameterSeriesHom K Polynomial.X = HahnSeries.single (1 : ℚ) (1 : K) :=
  GenericSeries.rationalSeriesHom_X

lemma parameterSeriesHom_map_constant {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {σ : Type} (p : MvPolynomial σ K) :
    MvPolynomial.map (parameterSeriesHom K) (MvPolynomial.map Polynomial.C p) = MvPolynomial.map HahnSeries.C p := by
  rw [MvPolynomial.map_map]
  have hh : (parameterSeriesHom K).comp Polynomial.C = (HahnSeries.C : K →+* HahnSeries ℚ K) := by
    apply RingHom.ext
    intro c
    exact parameterSeriesHom_C c
  rw [hh]

lemma series_monomial_perturbation_no_nonzero_roots {K : Type} [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i)
    (G : Fin (n+1) → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i)) :
    ∀ x : Fin (n+1) → HahnSeries ℚ K,
      (∀ i, MvPolynomial.eval x (MvPolynomial.map HahnSeries.C (G i) +
        MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) * MvPolynomial.X i ^ d i) = 0) → x = 0 := by
  letI : IsAlgClosed (HahnSeries ℚ K) := HahnSeries.isAlgClosed_rat
  letI : CharZero (HahnSeries ℚ K) := charZero_of_injective_ringHom (HahnSeries.C : K →+* HahnSeries ℚ K).injective
  let F : Fin (n+1) → MvPolynomial (Fin (n+1)) (HahnSeries ℚ K) := fun i =>
    MvPolynomial.map HahnSeries.C (G i) + MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) * MvPolynomial.X i ^ d i
  have hF (i : Fin (n+1)) : (F i).IsHomogeneous (d i) := by
    apply (hG i).map (HahnSeries.C : K →+* HahnSeries ℚ K) |>.add
    simpa only [zero_add] using
      (MvPolynomial.isHomogeneous_C (Fin (n+1)) (HahnSeries.single (1 : ℚ) (1 : K))).mul
        (MvPolynomial.isHomogeneous_X_pow i (d i))
  have hres : homogeneousResultant d F ≠ 0 := by
    have hp := resultant_monomial_perturbation_ne_zero d hd G hG
    have hh : parameterSeriesHom K
        (homogeneousResultant d (fun i => MvPolynomial.map Polynomial.C (G i) +
          MvPolynomial.C Polynomial.X * MvPolynomial.X i ^ d i)) = homogeneousResultant d F := by
      rw [homogeneousResultant_map]
      apply congrArg (homogeneousResultant d)
      funext i
      simp only [map_add,map_mul,MvPolynomial.map_C,map_pow,MvPolynomial.map_X,
        parameterSeriesHom_X,parameterSeriesHom_map_constant]
      rfl
    intro hz
    apply hp
    apply parameterSeriesHom_injective
    rw [hh,hz,map_zero]
  intro x hx
  by_contra hzero
  exact hres ((homogeneousResultant_zero_iff d hd F hF).mpr ⟨x,hzero,hx⟩)

end APSCounting893.Main
end Component_13

section Component_14

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma homogeneousComponent_mul_homogeneous {K : Type*} [CommSemiring K] {σ : Type*}
    (p f : MvPolynomial σ K) {d D : ℕ} (hf : f.IsHomogeneous d) (hD : d ≤ D) :
    homogeneousComponent D (p * f) = homogeneousComponent (D-d) p * f := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  have hh := DirectSum.coe_decompose_mul_of_right_mem_of_le
    (MvPolynomial.homogeneousSubmodule σ K) (a := p) hf hD
  change (MvPolynomial.decomposition.decompose' (p*f) D : MvPolynomial σ K) =
    (MvPolynomial.decomposition.decompose' p (D-d) : MvPolynomial σ K) * f at hh
  simpa only [MvPolynomial.decomposition.decompose'_apply] using hh

lemma coordinate_power_mem_of_no_projective_root {K : Type*} [Field K] [IsAlgClosed K]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) K)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (f i) = 0) → x = 0)
    (j : Fin n) : ∃ N : ℕ, 0 < N ∧ MvPolynomial.X j ^ N ∈ Ideal.span (Set.range f) := by
  classical
  let I := Ideal.span (Set.range f)
  have hr : MvPolynomial.X j ∈ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have hz : x = 0 := hroot x (fun i => by
      simpa only [MvPolynomial.aeval_eq_eval] using hx (f i) (Ideal.subset_span ⟨i, rfl⟩))
    simp [hz]
  obtain ⟨N, hN⟩ := hr
  exact ⟨N+1, Nat.succ_pos _, by
    rw [pow_succ]
    exact I.mul_mem_right _ hN⟩

lemma large_monomial_mem_of_coordinate_powers {K : Type*} [CommSemiring K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (N : Fin n → ℕ)
    (hN : ∀ i, 0 < N i ∧ MvPolynomial.X i ^ N i ∈ I)
    (e : Fin n →₀ ℕ) (he : (∑ i, (N i - 1)) < e.degree) :
    MvPolynomial.monomial e (1 : K) ∈ I := by
  classical
  have hi : ∃ i, N i ≤ e i := by
    by_contra h
    push Not at h
    have hh : (∑ i, e i) ≤ ∑ i, (N i - 1) :=
      Finset.sum_le_sum (fun i _ => by have := h i; omega)
    rw [Finsupp.degree_eq_sum] at he
    omega
  obtain ⟨i, hi⟩ := hi
  have hle : Finsupp.single i (N i) ≤ e := Finsupp.single_le_iff.mpr hi
  have hm : MvPolynomial.monomial e (1 : K) =
      MvPolynomial.monomial (e - Finsupp.single i (N i)) 1 * MvPolynomial.X i ^ N i := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      tsub_add_cancel_of_le hle, one_mul]
  rw [hm]
  exact I.mul_mem_left _ (hN i).2

end APSCounting893.Main
end Component_14

section Component_15

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

abbrev DegreeMonomial (n D : ℕ) := {e : Fin n →₀ ℕ // e.degree = D}

instance degreeMonomial_finite (n D : ℕ) : Finite (DegreeMonomial n D) := by
  apply Finite.of_injective
    (fun e : DegreeMonomial n D => fun i : Fin n =>
      (⟨e.1 i, Nat.lt_succ_of_le (by
        have h := Finsupp.le_degree i e.1
        rw [e.2] at h
        exact h)⟩ : Fin (D+1)))
  intro a b h
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance degreeMonomial_fintype (n D : ℕ) : Fintype (DegreeMonomial n D) :=
  Fintype.ofFinite _

lemma homogeneous_sum_monomials {K : Type*} [CommSemiring K] {n D : ℕ}
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous D) :
    p = ∑ e : DegreeMonomial n D, MvPolynomial.monomial e.1 (p.coeff e.1) := by
  classical
  ext a
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases ha : a.degree = D
  · let a' : DegreeMonomial n D := ⟨a,ha⟩
    rw [Finset.sum_eq_single a']
    · simp [a']
    · intro b hb hba
      have hb : a ≠ b.1 := by
        intro heq
        apply hba
        exact Subtype.ext heq.symm
      simp [Ne.symm hb]
    · simp
  · rw [hp.coeff_eq_zero ha]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hab : a ≠ b.1 := by intro h; exact ha (h ▸ b.2)
    simp [Ne.symm hab]

lemma eval₂_homogeneous_sum {K R : Type*} [CommSemiring K] [CommSemiring R]
    {n D : ℕ} (f : K →+* R) (x : Fin n → R)
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous D) :
    MvPolynomial.eval₂ f x p =
      ∑ e : DegreeMonomial n D, f (p.coeff e.1) * ∏ i : Fin n, x i ^ e.1 i := by
  classical
  conv_lhs => rw [homogeneous_sum_monomials p hp]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

end APSCounting893.Main
end Component_15

section Component_16

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

abbrev BoundedDegreeMonomial (n D : ℕ) := {e : Fin n →₀ ℕ // e.degree ≤ D}

instance boundedDegreeMonomial_finite (n D : ℕ) : Finite (BoundedDegreeMonomial n D) := by
  apply Finite.of_injective (fun e : BoundedDegreeMonomial n D => fun i : Fin n =>
    (⟨e.1 i,Nat.lt_succ_of_le ((Finsupp.le_degree i e.1).trans e.2)⟩ : Fin (D+1)))
  intro a b h
  exact Subtype.ext (Finsupp.ext (fun i => congrArg Fin.val (congrFun h i)))

lemma finite_algebra_of_degree_lowering_relations {K A : Type} [Field K] [CommRing A] [Algebra K A]
    {n : ℕ} (ξ : MvPolynomial (Fin n) K →ₐ[K] A) (hξ : Function.Surjective ξ)
    (N : Fin n → ℕ) (hN : ∀ i, 0 < N i)
    (p : Fin n → MvPolynomial (Fin n) K) (hp : ∀ i, (p i).totalDegree < N i)
    (hrel : ∀ i, ξ (MvPolynomial.X i) ^ N i = ξ (p i)) : Module.Finite K A := by
  classical
  let D := ∑ i, (N i - 1)
  let S : Set A := Set.range (fun e : BoundedDegreeMonomial n D => ξ (MvPolynomial.monomial e.1 1))
  let V := Submodule.span K S
  have hmono : ∀ d : ℕ, ∀ e : Fin n →₀ ℕ, e.degree = d → ξ (MvPolynomial.monomial e 1) ∈ V := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro e he
      by_cases heD : e.degree ≤ D
      · exact Submodule.subset_span ⟨⟨e,heD⟩,rfl⟩
      have hi : ∃ i, N i ≤ e i := by
        by_contra hh
        push Not at hh
        have hh' : e.degree ≤ D := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.sum_le_sum (fun i _ => by have := hh i; omega)
        exact heD hh'
      obtain ⟨i,hi⟩ := hi
      let b := e - Finsupp.single i (N i)
      have hle : Finsupp.single i (N i) ≤ e := Finsupp.single_le_iff.mpr hi
      have hbe : b + Finsupp.single i (N i) = e := tsub_add_cancel_of_le hle
      have hdegree : b.degree + N i = e.degree := by
        have hh := congrArg Finsupp.degree hbe
        simpa only [map_add,Finsupp.degree_single] using hh
      have hprod : ξ (MvPolynomial.monomial e 1) = ξ (MvPolynomial.monomial b 1 * p i) := by
        have hh : MvPolynomial.monomial e (1 : K) = MvPolynomial.monomial b 1 * MvPolynomial.X i ^ N i := by
          rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_mul,hbe,one_mul]
        rw [hh,map_mul,map_pow,hrel,map_mul]
      rw [hprod]
      rw [(p i).as_sum,Finset.mul_sum,map_sum]
      apply Submodule.sum_mem
      intro a ha
      rw [MvPolynomial.monomial_mul,one_mul]
      have hm : ξ (MvPolynomial.monomial (b+a) ((p i).coeff a)) =
          (p i).coeff a • ξ (MvPolynomial.monomial (b+a) 1) := by
        simpa only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one] using
          map_smul ξ ((p i).coeff a) (MvPolynomial.monomial (b+a) 1)
      rw [hm]
      apply Submodule.smul_mem
      apply ih (b+a).degree _ (b+a) rfl
      have hh := MvPolynomial.le_totalDegree ha
      change a.degree ≤ (p i).totalDegree at hh
      have hh' := hp i
      rw [map_add]
      omega
  have hV : V = ⊤ := by
    apply top_unique
    intro a ha
    obtain ⟨q,rfl⟩ := hξ a
    rw [q.as_sum,map_sum]
    apply Submodule.sum_mem
    intro e he
    have hh : ξ (MvPolynomial.monomial e (q.coeff e)) = q.coeff e • ξ (MvPolynomial.monomial e 1) := by
      simpa only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one] using
        map_smul ξ (q.coeff e) (MvPolynomial.monomial e 1)
    rw [hh]
    exact V.smul_mem _ (hmono e.degree e rfl)
  have hfg : V.FG := Submodule.fg_span (Set.finite_range _)
  exact Module.Finite.of_fg_top (hV ▸ hfg)

end APSCounting893.Main
end Component_16

section Component_17

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma totalDegree_lt_of_top_component_zero {K : Type} [CommRing K] {n D : ℕ}
    (p : MvPolynomial (Fin n) K) (hD : 0 < D) (hp : p.totalDegree ≤ D)
    (hz : homogeneousComponent D p = 0) : p.totalDegree < D := by
  classical
  have hb : p.totalDegree ≤ D-1 := by
    rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro e he
    have hle := MvPolynomial.le_totalDegree he
    change e.degree ≤ p.totalDegree at hle
    have hne : e.degree ≠ D := by
      intro h
      have hh := congrArg (MvPolynomial.coeff e) hz
      rw [MvPolynomial.coeff_homogeneousComponent,if_pos h,MvPolynomial.coeff_zero] at hh
      exact (MvPolynomial.mem_support_iff.mp he) hh
    change e.degree ≤ D-1
    omega
  omega

lemma homogeneousComponent_mul_left {K : Type} [CommRing K] {n : ℕ}
    (p f : MvPolynomial (Fin n) K) {d D : ℕ} (hp : p.IsHomogeneous (D-d)) (hd : d ≤ D) :
    homogeneousComponent D (p*f) = p * homogeneousComponent d f := by
  rw [mul_comm,homogeneousComponent_mul_homogeneous f p hp (Nat.sub_le _ _),
    Nat.sub_sub_self hd,mul_comm]

end APSCounting893.Main
end Component_17

section Component_18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finite_quotient_of_no_top_form_roots {K : Type} [Field K] [IsAlgClosed K]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) K) (d : Fin m → ℕ)
    (hdeg : ∀ j, (f j).totalDegree ≤ d j)
    (hroot : ∀ x : Fin n → K, (∀ j, MvPolynomial.eval x (homogeneousComponent (d j) (f j)) = 0) → x = 0) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f)) := by
  classical
  let H : Fin m → MvPolynomial (Fin n) K := fun j => homogeneousComponent (d j) (f j)
  let J := Ideal.span (Set.range H)
  choose N0 hN0 using coordinate_power_mem_of_no_projective_root H hroot
  let N : Fin n → ℕ := fun i => N0 i + ∑ j, d j
  have hN (i : Fin n) : 0 < N i := (hN0 i).1.trans_le (Nat.le_add_right _ _)
  have hdN (i : Fin n) (j : Fin m) : d j ≤ N i := by
    have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (d k)) (Finset.mem_univ j)
    dsimp [N]
    omega
  have hpow (i : Fin n) : MvPolynomial.X i ^ N i ∈ J := by
    dsimp only [N]
    rw [pow_add]
    exact J.mul_mem_right _ (hN0 i).2
  choose u hu using (fun i => Ideal.mem_span_range_iff_exists_fun.mp (hpow i))
  let g (i : Fin n) (j : Fin m) := homogeneousComponent (N i - d j) (u i j)
  have hgH (i : Fin n) : ∑ j, g i j * H j = MvPolynomial.X i ^ N i := by
    have hh := congrArg (homogeneousComponent (N i)) (hu i)
    rw [map_sum,homogeneousComponent_eq_self (MvPolynomial.isHomogeneous_X_pow _ _)] at hh
    have hH (j : Fin m) : (H j).IsHomogeneous (d j) := homogeneousComponent_isHomogeneous _ _
    simp_rw [homogeneousComponent_mul_homogeneous _ _ (hH _) (hdN i _)] at hh
    exact hh
  let p (i : Fin n) : MvPolynomial (Fin n) K := MvPolynomial.X i ^ N i - ∑ j, g i j * f j
  have hpdeg (i : Fin n) : (p i).totalDegree ≤ N i := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact le_of_eq (MvPolynomial.totalDegree_X_pow _ _)
    · apply (MvPolynomial.totalDegree_finsetSum _ _).trans
      apply Finset.sup_le
      intro j hj
      have hgdeg : (g i j).totalDegree ≤ N i - d j :=
        (homogeneousComponent_isHomogeneous (N i - d j) (u i j)).totalDegree_le
      have hmul := MvPolynomial.totalDegree_mul (g i j) (f j)
      have hfdeg := hdeg j
      have hdji := hdN i j
      omega
  have hptop (i : Fin n) : homogeneousComponent (N i) (p i) = 0 := by
    dsimp only [p]
    rw [map_sub,map_sum,homogeneousComponent_eq_self (MvPolynomial.isHomogeneous_X_pow _ _)]
    have hg (j : Fin m) : (g i j).IsHomogeneous (N i - d j) := homogeneousComponent_isHomogeneous _ _
    simp_rw [homogeneousComponent_mul_left _ _ (hg _) (hdN i _)]
    exact sub_eq_zero.mpr (hgH i).symm
  let I := Ideal.span (Set.range f)
  let ξ := Ideal.Quotient.mkₐ K I
  have hξf (j : Fin m) : ξ (f j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
  have hrel (i : Fin n) : ξ (MvPolynomial.X i) ^ N i = ξ (p i) := by
    simp only [p,map_sub,map_sum,map_mul,hξf,mul_zero,Finset.sum_const_zero,sub_zero,map_pow]
  exact finite_algebra_of_degree_lowering_relations ξ (Ideal.Quotient.mkₐ_surjective K I) N hN p
    (fun i => totalDegree_lt_of_top_component_zero (p i) (hN i) (hpdeg i) (hptop i)) hrel

end APSCounting893.Main
end Component_18

section Component_19

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finite_zeroLocus_of_module_finite_quotient {K : Type} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [Module.Finite K (MvPolynomial (Fin n) K ⧸ I)] :
    (MvPolynomial.zeroLocus K I).Finite := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let ξ := Ideal.Quotient.mkₐ K I
  let point : (A →ₐ[K] K) → (Fin n → K) := fun ρ i => ρ (ξ (MvPolynomial.X i))
  apply (Set.finite_range point).subset
  intro x hx
  let ρ : A →ₐ[K] K := Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) hx
  refine ⟨ρ,?_⟩
  funext i
  change MvPolynomial.aeval (R := K) x (MvPolynomial.X i) = x i
  exact MvPolynomial.aeval_X x i

lemma finite_zeroLocus_of_no_top_form_roots {K : Type} [Field K] [IsAlgClosed K]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) K) (d : Fin m → ℕ)
    (hdeg : ∀ j, (f j).totalDegree ≤ d j)
    (hroot : ∀ x : Fin n → K, (∀ j, MvPolynomial.eval x (homogeneousComponent (d j) (f j)) = 0) → x = 0) :
    {x : Fin n → K | ∀ j, MvPolynomial.eval x (f j) = 0}.Finite := by
  letI := finite_quotient_of_no_top_form_roots f d hdeg hroot
  have hh := finite_zeroLocus_of_module_finite_quotient (Ideal.span (Set.range f))
  simpa only [MvPolynomial.zeroLocus_span,Set.forall_mem_range,MvPolynomial.aeval_eq_eval] using hh

end APSCounting893.Main
end Component_19

section Component_20

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma map_homogeneousComponent {K L σ : Type} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (D : ℕ) (p : MvPolynomial σ K) :
    MvPolynomial.map f (homogeneousComponent D p) = homogeneousComponent D (MvPolynomial.map f p) := by
  classical
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_map,MvPolynomial.coeff_homogeneousComponent]
  split_ifs
  · rfl
  · exact map_zero f

lemma series_monomial_perturbation_finite {K : Type} [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i)
    (f : Fin (n+1) → MvPolynomial (Fin (n+1)) K) (hdeg : ∀ i, (f i).totalDegree ≤ d i) :
    {x : Fin (n+1) → HahnSeries ℚ K | ∀ i, MvPolynomial.eval x
      (MvPolynomial.map HahnSeries.C (f i) +
        MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) * MvPolynomial.X i ^ d i) = 0}.Finite := by
  letI : IsAlgClosed (HahnSeries ℚ K) := HahnSeries.isAlgClosed_rat
  let H : Fin (n+1) → MvPolynomial (Fin (n+1)) K := fun i => homogeneousComponent (d i) (f i)
  let G : Fin (n+1) → MvPolynomial (Fin (n+1)) (HahnSeries ℚ K) := fun i =>
    MvPolynomial.map HahnSeries.C (f i) +
      MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) * MvPolynomial.X i ^ d i
  have hG (i : Fin (n+1)) : (G i).totalDegree ≤ d i := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · rw [MvPolynomial.totalDegree]
      apply Finset.sup_le
      intro e he
      exact (MvPolynomial.le_totalDegree
        (MvPolynomial.support_map_subset (HahnSeries.C : K →+* HahnSeries ℚ K) (f i) he)).trans (hdeg i)
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X_pow,zero_add,le_refl]
  have htop (i : Fin (n+1)) : homogeneousComponent (d i) (G i) =
      MvPolynomial.map HahnSeries.C (H i) +
        MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) * MvPolynomial.X i ^ d i := by
    dsimp only [G,H]
    rw [map_add,homogeneousComponent_C_mul,
      homogeneousComponent_eq_self (MvPolynomial.isHomogeneous_X_pow _ _),← map_homogeneousComponent]
  apply finite_zeroLocus_of_no_top_form_roots G d hG
  intro x hx
  apply series_monomial_perturbation_no_nonzero_roots d hd H
    (fun i => homogeneousComponent_isHomogeneous _ _) x
  intro i
  rw [← htop]
  exact hx i

end APSCounting893.Main
end Component_20

section Component_21

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_homogenize_infinity {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (x : Fin n → K) :
    MvPolynomial.eval₂ f (Fin.cons 0 x) (homogenizeAll d p) =
      MvPolynomial.eval₂ f x (homogeneousComponent d p) := by
  classical
  rw [homogenizeAll,MvPolynomial.eval₂_sum,homogeneousComponent_apply,MvPolynomial.eval₂_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_homogenize_monomial]
  simp only [Fin.cons_zero,Fin.cons_succ]
  have hcount : e.sum (fun _ k => k) = e.degree := rfl
  rw [hcount]
  by_cases h : e.degree = d
  · simp only [h,Nat.sub_self,pow_zero,mul_one,ite_true,MvPolynomial.eval₂_monomial]
  · have hle := (MvPolynomial.le_totalDegree he).trans hd
    change e.degree ≤ d at hle
    have hlt : e.degree < d := lt_of_le_of_ne hle h
    simp only [if_neg h,zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)),mul_zero,zero_mul]

end APSCounting893.Main
end Component_21

section Component_22

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma coordinate_power_mem_of_no_projective_root_extension {K E : Type}
    [Field K] [Field E] [Algebra K E] [IsAlgClosed E]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) K)
    (hroot : ∀ x : Fin n → E, (∀ i, MvPolynomial.eval₂ (algebraMap K E) x (f i) = 0) → x = 0)
    (j : Fin n) : ∃ N : ℕ, 0 < N ∧ MvPolynomial.X j ^ N ∈ Ideal.span (Set.range f) := by
  classical
  let I := Ideal.span (Set.range f)
  have hr : MvPolynomial.X j ∈ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := E)]
    intro x hx
    have hz : x = 0 := hroot x (fun i => by
      simpa only [MvPolynomial.aeval_def] using hx (f i) (Ideal.subset_span ⟨i,rfl⟩))
    rw [MvPolynomial.aeval_X,hz]
    rfl
  obtain ⟨N,hN⟩ := hr
  exact ⟨N+1,Nat.succ_pos _,by rw [pow_succ]; exact I.mul_mem_right _ hN⟩

end APSCounting893.Main
end Component_22

section Component_23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finite_quotient_of_no_top_form_roots_extension {K E : Type}
    [Field K] [Field E] [Algebra K E] [IsAlgClosed E]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) K) (d : Fin m → ℕ)
    (hdeg : ∀ j, (f j).totalDegree ≤ d j)
    (hroot : ∀ x : Fin n → E, (∀ j, MvPolynomial.eval₂ (algebraMap K E) x (homogeneousComponent (d j) (f j)) = 0) → x = 0) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f)) := by
  classical
  let H : Fin m → MvPolynomial (Fin n) K := fun j => homogeneousComponent (d j) (f j)
  let J := Ideal.span (Set.range H)
  choose N0 hN0 using coordinate_power_mem_of_no_projective_root_extension H hroot
  let N : Fin n → ℕ := fun i => N0 i + ∑ j, d j
  have hN (i : Fin n) : 0 < N i := (hN0 i).1.trans_le (Nat.le_add_right _ _)
  have hdN (i : Fin n) (j : Fin m) : d j ≤ N i := by
    have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (d k)) (Finset.mem_univ j)
    dsimp [N]
    omega
  have hpow (i : Fin n) : MvPolynomial.X i ^ N i ∈ J := by
    dsimp only [N]
    rw [pow_add]
    exact J.mul_mem_right _ (hN0 i).2
  choose u hu using (fun i => Ideal.mem_span_range_iff_exists_fun.mp (hpow i))
  let g (i : Fin n) (j : Fin m) := homogeneousComponent (N i - d j) (u i j)
  have hgH (i : Fin n) : ∑ j, g i j * H j = MvPolynomial.X i ^ N i := by
    have hh := congrArg (homogeneousComponent (N i)) (hu i)
    rw [map_sum,homogeneousComponent_eq_self (MvPolynomial.isHomogeneous_X_pow _ _)] at hh
    have hH (j : Fin m) : (H j).IsHomogeneous (d j) := homogeneousComponent_isHomogeneous _ _
    simp_rw [homogeneousComponent_mul_homogeneous _ _ (hH _) (hdN i _)] at hh
    exact hh
  let p (i : Fin n) : MvPolynomial (Fin n) K := MvPolynomial.X i ^ N i - ∑ j, g i j * f j
  have hpdeg (i : Fin n) : (p i).totalDegree ≤ N i := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact le_of_eq (MvPolynomial.totalDegree_X_pow _ _)
    · apply (MvPolynomial.totalDegree_finsetSum _ _).trans
      apply Finset.sup_le
      intro j hj
      have hgdeg : (g i j).totalDegree ≤ N i - d j :=
        (homogeneousComponent_isHomogeneous (N i - d j) (u i j)).totalDegree_le
      have hmul := MvPolynomial.totalDegree_mul (g i j) (f j)
      have hfdeg := hdeg j
      have hdji := hdN i j
      omega
  have hptop (i : Fin n) : homogeneousComponent (N i) (p i) = 0 := by
    dsimp only [p]
    rw [map_sub,map_sum,homogeneousComponent_eq_self (MvPolynomial.isHomogeneous_X_pow _ _)]
    have hg (j : Fin m) : (g i j).IsHomogeneous (N i - d j) := homogeneousComponent_isHomogeneous _ _
    simp_rw [homogeneousComponent_mul_left _ _ (hg _) (hdN i _)]
    exact sub_eq_zero.mpr (hgH i).symm
  let I := Ideal.span (Set.range f)
  let ξ := Ideal.Quotient.mkₐ K I
  have hξf (j : Fin m) : ξ (f j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
  have hrel (i : Fin n) : ξ (MvPolynomial.X i) ^ N i = ξ (p i) := by
    simp only [p,map_sub,map_sum,map_mul,hξf,mul_zero,Finset.sum_const_zero,sub_zero,map_pow]
  exact finite_algebra_of_degree_lowering_relations ξ (Ideal.Quotient.mkₐ_surjective K I) N hN p
    (fun i => totalDegree_lt_of_top_component_zero (p i) (hN i) (hpdeg i) (hptop i)) hrel

end APSCounting893.Main
end Component_23

section Component_24

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial HahnSeries
open scoped RatFunc
namespace APSCounting893.Main.GenericSeries

lemma puiseux_of_algebraic_parameter {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (x : HahnSeries ℚ K)
    (hx : letI : Algebra (RatFunc K) (HahnSeries ℚ K) := (rationalSeriesHom (K := K)).toRingHom.toAlgebra
      IsIntegral (RatFunc K) x) : IsPuiseuxOver x := by
  classical
  letI : Algebra (RatFunc K) (HahnSeries ℚ K) := (rationalSeriesHom (K := K)).toRingHom.toAlgebra
  let q := (minpoly (RatFunc K) x).map (rationalSeriesHom (K := K)).toRingHom
  have hq : q ≠ 0 := (minpoly.monic hx).map (rationalSeriesHom (K := K)).toRingHom |>.ne_zero
  have hcoeff (i : ℕ) : HahnSeries.HasRamBound 1 (q.coeff i) := by
    simpa [q] using rationalSeriesHom_puiseux ((minpoly (RatFunc K) x).coeff i)
  have hroot : q.IsRoot x := by
    change q.eval x = 0
    dsimp only [q]
    rw [Polynomial.eval_map]
    exact minpoly.aeval (RatFunc K) x
  exact ⟨q.natDegree.factorial,Nat.factorial_pos _,
    (HahnSeries.mem_puiseuxRamSubfield_iff (Nat.factorial_pos _)).mpr
      (HahnSeries.hasRamBound_natDegree_factorial_of_isRoot hq hcoeff hroot)⟩

end APSCounting893.Main.GenericSeries
end Component_24

section Component_25

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
open scoped RatFunc
namespace APSCounting893.Main

lemma rationalSeriesHom_map_constant {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {σ : Type} (p : MvPolynomial σ K) :
    MvPolynomial.map (GenericSeries.rationalSeriesHom (K := K)).toRingHom
      (MvPolynomial.map (algebraMap K (RatFunc K)) p) = MvPolynomial.map HahnSeries.C p := by
  rw [MvPolynomial.map_map]
  have hh : (GenericSeries.rationalSeriesHom (K := K)).toRingHom.comp (algebraMap K (RatFunc K)) =
      (HahnSeries.C : K →+* HahnSeries ℚ K) := by
    apply RingHom.ext
    intro c
    change GenericSeries.rationalSeriesHom (K := K) (algebraMap K (RatFunc K) c) = HahnSeries.C c
    simpa only [HahnSeries.algebraMap_apply',
      PowerSeries.algebraMap_apply,Algebra.algebraMap_self,RingHom.id_apply,HahnSeries.ofPowerSeries_C] using
      (GenericSeries.rationalSeriesHom (K := K)).commutes c
  rw [hh]

lemma series_monomial_perturbation_coordinates_integral {K : Type} [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i)
    (f : Fin (n+1) → MvPolynomial (Fin (n+1)) K) (hdeg : ∀ i, (f i).totalDegree ≤ d i)
    (x : Fin (n+1) → HahnSeries ℚ K)
    (hx : ∀ i, MvPolynomial.eval x (MvPolynomial.map HahnSeries.C (f i) +
      MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) * MvPolynomial.X i ^ d i) = 0) :
    ∀ j, letI : Algebra (RatFunc K) (HahnSeries ℚ K) :=
      (GenericSeries.rationalSeriesHom (K := K)).toRingHom.toAlgebra
      IsIntegral (RatFunc K) (x j) := by
  classical
  let R := RatFunc K
  let E := HahnSeries ℚ K
  let ρ := (GenericSeries.rationalSeriesHom (K := K)).toRingHom
  letI : Algebra R E := ρ.toAlgebra
  letI : IsAlgClosed E := HahnSeries.isAlgClosed_rat
  let F : Fin (n+1) → MvPolynomial (Fin (n+1)) R := fun i =>
    MvPolynomial.map (algebraMap K R) (f i) + MvPolynomial.C RatFunc.X * MvPolynomial.X i ^ d i
  have hmap (i : Fin (n+1)) : MvPolynomial.map ρ (F i) =
      MvPolynomial.map HahnSeries.C (f i) +
        MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) * MvPolynomial.X i ^ d i := by
    dsimp only [F]
    rw [map_add,map_mul,MvPolynomial.map_C,map_pow,MvPolynomial.map_X,rationalSeriesHom_map_constant]
    change _ + MvPolynomial.C (GenericSeries.rationalSeriesHom (K := K) RatFunc.X) * _ = _
    have hX : GenericSeries.rationalSeriesHom (K := K) (RatFunc.X : RatFunc K) =
        HahnSeries.single (1 : ℚ) (1 : K) := by
      exact GenericSeries.rationalSeriesHom_X (K := K)
    rw [hX]
  have hFdeg (i : Fin (n+1)) : (F i).totalDegree ≤ d i := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · rw [MvPolynomial.totalDegree]
      apply Finset.sup_le
      intro e he
      exact (MvPolynomial.le_totalDegree
        (MvPolynomial.support_map_subset (algebraMap K R) (f i) he)).trans (hdeg i)
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X_pow,zero_add,le_refl]
  have htop (i : Fin (n+1)) :
      MvPolynomial.map ρ (homogeneousComponent (d i) (F i)) =
        MvPolynomial.map HahnSeries.C (homogeneousComponent (d i) (f i)) +
          MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) * MvPolynomial.X i ^ d i := by
    rw [map_homogeneousComponent,hmap,map_add,homogeneousComponent_C_mul,
      homogeneousComponent_eq_self (MvPolynomial.isHomogeneous_X_pow _ _),← map_homogeneousComponent]
  have hnoTop (z : Fin (n+1) → E)
      (hz : ∀ i, MvPolynomial.eval₂ (algebraMap R E) z (homogeneousComponent (d i) (F i)) = 0) : z = 0 := by
    apply series_monomial_perturbation_no_nonzero_roots d hd
      (fun i => homogeneousComponent (d i) (f i)) (fun i => homogeneousComponent_isHomogeneous _ _) z
    intro i
    rw [← htop, MvPolynomial.eval_map]
    exact hz i
  let I := Ideal.span (Set.range F)
  let A := MvPolynomial (Fin (n+1)) R ⧸ I
  letI : Module.Finite R A := finite_quotient_of_no_top_form_roots_extension F d hFdeg hnoTop
  have hFx (i : Fin (n+1)) : MvPolynomial.aeval (R := R) x (F i) = 0 := by
    change MvPolynomial.eval₂ ρ x (F i) = 0
    rw [← MvPolynomial.eval_map,hmap]
    exact hx i
  have hI (p : MvPolynomial (Fin (n+1)) R) (hp : p ∈ I) : MvPolynomial.aeval (R := R) x p = 0 := by
    have hle : I ≤ RingHom.ker (MvPolynomial.aeval (R := R) x).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      exact hFx i
    exact hle hp
  let ψ : A →ₐ[R] E := Ideal.Quotient.liftₐ I (MvPolynomial.aeval (R := R) x) hI
  intro j
  have hi : IsIntegral R (Ideal.Quotient.mkₐ R I (MvPolynomial.X j)) := Algebra.IsIntegral.isIntegral _
  have hm := hi.map ψ
  have hval : ψ (Ideal.Quotient.mkₐ R I (MvPolynomial.X j)) = x j := by
    change MvPolynomial.aeval (R := R) x (MvPolynomial.X j) = x j
    exact MvPolynomial.aeval_X x j
  rw [hval] at hm
  exact hm

lemma series_monomial_perturbation_coordinates_puiseux {K : Type} [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i)
    (f : Fin (n+1) → MvPolynomial (Fin (n+1)) K) (hdeg : ∀ i, (f i).totalDegree ≤ d i)
    (x : Fin (n+1) → HahnSeries ℚ K)
    (hx : ∀ i, MvPolynomial.eval x (MvPolynomial.map HahnSeries.C (f i) +
      MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) * MvPolynomial.X i ^ d i) = 0) :
    ∀ j, GenericSeries.IsPuiseuxOver (x j) := by
  intro j
  exact GenericSeries.puiseux_of_algebraic_parameter _
    (series_monomial_perturbation_coordinates_integral d hd f hdeg x hx j)

end APSCounting893.Main
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma totalDegree_map_le {R K σ : Type} [CommSemiring R] [CommSemiring K]
    (f : R →+* K) (p : MvPolynomial σ R) : (MvPolynomial.map f p).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  exact MvPolynomial.le_totalDegree (MvPolynomial.support_map_subset f p he)

lemma epsilon_equationWithAux_map (F : RawMap) (c alpha : Affine ℂ F.n)
    (i : Fin (F.n + (F.n+1))) :
    (MvPolynomial.map epsilonAuxHom (equationWithAux F c alpha i) : MvPolynomial (Fin (F.n+(F.n+1))) EpsilonAmbient) =
      MvPolynomial.map (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient) (MvPolynomial.map tAuxHom (equationWithAux F c alpha i)) := by
  rw [equationWithAux,MvPolynomial.map_map,MvPolynomial.map_map,MvPolynomial.map_map]
  have hh : epsilonAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      ((HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient).comp tAuxHom).comp
        (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) := by
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply]
    rw [epsilonAux_polynomial_coefficients,tAux_polynomial_coefficients]
  rw [hh]

lemma epsilon_perturbed_chart_eval (F : RawMap) (c alpha : Affine ℂ F.n)
    (d : Fin (F.n+(F.n+1)) → ℕ) (hd : HomogenizingDegrees F c alpha d)
    (x : Fin (F.n+(F.n+1)) → EpsilonAmbient) (i : Fin (F.n+(F.n+1))) :
    MvPolynomial.eval₂ epsilonAuxHom (Fin.cons 1 x) (perturbedEquation F c alpha d i) =
      MvPolynomial.eval x (MvPolynomial.map (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient) (MvPolynomial.map tAuxHom (equationWithAux F c alpha i)) +
        MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : PuiseuxAmbient)) * MvPolynomial.X i ^ d i) := by
  have hh := eval_homogenize_scaled (K := EpsilonAmbient) epsilonAuxHom (equationWithAux F c alpha i) (d i) (hd i).2.2 1 x
  have hpoint : (Fin.cases (1 : EpsilonAmbient) (fun j => 1*x j) : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) = Fin.cons 1 x := by
    funext j
    refine Fin.cases (by rfl) (fun j => ?_) j
    exact one_mul (x j)
  rw [hpoint] at hh
  have hOne : (1 : EpsilonAmbient) ^ d i = 1 := one_pow (M := EpsilonAmbient) (d i)
  rw [hOne] at hh
  have hMul : (1 : EpsilonAmbient) * MvPolynomial.eval₂ epsilonAuxHom x (equationWithAux F c alpha i) =
      MvPolynomial.eval₂ epsilonAuxHom x (equationWithAux F c alpha i) := one_mul (M := EpsilonAmbient) _
  rw [hMul] at hh
  rw [perturbedEquation,MvPolynomial.eval₂_add,homogenizedEquation,hh,epsilon_equationWithAux_eval,
    MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X]
  simp only [map_add,map_mul,MvPolynomial.eval_map,MvPolynomial.eval_C,map_pow,MvPolynomial.eval_X,
    Fin.cons_succ]
  simp [epsilonAuxHom]

lemma epsilon_perturbed_homogeneous (F : RawMap) (c alpha : Affine ℂ F.n)
    (d : Fin (F.n+(F.n+1)) → ℕ) (hd : HomogenizingDegrees F c alpha d)
    (i : Fin (F.n+(F.n+1))) :
    (MvPolynomial.map epsilonAuxHom (perturbedEquation F c alpha d i) : MvPolynomial (Fin (F.n+(F.n+1)+1)) EpsilonAmbient).IsHomogeneous (d i) := by
  apply MvPolynomial.IsHomogeneous.map
  apply MvPolynomial.IsHomogeneous.add
  · exact homogenizeAll_homogeneous _ _ (hd i).2.2
  · simpa only [zero_add] using
      (MvPolynomial.isHomogeneous_C (Fin (F.n+(F.n+1)+1)) (MvPolynomial.X (0 : Fin 4) : Aux)).mul
        (MvPolynomial.isHomogeneous_X_pow i.succ (d i))

lemma epsilon_perturbed_infinity_eval (F : RawMap) (c alpha : Affine ℂ F.n)
    (d : Fin (F.n+(F.n+1)) → ℕ) (hd : HomogenizingDegrees F c alpha d)
    (x : Fin (F.n+(F.n+1)) → EpsilonAmbient) (i : Fin (F.n+(F.n+1))) :
    MvPolynomial.eval₂ epsilonAuxHom (Fin.cons 0 x) (perturbedEquation F c alpha d i) =
      MvPolynomial.eval x
        (MvPolynomial.map (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient) (homogeneousComponent (d i)
          (MvPolynomial.map tAuxHom (equationWithAux F c alpha i))) +
        MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : PuiseuxAmbient)) * MvPolynomial.X i ^ d i) := by
  rw [perturbedEquation,MvPolynomial.eval₂_add,homogenizedEquation,
    eval_homogenize_infinity (K := EpsilonAmbient) epsilonAuxHom _ _ (hd i).2.2]
  rw [← MvPolynomial.eval_map,map_homogeneousComponent,epsilon_equationWithAux_map,
    ← map_homogeneousComponent]
  simp only [map_add,map_mul,MvPolynomial.eval_C,map_pow,MvPolynomial.eval_X,
    MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,
    Fin.cons_succ]
  simp [epsilonAuxHom]

end APSCounting893.Main
end Component_26

section Component_27

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

lemma exists_regular_projective_ratio {K : Type} [Field K] {n : ℕ}
    (v : Fin n → HahnSeries ℚ K) (hv : v ≠ 0) :
    ∃ j : Fin n, v j ≠ 0 ∧ ∀ i, 0 ≤ (v i / v j).orderTop := by
  classical
  have hex : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  let B := Finset.univ.filter (fun i => v i ≠ 0)
  have hB : B.Nonempty := by obtain ⟨j,hj⟩ := hex; exact ⟨j,by simp [B,hj]⟩
  obtain ⟨j,hjB,hmin⟩ := B.exists_min_image (fun i => (v i).order) hB
  have hj : v j ≠ 0 := (Finset.mem_filter.mp hjB).2
  refine ⟨j,hj,?_⟩
  intro i
  by_cases hi : v i = 0
  · simp [hi]
  have hq : v i / v j ≠ 0 := div_ne_zero hi hj
  have hmi := hmin i (by simp [B,hi])
  have he := HahnSeries.orderTop_mul (v i / v j) (v j)
  rw [div_mul_cancel₀ _ hj] at he
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hi,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hq,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hj,← WithTop.coe_add] at he
  have horder : (v i).order = (v i / v j).order + (v j).order := WithTop.coe_inj.mp he
  apply HahnSeries.zero_le_orderTop_iff.mpr
  linarith

end APSCounting893.Main
end Component_27

section Component_28

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
open scoped RatFunc
namespace APSCounting893.Main

lemma exists_regular_puiseux_projective_rescaling {K : Type} [Field K] [IsAlgClosed K]
    [CharZero K] {n : ℕ} (v : Fin n → HahnSeries ℚ K) (hv : v ≠ 0)
    (hInt : ∀ i, letI : Algebra (RatFunc K) (HahnSeries ℚ K) :=
      (GenericSeries.rationalSeriesHom (K := K)).toRingHom.toAlgebra
      IsIntegral (RatFunc K) (v i)) :
    ∃ (q : Fin n → HahnSeries ℚ K) (a : HahnSeries ℚ K), a ≠ 0 ∧ q = a • v ∧
      (∀ i, GenericSeries.IsPuiseuxOver (q i) ∧ 0 ≤ (q i).orderTop) ∧
      ∃ j, (q j).orderTop = 0 := by
  classical
  letI : Algebra (RatFunc K) (HahnSeries ℚ K) :=
    (GenericSeries.rationalSeriesHom (K := K)).toRingHom.toAlgebra
  obtain ⟨j,hj,hreg⟩ := exists_regular_projective_ratio v hv
  let q : Fin n → HahnSeries ℚ K := fun i => v i / v j
  refine ⟨q,(v j)⁻¹,inv_ne_zero hj,?_,?_,?_⟩
  · funext i
    simp only [q,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  · intro i
    refine ⟨GenericSeries.puiseux_of_algebraic_parameter _ ?_,hreg i⟩
    change IsIntegral (RatFunc K) (v i / v j)
    rw [div_eq_mul_inv]
    exact (hInt i).mul (hInt j).inv
  · refine ⟨j,?_⟩
    change (v j / v j).orderTop = 0
    rw [div_self hj]
    simp

end APSCounting893.Main
end Component_28

section Component_29

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped Pointwise
namespace APSCounting893.Main

lemma projectiveRepresentative_smul {K : Type} [Field K] {n : ℕ}
    (a : K) (ha : a ≠ 0) (v : Fin n → K) :
    projectiveRepresentative (a • v) = projectiveRepresentative v := by
  classical
  have hB : Finset.univ.filter (fun i => (a • v) i ≠ 0) = Finset.univ.filter (fun i => v i ≠ 0) := by
    ext i
    simp [ha]
  unfold projectiveRepresentative
  rw [hB]
  split_ifs with h
  · funext i
    change (a * v i) / (a * v ((Finset.univ.filter (fun j => v j ≠ 0)).min' h)) = _
    exact mul_div_mul_left _ _ ha
  · rfl

end APSCounting893.Main
end Component_29

section Component_30

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

lemma projective_residue_eq_of_regular_rescaling {K : Type} [Field K] {n : ℕ}
    (q r : Fin n → HahnSeries ℚ K)
    (hq : ∀ j, 0 ≤ (q j).orderTop) (hr : ∀ j, 0 ≤ (r j).orderTop)
    (hq0 : ∃ j, (q j).orderTop = 0) (hr0 : ∃ j, (r j).orderTop = 0)
    (a : HahnSeries ℚ K) (hscale : r = a • q) :
    projectiveRepresentative (fun j => (r j).coeff 0) =
      projectiveRepresentative (fun j => (q j).coeff 0) := by
  classical
  obtain ⟨j,hj⟩ := hq0
  have ha : 0 ≤ a.orderTop := by
    have he := HahnSeries.orderTop_mul a (q j)
    rw [hj,add_zero] at he
    have hrj := hr j
    have hsj : r j = a * q j := by simpa only [Pi.smul_apply,smul_eq_mul] using congrFun hscale j
    rw [hsj,he] at hrj
    exact hrj
  have hcoeff (i : Fin n) : (r i).coeff 0 = a.coeff 0 * (q i).coeff 0 := by
    have hsi : r i = a * q i := by simpa only [Pi.smul_apply,smul_eq_mul] using congrFun hscale i
    rw [hsi]
    exact hahn_coeff_zero_mul_nonnegative a (q i) ha (hq i)
  have ha0 : a.coeff 0 ≠ 0 := by
    obtain ⟨k,hk⟩ := hr0
    have hk0 := HahnSeries.coeff_orderTop_ne hk
    rw [hcoeff] at hk0
    exact fun hz => hk0 (by rw [hz,zero_mul])
  have heq : (fun j => (r j).coeff 0) = a.coeff 0 • (fun j => (q j).coeff 0) := by
    funext j
    exact hcoeff j
  rw [heq,projectiveRepresentative_smul _ ha0]

end APSCounting893.Main
end Component_30

section Component_31

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
open scoped RatFunc
namespace APSCounting893.Main

lemma finite_projective_series_limits {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {n m : ℕ} (d : Fin m → ℕ)
    (G : Fin m → MvPolynomial (Fin (n+1)) (HahnSeries ℚ K))
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hnoInf : ∀ q : Fin (n+1) → HahnSeries ℚ K, q 0 = 0 →
      (∀ i, MvPolynomial.eval q (G i) = 0) → q = 0)
    (S : Finset (Fin n → HahnSeries ℚ K))
    (hS : (S : Set _) = {x | ∀ i, MvPolynomial.eval (Fin.cons 1 x) (G i) = 0})
    (hInt : ∀ x ∈ S, ∀ j, letI : Algebra (RatFunc K) (HahnSeries ℚ K) :=
      (GenericSeries.rationalSeriesHom (K := K)).toRingHom.toAlgebra
      IsIntegral (RatFunc K) (x j)) :
    {z : Fin (n+1) → K | ∃ q : Fin (n+1) → HahnSeries ℚ K,
      (∀ j, GenericSeries.IsPuiseuxOver (q j) ∧ 0 ≤ (q j).orderTop) ∧
      (∃ j, (q j).orderTop = 0) ∧ (∀ i, MvPolynomial.eval q (G i) = 0) ∧
      z = projectiveRepresentative (fun j => (q j).coeff 0)}.Finite := by
  classical
  letI : Algebra (RatFunc K) (HahnSeries ℚ K) :=
    (GenericSeries.rationalSeriesHom (K := K)).toRingHom.toAlgebra
  have hex (x : S) : ∃ (q : Fin (n+1) → HahnSeries ℚ K) (a : HahnSeries ℚ K),
      a ≠ 0 ∧ q = a • (Fin.cons 1 x.1) ∧
      (∀ j, GenericSeries.IsPuiseuxOver (q j) ∧ 0 ≤ (q j).orderTop) ∧
      ∃ j, (q j).orderTop = 0 := by
    apply exists_regular_puiseux_projective_rescaling
    · intro hh
      have h0 := congrFun hh 0
      simpa using h0
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact isIntegral_one
      · exact hInt x.1 x.2 j
  choose Q a ha hQ hreg hunit using hex
  apply (Set.finite_range (fun x : S => projectiveRepresentative (fun j => (Q x j).coeff 0))).subset
  rintro z ⟨q,hq,hq0,hroots,hz⟩
  have hqne : q ≠ 0 := by
    intro hh
    obtain ⟨j,hj⟩ := hq0
    simp only [hh,Pi.zero_apply,HahnSeries.orderTop_zero] at hj
    exact WithTop.top_ne_coe hj
  have hqzero : q 0 ≠ 0 := by intro hh; exact hqne (hnoInf q hh hroots)
  let y : Fin n → HahnSeries ℚ K := fun j => (q 0)⁻¹ * q j.succ
  have hy : (Fin.cons 1 y : Fin (n+1) → HahnSeries ℚ K) = (q 0)⁻¹ • q := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [hqzero]
    · rfl
  have hyroot (i : Fin m) : MvPolynomial.eval (Fin.cons 1 y) (G i) = 0 := by
    rw [hy]
    change MvPolynomial.eval₂ (RingHom.id (HahnSeries ℚ K)) (fun j => (q 0)⁻¹ * q j) (G i) = 0
    rw [homogeneous_eval₂_scaled _ _ (hG i),MvPolynomial.eval₂_id,hroots i,mul_zero]
  have hyS : y ∈ S := by
    change y ∈ (S : Set _)
    rw [hS]
    exact hyroot
  let x : S := ⟨y,hyS⟩
  have hscale : Q x = (a x * (q 0)⁻¹) • q := by
    rw [hQ]
    change a x • (Fin.cons 1 y : Fin (n+1) → HahnSeries ℚ K) = _
    rw [hy,smul_smul]
  have he := projective_residue_eq_of_regular_rescaling q (Q x)
    (fun j => (hq j).2) (fun j => (hreg x j).2) hq0 (hunit x) _ hscale
  exact ⟨x,he.trans hz.symm⟩

end APSCounting893.Main
end Component_31

section Component_32

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
open scoped RatFunc
namespace APSCounting893.Main

lemma epsilon_perturbed_no_infinity (F : RawMap) (c alpha : Affine ℂ F.n)
    (d : Fin (F.n+(F.n+1)) → ℕ) (hd : HomogenizingDegrees F c alpha d)
    (q : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) (hq0 : q 0 = 0)
    (hroot : ∀ i, MvPolynomial.eval₂ epsilonAuxHom q (perturbedEquation F c alpha d i) = 0) : q = 0 := by
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  letI : CharZero PuiseuxAmbient := charZero_of_injective_ringHom (HahnSeries.C : ℂ →+* PuiseuxAmbient).injective
  let f := fun i => MvPolynomial.map tAuxHom (equationWithAux F c alpha i)
  let x := fun j : Fin (F.n+(F.n+1)) => q j.succ
  have hpoint : (Fin.cons 0 x : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) = q := by
    funext j
    refine Fin.cases (by simpa using hq0.symm) (fun j => rfl) j
  have hz : x = 0 := series_monomial_perturbation_no_nonzero_roots d (fun i => (hd i).1)
    (fun i => homogeneousComponent (d i) (f i)) (fun i => homogeneousComponent_isHomogeneous _ _) x (by
      intro i
      have hh := hroot i
      rw [← hpoint,epsilon_perturbed_infinity_eval F c alpha d hd] at hh
      exact hh)
  rw [← hpoint,hz]
  funext j
  exact Fin.cases rfl (fun j => rfl) j

lemma epsilon_perturbed_affine_roots_finite (F : RawMap) (c alpha : Affine ℂ F.n)
    (d : Fin (F.n+(F.n+1)) → ℕ) (hd : HomogenizingDegrees F c alpha d) :
    {x : Fin (F.n+(F.n+1)) → EpsilonAmbient |
      ∀ i, MvPolynomial.eval₂ epsilonAuxHom (Fin.cons 1 x) (perturbedEquation F c alpha d i) = 0}.Finite := by
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  letI : CharZero PuiseuxAmbient := charZero_of_injective_ringHom (HahnSeries.C : ℂ →+* PuiseuxAmbient).injective
  let f := fun i => MvPolynomial.map tAuxHom (equationWithAux F c alpha i)
  have hdeg (i : Fin (F.n+(F.n+1))) : (f i).totalDegree ≤ d i :=
    (totalDegree_map_le _ _).trans (hd i).2.2
  have hh : {x : Fin (F.n+(F.n+1)) → EpsilonAmbient | ∀ i,
      MvPolynomial.eval x (MvPolynomial.map (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient) (f i) +
        MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : PuiseuxAmbient)) * MvPolynomial.X i ^ d i) = 0}.Finite :=
    series_monomial_perturbation_finite d (fun i => (hd i).1) f hdeg
  simpa only [epsilon_perturbed_chart_eval F c alpha d hd,f] using hh

lemma epsilon_perturbed_affine_coordinates_integral (F : RawMap) (c alpha : Affine ℂ F.n)
    (d : Fin (F.n+(F.n+1)) → ℕ) (hd : HomogenizingDegrees F c alpha d)
    (x : Fin (F.n+(F.n+1)) → EpsilonAmbient)
    (hx : ∀ i, MvPolynomial.eval₂ epsilonAuxHom (Fin.cons 1 x) (perturbedEquation F c alpha d i) = 0) :
    ∀ j, letI : Algebra (RatFunc PuiseuxAmbient) EpsilonAmbient :=
      (GenericSeries.rationalSeriesHom (K := PuiseuxAmbient)).toRingHom.toAlgebra
      IsIntegral (RatFunc PuiseuxAmbient) (x j) := by
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  letI : CharZero PuiseuxAmbient := charZero_of_injective_ringHom (HahnSeries.C : ℂ →+* PuiseuxAmbient).injective
  let f := fun i => MvPolynomial.map tAuxHom (equationWithAux F c alpha i)
  have hdeg (i : Fin (F.n+(F.n+1))) : (f i).totalDegree ≤ d i :=
    (totalDegree_map_le _ _).trans (hd i).2.2
  apply series_monomial_perturbation_coordinates_integral d (fun i => (hd i).1) f hdeg x
  intro i
  have hh := hx i
  rw [epsilon_perturbed_chart_eval F c alpha d hd] at hh
  exact hh

end APSCounting893.Main
end Component_32

section Component_33

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
open scoped RatFunc
namespace APSCounting893.Main

lemma epsilonLimitSet_finite (F : RawMap) (c alpha : Affine ℂ F.n)
    (d : Fin (F.n+(F.n+1)) → ℕ) (hd : HomogenizingDegrees F c alpha d) :
    (epsilonLimitSet F c alpha d).Finite := by
  classical
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  letI : CharZero PuiseuxAmbient := charZero_of_injective_ringHom (HahnSeries.C : ℂ →+* PuiseuxAmbient).injective
  let G : Fin (F.n+(F.n+1)) → MvPolynomial (Fin (F.n+(F.n+1)+1)) EpsilonAmbient :=
    fun i => MvPolynomial.map epsilonAuxHom (perturbedEquation F c alpha d i)
  let S := (epsilon_perturbed_affine_roots_finite F c alpha d hd).toFinset
  have hS : (S : Set _) = {x | ∀ i, MvPolynomial.eval (Fin.cons 1 x) (G i) = 0} := by
    dsimp only [S]
    rw [Set.Finite.coe_toFinset]
    ext x
    simp only [Set.mem_setOf_eq,G,MvPolynomial.eval_map]
  have hG (i : Fin (F.n+(F.n+1))) : (G i).IsHomogeneous (d i) :=
    epsilon_perturbed_homogeneous F c alpha d hd i
  have hnoInf (q : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) (hq : q 0 = 0)
      (hroot : ∀ i, MvPolynomial.eval q (G i) = 0) : q = 0 := by
    apply epsilon_perturbed_no_infinity F c alpha d hd q hq
    simpa only [G,MvPolynomial.eval_map] using hroot
  have hInt (x : Fin (F.n+(F.n+1)) → EpsilonAmbient) (hx : x ∈ S) :
      ∀ j, letI : Algebra (RatFunc PuiseuxAmbient) EpsilonAmbient :=
        (GenericSeries.rationalSeriesHom (K := PuiseuxAmbient)).toRingHom.toAlgebra
        IsIntegral (RatFunc PuiseuxAmbient) (x j) := by
    apply epsilon_perturbed_affine_coordinates_integral F c alpha d hd x
    have hh : x ∈ {x | ∀ i, MvPolynomial.eval₂ epsilonAuxHom (Fin.cons 1 x)
        (perturbedEquation F c alpha d i) = 0} := by simpa only [S,Set.Finite.mem_toFinset] using hx
    exact hh
  have hh := finite_projective_series_limits d G hG hnoInf S hS hInt
  simpa only [epsilonLimitSet,GenericSeries.IsPuiseuxOver,G,MvPolynomial.eval_map,epsilonAuxHom] using hh

end APSCounting893.Main
end Component_33

section Component_34
set_option autoImplicit false
open APSCounting893.Main
theorem solution
    (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F c alpha degrees) :
    (epsilonLimitSet F c alpha degrees).Finite := by
  exact epsilonLimitSet_finite F c alpha degrees hdegrees
end Component_34

open APSCounting893.Main

