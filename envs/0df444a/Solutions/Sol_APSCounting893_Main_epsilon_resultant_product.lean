-- Prove2me | solution 1 for APSCounting893.Main.epsilon_resultant_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:57:28.653885+00:00
-- url     : https://prove2.me/submissions/51cd2786-e2a8-4549-8044-f099dd30b0a7

import Definitions.Def_APSCounting893_Main_CoefficientLanguages
import Definitions.Def_APSCounting893_Main_Resultant
import Mathlib
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Theorems.Thm_APSCounting893_Main_normalized_resultant_foundation
import Theorems.Thm_DiazModulus_card_le_height_add_of_ringKrullDim_quotient_le
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
end Component_1

section Component_2

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
end Component_2

section Component_3

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
end Component_3

section Component_4

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
end Component_4

section Component_5

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
end Component_5

section Component_6

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
end Component_6

section Component_7

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
end Component_7

section Component_8

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
end Component_8

section Component_9

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
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma projective_series_limits_eq_image {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {n m : ℕ} (d : Fin m → ℕ)
    (G : Fin m → MvPolynomial (Fin (n+1)) (HahnSeries ℚ K))
    (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hnoInf : ∀ q : Fin (n+1) → HahnSeries ℚ K, q 0 = 0 →
      (∀ i, MvPolynomial.eval q (G i) = 0) → q = 0)
    (S : Finset (Fin n → HahnSeries ℚ K))
    (hS : (S : Set _) = {x | ∀ i, MvPolynomial.eval (Fin.cons 1 x) (G i) = 0})
    (Q : S → Fin (n+1) → HahnSeries ℚ K) (a : S → HahnSeries ℚ K)
    (ha : ∀ x, a x ≠ 0) (hQ : ∀ x, Q x = a x • Fin.cons 1 x.1)
    (hreg : ∀ x j, GenericSeries.IsPuiseuxOver (Q x j) ∧ 0 ≤ (Q x j).orderTop)
    (hunit : ∀ x, ∃ j, (Q x j).orderTop = 0) :
    {z : Fin (n+1) → K | ∃ q : Fin (n+1) → HahnSeries ℚ K,
      (∀ j, GenericSeries.IsPuiseuxOver (q j) ∧ 0 ≤ (q j).orderTop) ∧
      (∃ j, (q j).orderTop = 0) ∧ (∀ i, MvPolynomial.eval q (G i) = 0) ∧
      z = projectiveRepresentative (fun j => (q j).coeff 0)} = Set.range (fun x : S => projectiveRepresentative (fun j => (Q x j).coeff 0)) := by
  classical
  apply Set.Subset.antisymm
  ·
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
  · rintro z ⟨x,rfl⟩
    refine ⟨Q x,hreg x,hunit x,?_,rfl⟩
    intro i
    have hx : ∀ i, MvPolynomial.eval (Fin.cons 1 x.1) (G i) = 0 := by
      have hh : x.1 ∈ (S : Set _) := x.2
      rw [hS] at hh
      exact hh
    rw [hQ x]
    have he := homogeneous_eval₂_scaled (G i) (d i) (hG i)
      (RingHom.id (HahnSeries ℚ K)) (a x) (Fin.cons 1 x.1)
    simp only [MvPolynomial.eval₂_id,hx i,mul_zero] at he
    simpa only [MvPolynomial.eval₂_id,Pi.smul_def,smul_eq_mul] using he

end APSCounting893.Main
end Component_10

section Component_11

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
end Component_11

section Component_12

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
end Component_12

section Component_13
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
end Component_13

section Component_14
set_option autoImplicit false
namespace APSCounting893.Main
lemma universalResultant_specification {n : ℕ} (d : Fin (n+1) → ℕ)
    (hd : ∀ i, 0 < d i) : ResultantVNP.IsMultivariateResultant d (universalResultant d) :=
  Classical.epsilon_spec (normalized_resultant_foundation d hd).1
end APSCounting893.Main
end Component_14

section Component_15
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
end Component_15

section Component_16
set_option autoImplicit false
namespace APSCounting893.Main
noncomputable def diagonalCoefficient {K : Type} [CommRing K] {n : ℕ}
    (d : Fin n → ℕ) (v : ResultantVNP.CoeffVar d) : K :=
  if v.2.1 = Finsupp.single v.1 (d v.1) then 1 else 0
end APSCounting893.Main
end Component_16

section Component_17

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
end Component_17

section Component_18

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
end Component_18

section Component_19

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
end Component_19

section Component_20

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
end Component_20

section Component_21

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
end Component_21

section Component_22

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
end Component_22

section Component_23

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
end Component_23

section Component_24

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
end Component_24

section Component_25

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
end Component_25

section Component_26

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
end Component_26

section Component_27

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
end Component_27

section Component_28

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
end Component_28

section Component_29

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
end Component_29

section Component_30

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
end Component_30

section Component_31

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
end Component_31

section Component_32

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
end Component_32

section Component_33

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
end Component_33

section Component_34

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma exists_nonzero_root_of_fewer_homogeneous_forms {K : Type} [Field K] [IsAlgClosed K]
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (G : Fin n → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i)) :
    ∃ x : Fin (n+1) → K, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (G i) = 0 := by
  classical
  by_contra h
  push Not at h
  let I := Ideal.span (Set.range G)
  let P : Ideal (MvPolynomial (Fin (n+1)) K) := RingHom.ker (MvPolynomial.eval 0)
  have hsurj : Function.Surjective (MvPolynomial.eval (0 : Fin (n+1) → K)) := by
    intro c
    exact ⟨MvPolynomial.C c,MvPolynomial.eval_C c⟩
  haveI : P.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  haveI : P.IsPrime := inferInstance
  have hz : MvPolynomial.zeroLocus K I = {0} := by
    rw [MvPolynomial.zeroLocus_span]
    ext x
    simp only [Set.mem_setOf_eq,Set.forall_mem_range,MvPolynomial.aeval_eq_eval,Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hx0
      obtain ⟨i,hi⟩ := h x hx0
      exact hi (hx i)
    · rintro rfl i
      rw [MvPolynomial.eval_zero]
      change (G i).coeff 0 = 0
      exact (hG i).coeff_eq_zero (by simpa using (Nat.ne_of_gt (hd i)).symm)
  have hrad : I.radical = P := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K),hz]
    ext q
    simp [MvPolynomial.mem_vanishingIdeal_iff,P,RingHom.mem_ker,MvPolynomial.aeval_eq_eval]
  have hm : P ∈ I.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes,hrad,Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  let s := Finset.univ.image G
  have hspan : I = Ideal.span (s : Set (MvPolynomial (Fin (n+1)) K)) := by
    change Ideal.span (Set.range G) = Ideal.span (s : Set _)
    congr 1
    ext q
    simp [s]
  rw [hspan] at hm
  have hheight := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hm
  have hcard : s.card ≤ n := (Finset.card_image_le).trans (by simp)
  have hpheight : P.height ≤ (n : ℕ∞) := hheight.trans (by exact_mod_cast hcard)
  letI : Field (MvPolynomial (Fin (n+1)) K ⧸ P) := Ideal.Quotient.field P
  have hdim : ringKrullDim (MvPolynomial (Fin (n+1)) K ⧸ P) ≤ 0 := by
    rw [ringKrullDim_eq_zero_of_field]
  have hh := DiazModulus.card_le_height_add_of_ringKrullDim_quotient_le P inferInstance 0 hdim
  simp only [Nat.card_eq_fintype_card,Fintype.card_fin,Nat.cast_zero,add_zero] at hh
  have hbad : n+1 ≤ n := by exact_mod_cast hh.trans hpheight
  omega

end APSCounting893.Main
end Component_34

section Component_35

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
open scoped RatFunc
namespace APSCounting893.Main

lemma epsilon_limit_data (F : RawMap) (c alpha : Affine ℂ F.n)
    (d : Fin (F.n+(F.n+1)) → ℕ) (hd : HomogenizingDegrees F c alpha d) :
    ∃ S : Finset (Fin (F.n+(F.n+1)) → EpsilonAmbient), S.Nonempty ∧
      (S : Set _) = {x | ∀ i, MvPolynomial.eval₂ epsilonAuxHom (Fin.cons 1 x) (perturbedEquation F c alpha d i) = 0} ∧
      ∃ (Q : S → Fin (F.n+(F.n+1)+1) → EpsilonAmbient) (a : S → EpsilonAmbient),
        (∀ x, a x ≠ 0) ∧ (∀ x, Q x = a x • Fin.cons 1 x.1) ∧
        (∀ x j, GenericSeries.IsPuiseuxOver (Q x j) ∧ 0 ≤ (Q x j).orderTop) ∧
        (∀ x, ∃ j, (Q x j).orderTop = 0) ∧
        epsilonLimitSet F c alpha d = Set.range (fun x : S => projectiveRepresentative (fun j => (Q x j).coeff 0)) := by
  classical
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  letI : CharZero PuiseuxAmbient := charZero_of_injective_ringHom (HahnSeries.C : ℂ →+* PuiseuxAmbient).injective
  letI : IsAlgClosed EpsilonAmbient := HahnSeries.isAlgClosed_rat
  letI : Algebra (RatFunc PuiseuxAmbient) EpsilonAmbient :=
    (GenericSeries.rationalSeriesHom (K := PuiseuxAmbient)).toRingHom.toAlgebra
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
  have hInt (x : S) (j : Fin (F.n+(F.n+1))) : IsIntegral (RatFunc PuiseuxAmbient) (x.1 j) := by
    apply epsilon_perturbed_affine_coordinates_integral F c alpha d hd x.1 _ j
    have hh : x.1 ∈ (S : Set _) := x.2
    rw [hS] at hh
    simpa only [G,MvPolynomial.eval_map,Set.mem_setOf_eq] using hh
  have hne : S.Nonempty := by
    obtain ⟨q,hq,hroot⟩ := exists_nonzero_root_of_fewer_homogeneous_forms d (fun i => (hd i).1) G hG
    have hq0 : q 0 ≠ 0 := fun h => hq (hnoInf q h hroot)
    let x := fun j : Fin (F.n+(F.n+1)) => (q 0)⁻¹ * q j.succ
    have hpoint : (Fin.cons 1 x : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) = (q 0)⁻¹ • q := by
      funext j
      refine Fin.cases (by simp [hq0]) (fun j => rfl) j
    refine ⟨x,?_⟩
    change x ∈ (S : Set _)
    rw [hS]
    intro i
    rw [hpoint]
    change MvPolynomial.eval₂ (RingHom.id EpsilonAmbient) (fun j => (q 0)⁻¹ * q j) (G i) = 0
    rw [homogeneous_eval₂_scaled _ _ (hG i),MvPolynomial.eval₂_id,hroot i,mul_zero]
  refine ⟨S,hne,?_,?_⟩
  · simpa only [G,MvPolynomial.eval_map] using hS
  · have hex (x : S) : ∃ (q : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) (a : EpsilonAmbient),
        a ≠ 0 ∧ q = a • Fin.cons 1 x.1 ∧
        (∀ j, GenericSeries.IsPuiseuxOver (q j) ∧ 0 ≤ (q j).orderTop) ∧
        ∃ j, (q j).orderTop = 0 := by
      apply exists_regular_puiseux_projective_rescaling
      · intro hh
        have hh0 := congrFun hh 0
        simpa using hh0
      · intro j
        refine Fin.cases isIntegral_one (fun j => hInt x j) j
    choose Q a ha hQ hreg hunit using hex
    refine ⟨Q,a,ha,hQ,hreg,hunit,?_⟩
    have hh := projective_series_limits_eq_image d G hG hnoInf S hS Q a ha hQ hreg hunit
    simpa only [epsilonLimitSet,GenericSeries.IsPuiseuxOver,G,MvPolynomial.eval_map,epsilonAuxHom] using hh

end APSCounting893.Main
end Component_35

section Component_36

set_option autoImplicit false
open MvPolynomial
namespace APSCounting893.Main

lemma coefficientIn_zero {K : Type} [CommRing K] {n : ℕ} (v : Fin n) (k : ℕ) :
    coefficientIn v k (0 : MvPolynomial (Fin n) K) = 0 := by
  simp [coefficientIn]

lemma coefficientIn_monomial {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (e : Fin n →₀ ℕ) (a : K) :
    coefficientIn v k (monomial e a) =
      if e v = k then monomial (e - Finsupp.single v k) a else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, coefficientIn_zero]
  · simp [coefficientIn, support_monomial, ha]

lemma coefficientIn_add {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p q : MvPolynomial (Fin n) K) :
    coefficientIn v k (p + q) = coefficientIn v k p + coefficientIn v k q := by
  classical
  change Finsupp.sum (AddMonoidAlgebra.coeff (p + q))
    (fun e a => if e v = k then monomial (e - Finsupp.single v k) a else 0) =
    Finsupp.sum (AddMonoidAlgebra.coeff p)
      (fun e a => if e v = k then monomial (e - Finsupp.single v k) a else 0) +
    Finsupp.sum (AddMonoidAlgebra.coeff q)
      (fun e a => if e v = k then monomial (e - Finsupp.single v k) a else 0)
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index
  · intro e; split_ifs <;> simp
  · intro e a b; split_ifs <;> simp

lemma coefficientIn_sum {K : Type} [CommRing K] {n : ℕ} {ι : Type}
    (v : Fin n) (k : ℕ) (s : Finset ι) (p : ι → MvPolynomial (Fin n) K) :
    coefficientIn v k (∑ i ∈ s, p i) = ∑ i ∈ s, coefficientIn v k (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coefficientIn_zero]
  | @insert i s hi ih => simp [hi, coefficientIn_add, ih]

lemma coefficientIn_coeff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) (e : Fin n →₀ ℕ) :
    (coefficientIn v k p).coeff e =
      if e v = 0 then p.coeff (e + Finsupp.single v k) else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [coefficientIn_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp
  | monomial d a =>
    rw [coefficientIn_monomial]
    by_cases hd : d v = k
    · rw [if_pos hd]
      by_cases he : e v = 0
      · rw [if_pos he, coeff_monomial, coeff_monomial]
        have hle : Finsupp.single v k ≤ d := Finsupp.single_le_iff.mpr hd.ge
        have hi : d - Finsupp.single v k = e ↔ d = e + Finsupp.single v k := by
          constructor
          · intro h; rw [← h, tsub_add_cancel_of_le hle]
          · intro h; simp [h]
        simp only [hi]
      · rw [if_neg he, coeff_monomial]
        have hi : d - Finsupp.single v k ≠ e := by
          intro h
          have := congrArg (fun f : Fin n →₀ ℕ => f v) h
          simp [Finsupp.tsub_apply, hd] at this
          exact he this.symm
        simp [hi]
    · rw [if_neg hd, coeff_zero]
      split_ifs with he
      · rw [coeff_monomial]
        have hi : d ≠ e + Finsupp.single v k := by
          intro h; apply hd
          simpa [he] using congrArg (fun f : Fin n →₀ ℕ => f v) h
        simp [hi]
      · rfl

lemma coefficientIn_ne_zero_iff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v k p ≠ 0 ↔ ∃ e ∈ p.support, e v = k := by
  classical
  constructor
  · intro h
    obtain ⟨e, he⟩ := exists_coeff_ne_zero h
    rw [coefficientIn_coeff] at he
    split_ifs at he with hv
    · refine ⟨e + Finsupp.single v k, mem_support_iff.mpr he, ?_⟩
      simp [hv]
    · exact (he rfl).elim
  · rintro ⟨e, he, hv⟩ h
    have ha : (e - Finsupp.single v k) v = 0 := by simp [Finsupp.tsub_apply, hv]
    have hb : e - Finsupp.single v k + Finsupp.single v k = e :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hv.ge)
    have := congrArg (coeff (e - Finsupp.single v k)) h
    simpa [coefficientIn_coeff, ha, hb, mem_support_iff.mp he] using this

lemma trailingCoefficient_ne_zero {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    trailingCoefficient v p ≠ 0 := by
  classical
  have hs : p.support.Nonempty := support_nonempty.mpr hp
  rw [trailingCoefficient, dif_pos hs, coefficientIn_ne_zero_iff]
  exact Finset.mem_image.mp (Finset.min'_mem _ (hs.image _))

lemma coefficientIn_totalDegree_le {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    (coefficientIn v k p).totalDegree ≤ p.totalDegree := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro e he
  have hc := mem_support_iff.mp he
  rw [coefficientIn_coeff] at hc
  split_ifs at hc with hv
  · have hd := le_totalDegree (mem_support_iff.mpr hc)
    have hadd : (e + Finsupp.single v k).sum (fun _ a => a) =
        e.sum (fun _ a => a) + k := by
      simp [Finsupp.sum_add_index']
    rw [hadd] at hd
    exact (Nat.le_add_right _ _).trans hd
  · exact (hc rfl).elim

lemma trailingCoefficient_totalDegree_le {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    (trailingCoefficient v p).totalDegree ≤ p.totalDegree := by
  classical
  unfold trailingCoefficient
  split_ifs
  · exact coefficientIn_totalDegree_le ..
  · simp

lemma trailingCoefficient_eq_of_min {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (k : ℕ)
    (hk : coefficientIn v k p ≠ 0)
    (hmin : ∀ j < k, coefficientIn v j p = 0) :
    trailingCoefficient v p = coefficientIn v k p := by
  classical
  obtain ⟨e, he, hv⟩ := (coefficientIn_ne_zero_iff v k p).mp hk
  have hs : p.support.Nonempty := ⟨e, he⟩
  rw [trailingCoefficient, dif_pos hs]
  congr 1
  apply le_antisymm
  · apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨e, he, hv⟩
  · by_contra h
    have hlt := Nat.lt_of_not_ge h
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp (Finset.min'_mem _ (hs.image (fun e => e v)))
    have hz := hmin _ hlt
    exact ((coefficientIn_ne_zero_iff v _ p).mpr ⟨d, hd, heq⟩) hz

lemma coefficientIn_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v k (MvPolynomial.map f p) =
      MvPolynomial.map f (coefficientIn v k p) := by
  classical
  ext e
  simp only [coefficientIn_coeff, coeff_map]
  split_ifs <;> simp

lemma trailingCoefficient_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (v : Fin n) (p : MvPolynomial (Fin n) K)
    (hp : MvPolynomial.map f (trailingCoefficient v p) ≠ 0) :
    trailingCoefficient v (MvPolynomial.map f p) =
      MvPolynomial.map f (trailingCoefficient v p) := by
  classical
  have hs : p.support.Nonempty := by
    by_contra h
    simp [trailingCoefficient, h] at hp
  let k := (p.support.image (fun e => e v)).min' (hs.image _)
  have htc : trailingCoefficient v p = coefficientIn v k p := by
    simp [trailingCoefficient, hs, k]
  rw [htc] at hp ⊢
  rw [← coefficientIn_map] at hp ⊢
  apply trailingCoefficient_eq_of_min v _ k hp
  intro j hj
  rw [coefficientIn_map]
  have hz : coefficientIn v j p = 0 := by
    by_contra h
    obtain ⟨e, he, hv⟩ := (coefficientIn_ne_zero_iff v j p).mp h
    have hkj : k ≤ j := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e, he, hv⟩)
    omega
  simp [hz]

lemma specializeParameters_monomial {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K) (e : Fin (s + (k + 1)) →₀ ℕ) (a : ℚ) :
    specializeParameters theta (monomial e a) =
      monomial (Finsupp.equivFunOnFinite.symm (fun i : Fin (k + 1) => e (i.natAdd s)))
        (algebraMap ℚ K a * ∏ i : Fin s, theta i ^ e (i.castAdd (k + 1))) := by
  classical
  simp only [specializeParameters, eval₂Hom_monomial, RingHom.coe_comp, Function.comp_apply,
    Finsupp.prod_pow]
  rw [Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [monomial_eq]
  simp only [Finsupp.prod_pow, Finsupp.equivFunOnFinite_symm_apply_apply]
  simp [map_mul, map_prod, map_pow, mul_assoc]

lemma specializeParameters_coefficientIn {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K) (v : Fin (k + 1)) (j : ℕ)
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ) :
    specializeParameters theta (coefficientIn (v.natAdd s) j p) =
      coefficientIn v j (specializeParameters theta p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [coefficientIn_add, specializeParameters, map_add] at hp hq ⊢
    rw [hp, hq]
  | monomial e a =>
    rw [coefficientIn_monomial, specializeParameters_monomial, coefficientIn_monomial]
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    split_ifs with he
    · rw [specializeParameters_monomial]
      have haux : Finsupp.equivFunOnFinite.symm
          (fun i : Fin (k + 1) => (e - Finsupp.single (v.natAdd s) j) (i.natAdd s)) =
          Finsupp.equivFunOnFinite.symm (fun i : Fin (k + 1) => e (i.natAdd s)) -
            Finsupp.single v j := by
        ext i
        simp [Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]
      rw [haux]
      congr 2
      apply Finset.prod_congr rfl
      intro i _
      have hn : i.castAdd (k + 1) ≠ v.natAdd s := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [Finsupp.tsub_apply, Finsupp.single_apply, hn, Ne.symm hn]
    · simp [specializeParameters]

lemma totalDegree_eval₂_linear {K L : Type} [CommRing K] [CommRing L] {n m : ℕ}
    (f : K →+* L) (g : Fin n → MvPolynomial (Fin m) L)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial (Fin n) K) :
    (eval₂Hom (MvPolynomial.C.comp f) g p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.coe_comp, Function.comp_apply, totalDegree_C, zero_add]
  rw [Finsupp.prod_pow]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))))
  simpa [Finsupp.sum_fintype] using (le_totalDegree he)

lemma specializeParameters_trailingCoefficient {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K) (v : Fin (k + 1))
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ)
    (hp : specializeParameters theta (trailingCoefficient (v.natAdd s) p) ≠ 0) :
    specializeParameters theta (trailingCoefficient (v.natAdd s) p) =
      trailingCoefficient v (specializeParameters theta p) := by
  classical
  have hs : p.support.Nonempty := by
    by_contra h
    simp [trailingCoefficient, h, specializeParameters] at hp
  let j := (p.support.image (fun e => e (v.natAdd s))).min' (hs.image _)
  have htc : trailingCoefficient (v.natAdd s) p = coefficientIn (v.natAdd s) j p := by
    simp [trailingCoefficient, hs, j]
  rw [htc, specializeParameters_coefficientIn] at hp ⊢
  symm
  apply trailingCoefficient_eq_of_min v _ j hp
  intro i hi
  rw [← specializeParameters_coefficientIn]
  have hz : coefficientIn (v.natAdd s) i p = 0 := by
    by_contra h
    obtain ⟨e, he, hv⟩ := (coefficientIn_ne_zero_iff (v.natAdd s) i p).mp h
    have hji : j ≤ i := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e, he, hv⟩)
    omega
  simp [hz, specializeParameters]

lemma specialization_nonzero_witness {s k : ℕ}
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ) (hp : p ≠ 0) :
    ∃ A : MvPolynomial (Fin s) ℚ,
      A ≠ 0 ∧ A.totalDegree ≤ p.totalDegree ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K),
        eval₂ (algebraMap ℚ K) theta A ≠ 0 → specializeParameters theta p ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : Fin (s + (k + 1)) → ℚ, eval x p ≠ 0 := by
    by_contra h
    push_neg at h
    apply hp
    apply MvPolynomial.funext
    intro x
    simpa using h x
  let z : Fin (k + 1) → ℚ := fun i => x (i.natAdd s)
  let freeze : MvPolynomial (Fin (s + (k + 1))) ℚ →+* MvPolynomial (Fin s) ℚ :=
    eval₂Hom C (Fin.addCases X (fun i => C (z i)))
  have commute (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K) :
      (eval₂Hom (algebraMap ℚ K) theta).comp freeze =
        (eval₂Hom (RingHom.id K) (fun i => algebraMap ℚ K (z i))).comp
          (eval₂Hom (C.comp (algebraMap ℚ K)) (Fin.addCases (fun i => C (theta i)) X)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [freeze]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [freeze]
      · intro j; simp [freeze]
  refine ⟨freeze p, ?_, ?_, ?_⟩
  · intro h
    have hcomp : (eval₂Hom (RingHom.id ℚ) (fun i => x (i.castAdd (k + 1)))).comp freeze =
        eval₂Hom (RingHom.id ℚ) x := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [freeze]
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [freeze]
        · intro j; simp [freeze, z]
    apply hx
    change (eval₂Hom (RingHom.id ℚ) x) p = 0
    rw [← hcomp, RingHom.comp_apply, h, map_zero]
  · apply totalDegree_eval₂_linear (RingHom.id ℚ)
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp
    · intro j; simp
  · intro K _ _ theta hA hz
    apply hA
    change (eval₂Hom (algebraMap ℚ K) theta) (freeze p) = 0
    rw [← RingHom.comp_apply, commute K theta, RingHom.comp_apply]
    change (eval₂Hom (RingHom.id K) (fun i => algebraMap ℚ K (z i)))
      (specializeParameters theta p) = 0
    rw [hz, map_zero]

lemma nestedTrailing_specialization_aux {s k : ℕ}
    (order : List (Fin (k + 1)))
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ) (hp : p ≠ 0) :
    ∃ A : Fin order.length → MvPolynomial (Fin s) ℚ,
      (∀ i, A i ≠ 0 ∧ (A i).totalDegree ≤ p.totalDegree) ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K),
        (∀ i, eval₂ (algebraMap ℚ K) theta (A i) ≠ 0) →
        specializeParameters theta (nestedTrailing (order.map (Fin.natAdd s)) p) =
          nestedTrailing order (specializeParameters theta p) := by
  classical
  induction order generalizing p with
  | nil =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · intro K _ _ theta h
      rfl
  | cons v order ih =>
    let q := trailingCoefficient (v.natAdd s) p
    have hq : q ≠ 0 := trailingCoefficient_ne_zero _ _ hp
    obtain ⟨a, ha, had, haw⟩ := specialization_nonzero_witness q hq
    obtain ⟨B, hB, hBw⟩ := ih q hq
    refine ⟨Fin.cons a B, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using And.intro ha (had.trans (trailingCoefficient_totalDegree_le _ _))
      · simpa using And.intro (hB j).1
          ((hB j).2.trans (trailingCoefficient_totalDegree_le _ _))
    · intro K _ _ theta hA
      have hqa : specializeParameters theta q ≠ 0 := haw K theta (by simpa using hA 0)
      have htc := specializeParameters_trailingCoefficient theta v p hqa
      have htail : ∀ i, eval₂ (algebraMap ℚ K) theta (B i) ≠ 0 := by
        intro i; simpa using hA i.succ
      have hrec := hBw K theta htail
      change specializeParameters theta (nestedTrailing (order.map (Fin.natAdd s)) q) =
        nestedTrailing order (trailingCoefficient v (specializeParameters theta p))
      rw [← htc]
      exact hrec

end APSCounting893.Main
end Component_36

section Component_37

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def splitVariable {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) : Polynomial (MvPolynomial (Fin n) K) :=
  ∑ e ∈ p.support, Polynomial.monomial (e v) (MvPolynomial.monomial (e.erase v) (p.coeff e))

lemma splitVariable_zero {K : Type} [CommRing K] {n : ℕ} (v : Fin n) :
    splitVariable v (0 : MvPolynomial (Fin n) K) = 0 := by simp [splitVariable]

lemma splitVariable_monomial {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (e : Fin n →₀ ℕ) (a : K) :
    splitVariable v (monomial e a) = Polynomial.monomial (e v) (monomial (e.erase v) a) := by
  classical
  by_cases ha : a = 0
  · simp [ha, splitVariable_zero]
  · simp [splitVariable, support_monomial, ha]

lemma splitVariable_add {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p q : MvPolynomial (Fin n) K) :
    splitVariable v (p + q) = splitVariable v p + splitVariable v q := by
  classical
  change Finsupp.sum (AddMonoidAlgebra.coeff (p + q))
    (fun e a => Polynomial.monomial (e v) (monomial (e.erase v) a)) =
      Finsupp.sum (AddMonoidAlgebra.coeff p) (fun e a => Polynomial.monomial (e v) (monomial (e.erase v) a)) +
      Finsupp.sum (AddMonoidAlgebra.coeff q) (fun e a => Polynomial.monomial (e v) (monomial (e.erase v) a))
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index
  · intro e; simp
  · intro e a b; simp

lemma splitVariable_mul {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p q : MvPolynomial (Fin n) K) :
    splitVariable v (p * q) = splitVariable v p * splitVariable v q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [add_mul, splitVariable_add, hp, hr]
  | monomial e a =>
    induction q using MvPolynomial.induction_on' with
    | add q r hq hr => simp only [mul_add, splitVariable_add, hq, hr]
    | monomial f b =>
      rw [monomial_mul, splitVariable_monomial, splitVariable_monomial, splitVariable_monomial,
        Polynomial.monomial_mul_monomial, monomial_mul]
      simp only [Finsupp.add_apply, Finsupp.erase_add]

lemma splitVariable_coeff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (k : ℕ) :
    (splitVariable v p).coeff k = coefficientIn v k p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [splitVariable_add, Polynomial.coeff_add, hp, hq, coefficientIn_add]
  | monomial e a =>
    rw [splitVariable_monomial, Polynomial.coeff_monomial, coefficientIn_monomial]
    have he : e.erase v = e - Finsupp.single v (e v) := by
      ext i
      by_cases hi : i = v
      · subst i; simp
      · simp [hi]
    split_ifs with h
    · rw [h] at he
      rw [he]
    · rfl

lemma splitVariable_eval {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    Polynomial.eval (X v) (splitVariable v p) = p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [splitVariable_add, Polynomial.eval_add, hp, hq]
  | monomial e a =>
    rw [splitVariable_monomial, Polynomial.eval_monomial]
    rw [X_pow_eq_monomial, monomial_mul, mul_one]
    rw [Finsupp.erase_add_single]

lemma splitVariable_ne_zero {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) : splitVariable v p ≠ 0 := by
  intro h
  have hh := splitVariable_eval v p
  rw [h, Polynomial.eval_zero] at hh
  exact hp hh.symm

end APSCounting893.Main
end Component_37

section Component_38

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def hahnCoefficientMap {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) : HahnSeries ℚ R →+* HahnSeries ℚ S where
  toFun x := x.map f
  map_zero' := by ext q; simp
  map_one' := by ext q; simp only [HahnSeries.map_coeff, HahnSeries.coeff_one]; split_ifs <;> simp
  map_add' x y := by ext q; simp
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom

lemma hahnCoefficientMap_coeff {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (x : HahnSeries ℚ R) (q : ℚ) :
    (hahnCoefficientMap f x).coeff q = f (x.coeff q) := rfl

lemma hahnCoefficientMap_single {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (q : ℚ) (r : R) :
    hahnCoefficientMap f (HahnSeries.single q r) = HahnSeries.single q (f r) := by
  ext t
  simp only [hahnCoefficientMap_coeff, HahnSeries.coeff_single]
  split_ifs <;> simp

lemma hahnCoefficientMap_regular {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (x : HahnSeries ℚ R) (hx : 0 ≤ x.orderTop) :
    0 ≤ (hahnCoefficientMap f x).orderTop := by
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro q hq
  rw [hahnCoefficientMap_coeff, HahnSeries.coeff_eq_zero_of_lt_orderTop (hq.trans_le hx), map_zero]

noncomputable def polynomialToHahn {K : Type} [CommRing K] :
    Polynomial (HahnSeries ℚ K) →+* HahnSeries ℚ (Polynomial K) :=
  Polynomial.eval₂RingHom (hahnCoefficientMap Polynomial.C) (HahnSeries.C Polynomial.X)

lemma polynomialToHahn_C {K : Type} [CommRing K] (x : HahnSeries ℚ K) :
    polynomialToHahn (Polynomial.C x) = hahnCoefficientMap Polynomial.C x := by
  simp [polynomialToHahn]

lemma polynomialToHahn_X {K : Type} [CommRing K] :
    polynomialToHahn (Polynomial.X : Polynomial (HahnSeries ℚ K)) = HahnSeries.C Polynomial.X := by
  simp [polynomialToHahn]

lemma polynomialToHahn_linear {K : Type} [CommRing K] (x : HahnSeries ℚ K) :
    polynomialToHahn (Polynomial.X - Polynomial.C x) =
      HahnSeries.C Polynomial.X - hahnCoefficientMap Polynomial.C x := by
  rw [map_sub, polynomialToHahn_X, polynomialToHahn_C]

lemma hahn_coeff_zero_mul_regular {R : Type} [CommRing R] [IsDomain R]
    (x y : HahnSeries ℚ R) (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    (x*y).coeff 0 = x.coeff 0 * y.coeff 0 := by
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

end APSCounting893.Main
end Component_38

section Component_39

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma hahn_regular_mul {R : Type} [CommRing R] [IsDomain R]
    {x y : HahnSeries ℚ R} (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    0 ≤ (x*y).orderTop := by
  rw [HahnSeries.orderTop_mul]
  exact add_nonneg hx hy

lemma hahn_regular_pow {R : Type} [CommRing R] [IsDomain R]
    {x : HahnSeries ℚ R} (hx : 0 ≤ x.orderTop) (n : ℕ) : 0 ≤ (x^n).orderTop := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact hahn_regular_mul ih hx

lemma hahn_coeff_zero_pow_regular {R : Type} [CommRing R] [IsDomain R]
    {x : HahnSeries ℚ R} (hx : 0 ≤ x.orderTop) (n : ℕ) :
    (x^n).coeff 0 = x.coeff 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, hahn_coeff_zero_mul_regular _ _ (hahn_regular_pow hx n) hx, ih, pow_succ]

lemma hahn_regular_prod {R ι : Type} [CommRing R] [IsDomain R]
    (s : Finset ι) (x : ι → HahnSeries ℚ R) (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    0 ≤ (∏ i ∈ s, x i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hahn_regular_mul (hx a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)))

lemma hahn_coeff_zero_prod_regular {R ι : Type} [CommRing R] [IsDomain R]
    (s : Finset ι) (x : ι → HahnSeries ℚ R) (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    (∏ i ∈ s, x i).coeff 0 = ∏ i ∈ s, (x i).coeff 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      hahn_coeff_zero_mul_regular _ _ (hx a (Finset.mem_insert_self _ _))
        (hahn_regular_prod s x (fun i hi => hx i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))]

lemma polynomialToHahn_linear_regular {K : Type} [Field K]
    (x : HahnSeries ℚ K) (hx : 0 ≤ x.orderTop) :
    0 ≤ (polynomialToHahn (Polynomial.X - Polynomial.C x)).orderTop := by
  rw [polynomialToHahn_linear]
  apply le_trans _ HahnSeries.min_orderTop_le_orderTop_sub
  apply le_min
  · rw [HahnSeries.zero_le_orderTop_iff, HahnSeries.order_C]
  · exact hahnCoefficientMap_regular Polynomial.C x hx

lemma polynomialToHahn_linear_coeff_zero {K : Type} [Field K]
    (x : HahnSeries ℚ K) :
    (polynomialToHahn (Polynomial.X - Polynomial.C x)).coeff 0 =
      Polynomial.X - Polynomial.C (x.coeff 0) := by
  rw [polynomialToHahn_linear, HahnSeries.coeff_sub, hahnCoefficientMap_coeff]
  simp [HahnSeries.C_apply]

lemma polynomialToHahn_product_linear_coeff_zero {K ι : Type} [Field K]
    (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    (polynomialToHahn (∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i)).coeff 0 =
      ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  rw [map_prod]
  simp only [map_pow]
  rw [hahn_coeff_zero_prod_regular s _ (fun i hi =>
    hahn_regular_pow (polynomialToHahn_linear_regular _ (hx i hi)) _)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hahn_coeff_zero_pow_regular (polynomialToHahn_linear_regular _ (hx i hi)),
    polynomialToHahn_linear_coeff_zero]

end APSCounting893.Main
end Component_39

section Component_40

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma polynomial_hahn_orderTop {R : Type} [CommRing R]
    (p : Polynomial R) (hp : p ≠ 0) :
    (algebraMap (Polynomial R) (HahnSeries ℚ R) p).orderTop = (p.natTrailingDegree : ℚ) := by
  let f := HahnSeries.toPowerSeries.symm (p : PowerSeries R)
  have hnat : f.orderTop = (p.natTrailingDegree : WithTop ℕ) := by
    apply HahnSeries.orderTop_eq_of_le
    · change PowerSeries.coeff p.natTrailingDegree (p : PowerSeries R) ≠ 0
      simpa using (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp)
    · intro j hj
      apply Polynomial.natTrailingDegree_le_of_ne_zero
      change PowerSeries.coeff j (p : PowerSeries R) ≠ 0 at hj
      simpa using hj
  change (HahnSeries.embDomain (Nat.castOrderEmbedding (α := ℚ)) f).orderTop = _
  rw [HahnSeries.orderTop_embDomain, hnat]
  rfl

lemma polynomial_hahn_coeff_nat {R : Type} [CommRing R] (p : Polynomial R) (n : ℕ) :
    (algebraMap (Polynomial R) (HahnSeries ℚ R) p).coeff (n : ℚ) = p.coeff n := by
  rw [Polynomial.algebraMap_hahnSeries_apply, HahnSeries.ofPowerSeries_apply_coeff]
  simp

lemma polynomial_hahn_leadingCoeff {R : Type} [CommRing R] (p : Polynomial R) :
    (algebraMap (Polynomial R) (HahnSeries ℚ R) p).leadingCoeff = p.trailingCoeff := by
  by_cases hp : p = 0
  · simp [hp, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_zero]
  have hh := polynomial_hahn_orderTop p hp
  have ho : (algebraMap (Polynomial R) (HahnSeries ℚ R) p).order = (p.natTrailingDegree : ℚ) := by
    have hp' : algebraMap (Polynomial R) (HahnSeries ℚ R) p ≠ 0 := by
      intro hz
      apply hp
      exact (Polynomial.algebraMap_hahnSeries_injective (Γ := ℚ) (R := R)) (by simpa only [map_zero] using hz)
    rw [HahnSeries.orderTop_of_ne_zero hp'] at hh
    rw [HahnSeries.order_of_ne hp']
    exact WithTop.coe_inj.mp hh
  rw [HahnSeries.leadingCoeff_eq, ho, polynomial_hahn_coeff_nat]
  rfl

end APSCounting893.Main
end Component_40

section Component_41

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma hahnCoefficientMap_order {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (x : HahnSeries ℚ R) :
    (hahnCoefficientMap f x).order = x.order := by
  by_cases hx : x = 0
  · simp [hx, map_zero]
  have hxn : x.coeff x.order ≠ 0 := by
    simpa only [← HahnSeries.leadingCoeff_eq] using (HahnSeries.leadingCoeff_ne_zero.mpr hx)
  have hyn : (hahnCoefficientMap f x).coeff x.order ≠ 0 := by
    rw [hahnCoefficientMap_coeff]
    exact fun h => hxn (hf (h.trans f.map_zero.symm))
  have hy : hahnCoefficientMap f x ≠ 0 := fun h => hyn (by simp [h])
  have ho : (hahnCoefficientMap f x).orderTop = (x.order : WithTop ℚ) := by
    apply HahnSeries.orderTop_eq_of_le hyn
    intro q hq
    apply HahnSeries.order_le_of_coeff_ne_zero
    exact fun h => hq (by rw [hahnCoefficientMap_coeff, h, map_zero])
  rw [HahnSeries.orderTop_of_ne_zero hy] at ho
  rw [HahnSeries.order_of_ne hy]
  exact WithTop.coe_inj.mp ho

lemma hahnCoefficientMap_leadingCoeff {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (x : HahnSeries ℚ R) :
    (hahnCoefficientMap f x).leadingCoeff = f x.leadingCoeff := by
  rw [HahnSeries.leadingCoeff_eq, hahnCoefficientMap_order f hf,
    hahnCoefficientMap_coeff, HahnSeries.leadingCoeff_eq]

lemma polynomialToHahn_product_linear_leadingCoeff {K ι : Type} [Field K]
    (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    (polynomialToHahn (∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i)).leadingCoeff =
      ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  let p := ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i
  have hreg : 0 ≤ (polynomialToHahn p).orderTop := by
    dsimp only [p]
    rw [map_prod]
    simp only [map_pow]
    exact hahn_regular_prod s _ (fun i hi => hahn_regular_pow (polynomialToHahn_linear_regular _ (hx i hi)) _)
  have hres := polynomialToHahn_product_linear_coeff_zero s x mu hx
  have hn : (polynomialToHahn p).coeff 0 ≠ 0 := by
    rw [hres]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (Polynomial.monic_X_sub_C _).ne_zero
  have ho : (polynomialToHahn p).order = 0 := by
    exact le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hn)
      (HahnSeries.zero_le_orderTop_iff.mp hreg)
  rw [HahnSeries.leadingCoeff_eq, ho]
  exact hres

lemma polynomialToHahn_scalar_product_leadingCoeff {K ι : Type} [Field K]
    (c : HahnSeries ℚ K) (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    (polynomialToHahn (Polynomial.C c * ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i)).leadingCoeff =
      Polynomial.C c.leadingCoeff * ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  rw [map_mul, polynomialToHahn_C, HahnSeries.leadingCoeff_mul,
    hahnCoefficientMap_leadingCoeff Polynomial.C Polynomial.C_injective,
    polynomialToHahn_product_linear_leadingCoeff s x mu hx]

end APSCounting893.Main
end Component_41

section Component_42

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def splitBivariate {K : Type} [CommRing K] :
    MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (fun j => if j = 0 then Polynomial.X else Polynomial.C Polynomial.X)

noncomputable def bivariateOther {K : Type} [CommRing K] :
    MvPolynomial (Fin 2) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = 0 then 0 else Polynomial.X)

lemma splitBivariate_monomial {K : Type} [CommRing K] (e : Fin 2 →₀ ℕ) (a : K) :
    splitBivariate (monomial e a) = Polynomial.monomial (e 0) (Polynomial.monomial (e 1) a) := by
  change MvPolynomial.eval₂ _ _ (monomial e a) = _
  rw [MvPolynomial.eval₂_monomial, e.prod_fintype _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp only [RingHom.comp_apply, ite_true, ite_false, one_ne_zero]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
    map_mul, map_pow]
  ring

lemma bivariateOther_monomial {K : Type} [CommRing K] (e : Fin 2 →₀ ℕ) (a : K) :
    bivariateOther (monomial e a) = if e 0 = 0 then Polynomial.monomial (e 1) a else 0 := by
  change MvPolynomial.eval₂ _ _ (monomial e a) = _
  rw [MvPolynomial.eval₂_monomial, e.prod_fintype _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp only [ite_true, ite_false, one_ne_zero]
  by_cases h : e 0 = 0
  · simp only [h, pow_zero, one_mul, ite_true]
    exact Polynomial.C_mul_X_pow_eq_monomial
  · simp [h, zero_pow h]

lemma splitBivariate_coeff {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) (k : ℕ) :
    (splitBivariate p).coeff k = bivariateOther (coefficientIn 0 k p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, coefficientIn_add, map_add, hp, hq]
  | monomial e a =>
    rw [splitBivariate_monomial, Polynomial.coeff_monomial, coefficientIn_monomial]
    by_cases h : e 0 = k
    · simp [h, bivariateOther_monomial, Finsupp.tsub_apply, Finsupp.single_apply]
    · simp only [h, Ne.symm h, ite_false, map_zero]

noncomputable def unsplitBivariate {K : Type} [CommRing K] :
    Polynomial (Polynomial K) →+* MvPolynomial (Fin 2) K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 1)) (MvPolynomial.X 0)

lemma unsplit_splitBivariate {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) :
    unsplitBivariate (splitBivariate p) = p := by
  have hh : (unsplitBivariate (K := K)).comp splitBivariate = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [unsplitBivariate, splitBivariate]
    · intro j
      fin_cases j <;> simp [unsplitBivariate, splitBivariate]
  exact RingHom.congr_fun hh p

lemma splitBivariate_injective {K : Type} [CommRing K] :
    Function.Injective (splitBivariate (K := K)) := by
  intro p q hpq
  rw [← unsplit_splitBivariate p, ← unsplit_splitBivariate q, hpq]

end APSCounting893.Main
end Component_42

section Component_43

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma trailingCoefficient_eq_split {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    trailingCoefficient v p = (splitVariable v p).trailingCoeff := by
  classical
  by_cases hp : p = 0
  · subst p
    simp [trailingCoefficient, splitVariable_zero]
  · have hsplit := splitVariable_ne_zero v p hp
    rw [Polynomial.trailingCoeff]
    rw [splitVariable_coeff]
    apply trailingCoefficient_eq_of_min
    · rw [← splitVariable_coeff]
      exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hsplit
    · intro j hj
      rw [← splitVariable_coeff]
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj

lemma trailingCoefficient_mul {K : Type} [CommRing K] [NoZeroDivisors K] {n : ℕ}
    (v : Fin n) (p q : MvPolynomial (Fin n) K) :
    trailingCoefficient v (p * q) = trailingCoefficient v p * trailingCoefficient v q := by
  rw [trailingCoefficient_eq_split, splitVariable_mul, Polynomial.trailingCoeff_mul,
    ← trailingCoefficient_eq_split, ← trailingCoefficient_eq_split]

lemma splitVariable_C {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (a : K) : splitVariable v (C a) = Polynomial.C (C a) := by
  change splitVariable v (monomial 0 a) = _
  rw [splitVariable_monomial]
  simp

lemma trailingCoefficient_C {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (a : K) : trailingCoefficient v (C a) = C a := by
  rw [trailingCoefficient_eq_split, splitVariable_C]
  simp [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_C]

noncomputable def trailingCoefficientHom {K : Type} [CommRing K] [NoZeroDivisors K] {n : ℕ}
    (v : Fin n) : MvPolynomial (Fin n) K →* MvPolynomial (Fin n) K where
  toFun := trailingCoefficient v
  map_one' := by simpa using trailingCoefficient_C v (1 : K)
  map_mul' := trailingCoefficient_mul v

lemma trailingCoefficient_pow {K : Type} [CommRing K] [NoZeroDivisors K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (m : ℕ) :
    trailingCoefficient v (p ^ m) = trailingCoefficient v p ^ m :=
  (trailingCoefficientHom v).map_pow p m

lemma trailingCoefficient_prod {K : Type} [CommRing K] [NoZeroDivisors K] {n : ℕ}
    {ι : Type} (v : Fin n) (s : Finset ι) (p : ι → MvPolynomial (Fin n) K) :
    trailingCoefficient v (∏ i ∈ s, p i) = ∏ i ∈ s, trailingCoefficient v (p i) :=
  map_prod (trailingCoefficientHom v) p s

end APSCounting893.Main
end Component_43

section Component_44

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma coefficientIn_zero_mul {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p q : MvPolynomial (Fin n) K) :
    coefficientIn v 0 (p * q) = coefficientIn v 0 p * coefficientIn v 0 q := by
  rw [← splitVariable_coeff, splitVariable_mul, Polynomial.mul_coeff_zero,
    splitVariable_coeff, splitVariable_coeff]

lemma coefficientIn_zero_C {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (a : K) : coefficientIn v 0 (C a) = C a := by
  rw [← splitVariable_coeff, splitVariable_C, Polynomial.coeff_C_zero]

lemma coefficientIn_neg {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v k (-p) = -coefficientIn v k p := by
  classical
  ext e
  simp only [coefficientIn_coeff, coeff_neg]
  split_ifs <;> simp

lemma coefficientIn_sub {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p q : MvPolynomial (Fin n) K) :
    coefficientIn v k (p - q) = coefficientIn v k p - coefficientIn v k q := by
  rw [sub_eq_add_neg, coefficientIn_add, coefficientIn_neg, sub_eq_add_neg]

lemma coefficientIn_zero_X {K : Type} [CommRing K] {n : ℕ}
    (v j : Fin n) : coefficientIn v 0 (X j : MvPolynomial (Fin n) K) =
      if j = v then 0 else X j := by
  classical
  change coefficientIn v 0 (monomial (Finsupp.single j 1) (1 : K)) = _
  rw [coefficientIn_monomial]
  by_cases hj : j = v
  · subst j; simp
  · simp [Finsupp.single_apply, hj, Ne.symm hj]
    rfl

lemma coefficientIn_zero_pow {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (m : ℕ) :
    coefficientIn v 0 (p ^ m) = coefficientIn v 0 p ^ m := by
  induction m with
  | zero => simpa using coefficientIn_zero_C v (1 : K)
  | succ m ih => rw [pow_succ, coefficientIn_zero_mul, ih, pow_succ]

lemma trailingCoefficient_eq_of_zero_coeff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (hp : coefficientIn v 0 p ≠ 0) :
    trailingCoefficient v p = coefficientIn v 0 p :=
  trailingCoefficient_eq_of_min v p 0 hp (fun j hj => False.elim (Nat.not_lt_zero j hj))

end APSCounting893.Main
end Component_44

section Component_45

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def coefficientZeroHom {K : Type} [CommRing K] {n : ℕ} (v : Fin n) :
    MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K where
  toFun := coefficientIn v 0
  map_zero' := coefficientIn_zero _ _
  map_one' := coefficientIn_zero_C v 1
  map_add' := coefficientIn_add v 0
  map_mul' := coefficientIn_zero_mul v

lemma bivariateOther_recover {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 1) (bivariateOther p) = coefficientIn 0 0 p := by
  have hh : (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (1 : Fin 2))).comp bivariateOther =
      coefficientZeroHom (K := K) 0 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, bivariateOther, MvPolynomial.eval₂Hom_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact (coefficientIn_zero_C _ _).symm
    · intro j
      fin_cases j <;> simp [bivariateOther, coefficientZeroHom, coefficientIn_zero_X]
  exact RingHom.congr_fun hh p

lemma coefficientIn_zero_idempotent {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v 0 (coefficientIn v k p) = coefficientIn v k p := by
  ext e
  simp only [coefficientIn_coeff, Finsupp.single_zero, add_zero]
  split_ifs <;> rfl

lemma bivariateOther_coefficient_ne_zero {K : Type} [CommRing K]
    (k : ℕ) (p : MvPolynomial (Fin 2) K) (hp : coefficientIn 0 k p ≠ 0) :
    bivariateOther (coefficientIn 0 k p) ≠ 0 := by
  intro hz
  have hh := bivariateOther_recover (coefficientIn 0 k p)
  rw [hz, Polynomial.eval₂_zero, coefficientIn_zero_idempotent] at hh
  exact hp hh.symm

lemma bivariate_trailingCoeff {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) :
    (splitBivariate p).trailingCoeff = bivariateOther (trailingCoefficient 0 p) := by
  classical
  by_cases hp : p = 0
  · simp [hp, trailingCoefficient]
  have hs : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp
  let k := (p.support.image (fun e => e 0)).min' (hs.image _)
  have hcoef : coefficientIn 0 k p ≠ 0 := by
    apply (coefficientIn_ne_zero_iff 0 k p).mpr
    exact Finset.mem_image.mp (Finset.min'_mem _ (hs.image _))
  have hsplit : splitBivariate p ≠ 0 := fun hz => hp (splitBivariate_injective (by simpa using hz))
  have hcoeff : (splitBivariate p).coeff k ≠ 0 := by
    rw [splitBivariate_coeff]
    exact bivariateOther_coefficient_ne_zero k p hcoef
  have hlower : ∀ j < k, (splitBivariate p).coeff j = 0 := by
    intro j hj
    rw [splitBivariate_coeff]
    have hz : coefficientIn 0 j p = 0 := by
      by_contra hn
      obtain ⟨e, he, hev⟩ := (coefficientIn_ne_zero_iff 0 j p).mp hn
      have hkj : k ≤ j := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e, he, hev⟩)
      omega
    rw [hz, map_zero]
  have hdeg : (splitBivariate p).natTrailingDegree = k :=
    le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hcoeff)
      (Polynomial.le_natTrailingDegree hsplit hlower)
  rw [Polynomial.trailingCoeff, hdeg, splitBivariate_coeff]
  rw [trailingCoefficient, dif_pos hs]

end APSCounting893.Main
end Component_45

section Component_46

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def bivariateSeries {K : Type} [CommRing K] :
    MvPolynomial (Fin 2) K →+* Polynomial (HahnSeries ℚ K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp HahnSeries.C)
    (fun j => if j = 0 then Polynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) else Polynomial.X)

lemma bivariateSeries_X_zero {K : Type} [CommRing K] :
    bivariateSeries (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) =
      Polynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) := by simp [bivariateSeries]

lemma bivariateSeries_X_one {K : Type} [CommRing K] :
    bivariateSeries (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) = Polynomial.X := by simp [bivariateSeries]

lemma splitBivariate_X_zero {K : Type} [CommRing K] :
    splitBivariate (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) = Polynomial.X := by simp [splitBivariate]

lemma splitBivariate_X_one {K : Type} [CommRing K] :
    splitBivariate (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) = Polynomial.C Polynomial.X := by simp [splitBivariate]

lemma polynomialToHahn_bivariateSeries {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) :
    polynomialToHahn (bivariateSeries p) =
      algebraMap (Polynomial (Polynomial K)) (HahnSeries ℚ (Polynomial K)) (splitBivariate p) := by
  have hh : (polynomialToHahn (K := K)).comp bivariateSeries =
      (algebraMap (Polynomial (Polynomial K)) (HahnSeries ℚ (Polynomial K))).comp splitBivariate := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, bivariateSeries, splitBivariate, MvPolynomial.eval₂Hom_C,
        RingHom.comp_apply, polynomialToHahn_C]
      rw [show HahnSeries.C c = HahnSeries.single (0 : ℚ) c from rfl, hahnCoefficientMap_single]
      simp [Polynomial.algebraMap_hahnSeries_apply]
    · intro j
      fin_cases j <;> ext q <;>
        simp [bivariateSeries, splitBivariate, polynomialToHahn, hahnCoefficientMap,
          Polynomial.algebraMap_hahnSeries_apply, HahnSeries.C_apply, HahnSeries.coeff_single]

  exact RingHom.congr_fun hh p

lemma bivariate_scalar_product_trailingCoeff {K ι : Type} [Field K]
    (p : MvPolynomial (Fin 2) K) (c : HahnSeries ℚ K) (hc : c ≠ 0)
    (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop)
    (hp : bivariateSeries p = Polynomial.C c *
      ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i) :
    ∃ a : K, a ≠ 0 ∧ (splitBivariate p).trailingCoeff =
      Polynomial.C a * ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  refine ⟨c.leadingCoeff, HahnSeries.leadingCoeff_ne_zero.mpr hc, ?_⟩
  have hh := congrArg (fun q => (polynomialToHahn q).leadingCoeff) hp
  rw [polynomialToHahn_bivariateSeries, polynomial_hahn_leadingCoeff,
    polynomialToHahn_scalar_product_leadingCoeff c s x mu hx] at hh
  exact hh

end APSCounting893.Main
end Component_46

section Component_47

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

lemma bivariate_trailing_factorization {K ι : Type} [Field K]
    (p : MvPolynomial (Fin 2) K) (c : HahnSeries ℚ K) (hc : c ≠ 0)
    (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop)
    (hp : bivariateSeries p = Polynomial.C c *
      ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i) :
    ∃ a : K, a ≠ 0 ∧ bivariateOther (trailingCoefficient 0 p) =
      Polynomial.C a * ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  obtain ⟨a, ha, heq⟩ := bivariate_scalar_product_trailingCoeff p c hc s x mu hx hp
  rw [bivariate_trailingCoeff] at heq
  exact ⟨a, ha, heq⟩

end APSCounting893.Main
end Component_47

section Component_48

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

lemma polynomial_trailingCoeff_map_injective {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).trailingCoeff = f p.trailingCoeff := by
  by_cases hp : p = 0
  · simp [hp, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_zero]
  have hm : (p.map f).coeff p.natTrailingDegree ≠ 0 := by
    rw [Polynomial.coeff_map]
    exact fun h => (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp) (hf (h.trans f.map_zero.symm))
  have hp' : p.map f ≠ 0 := fun h => hm (by simp [h])
  have hd : (p.map f).natTrailingDegree = p.natTrailingDegree :=
    le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hm)
      (Polynomial.le_natTrailingDegree hp' (fun j hj => by
        rw [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj, map_zero]))
  rw [Polynomial.trailingCoeff, hd, Polynomial.coeff_map]
  rfl

end APSCounting893.Main
end Component_48

section Component_49

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma bivariateSeries_injective {K : Type} [CommRing K] :
    Function.Injective (bivariateSeries (K := K)) := by
  intro p q hpq
  apply splitBivariate_injective
  apply (Polynomial.algebraMap_hahnSeries_injective (Γ := ℚ) (R := Polynomial K))
  rw [← polynomialToHahn_bivariateSeries, ← polynomialToHahn_bivariateSeries, hpq]

noncomputable def threeVariableSeries {K : Type} [CommRing K] :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) (HahnSeries ℚ K) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp HahnSeries.C)
    (fun j => if j = 0 then MvPolynomial.X 0 else
      if j = 1 then MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) else MvPolynomial.X 1)

lemma split_threeVariableSeries {K : Type} [CommRing K] (p : MvPolynomial (Fin 3) K) :
    splitBivariate (threeVariableSeries p) =
      Polynomial.map bivariateSeries (MvPolynomial.finSuccEquiv K 2 p) := by
  have hh : (splitBivariate (K := HahnSeries ℚ K)).comp threeVariableSeries =
      (Polynomial.mapRingHom (bivariateSeries (K := K))).comp (MvPolynomial.finSuccEquiv K 2).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change splitBivariate (threeVariableSeries (MvPolynomial.C c)) =
        Polynomial.map bivariateSeries (MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C c))
      have hc : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C c) =
          Polynomial.C (MvPolynomial.C c) := (MvPolynomial.finSuccEquiv K 2).commutes c
      rw [hc]
      simp [threeVariableSeries, splitBivariate, bivariateSeries]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [threeVariableSeries, splitBivariate, bivariateSeries, MvPolynomial.finSuccEquiv_X_zero]
      · change splitBivariate (threeVariableSeries (MvPolynomial.X i.succ)) =
          Polynomial.map bivariateSeries (MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X i.succ))
        rw [MvPolynomial.finSuccEquiv_X_succ]
        fin_cases i <;> simp [threeVariableSeries, splitBivariate, bivariateSeries]
  exact RingHom.congr_fun hh p

lemma threeVariableSeries_trailing {K : Type} [CommRing K] (p : MvPolynomial (Fin 3) K) :
    bivariateOther (trailingCoefficient 0 (threeVariableSeries p)) =
      bivariateSeries (MvPolynomial.finSuccEquiv K 2 p).trailingCoeff := by
  rw [← bivariate_trailingCoeff, split_threeVariableSeries,
    polynomial_trailingCoeff_map_injective _ bivariateSeries_injective]

end APSCounting893.Main
end Component_49

section Component_50

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma splitVariable_X {K : Type} [CommRing K] {n : ℕ} (v j : Fin n) :
    splitVariable v (MvPolynomial.X j : MvPolynomial (Fin n) K) =
      if j = v then Polynomial.X else Polynomial.C (MvPolynomial.X j) := by
  classical
  change splitVariable v (monomial (Finsupp.single j 1) (1 : K)) = _
  rw [splitVariable_monomial]
  by_cases hj : j = v
  · subst j
    simp
    exact Polynomial.monomial_one_one_eq_X
  · simp [hj, Ne.symm hj, Finsupp.single_apply]
    rfl

noncomputable def splitVariableRingHom {K : Type} [CommRing K] {n : ℕ} (v : Fin n) :
    MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial (Fin n) K) where
  toFun := splitVariable v
  map_zero' := splitVariable_zero v
  map_one' := by simpa using splitVariable_C v (1 : K)
  map_add' := splitVariable_add v
  map_mul' := splitVariable_mul v

lemma splitVariable_fin_zero {K : Type} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin (n+1)) K) :
    splitVariable 0 p = Polynomial.map (MvPolynomial.rename Fin.succ).toRingHom
      (MvPolynomial.finSuccEquiv K n p) := by
  have hh : (splitVariableRingHom (K := K) (0 : Fin (n+1))) =
      (Polynomial.mapRingHom (MvPolynomial.rename Fin.succ).toRingHom).comp (MvPolynomial.finSuccEquiv K n).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change splitVariable 0 (MvPolynomial.C c) = _
      rw [splitVariable_C]
      have hc : MvPolynomial.finSuccEquiv K n (MvPolynomial.C c) =
          Polynomial.C (MvPolynomial.C c) := (MvPolynomial.finSuccEquiv K n).commutes c
      change Polynomial.C (MvPolynomial.C c) = Polynomial.map _ (MvPolynomial.finSuccEquiv K n (MvPolynomial.C c))
      rw [hc, Polynomial.map_C]
      change Polynomial.C (MvPolynomial.C c) = Polynomial.C (MvPolynomial.rename Fin.succ (MvPolynomial.C c))
      rw [MvPolynomial.rename_C]
    · intro j
      change splitVariable 0 (MvPolynomial.X j) = _
      rw [splitVariable_X]
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [MvPolynomial.finSuccEquiv_X_zero]
      · simp [MvPolynomial.finSuccEquiv_X_succ]
  exact RingHom.congr_fun hh p

lemma trailingCoefficient_fin_zero {K : Type} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin (n+1)) K) :
    trailingCoefficient 0 p = MvPolynomial.rename Fin.succ (MvPolynomial.finSuccEquiv K n p).trailingCoeff := by
  rw [trailingCoefficient_eq_split, splitVariable_fin_zero,
    polynomial_trailingCoeff_map_injective _ (MvPolynomial.rename_injective _ (Fin.succ_injective n))]
  rfl

end APSCounting893.Main
end Component_50

section Component_51

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma splitVariable_rename_succ {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    splitVariable v.succ (MvPolynomial.rename Fin.succ p) =
      Polynomial.map (MvPolynomial.rename Fin.succ).toRingHom (splitVariable v p) := by
  have hh : (splitVariableRingHom (K := K) v.succ).comp (MvPolynomial.rename Fin.succ).toRingHom =
      (Polynomial.mapRingHom (MvPolynomial.rename Fin.succ).toRingHom).comp (splitVariableRingHom v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change splitVariable v.succ (MvPolynomial.rename Fin.succ (MvPolynomial.C c)) = _
      rw [MvPolynomial.rename_C, splitVariable_C]
      change Polynomial.C (MvPolynomial.C c) = Polynomial.map _ (splitVariable v (MvPolynomial.C c))
      rw [splitVariable_C, Polynomial.map_C]
      change Polynomial.C (MvPolynomial.C c) = Polynomial.C (MvPolynomial.rename Fin.succ (MvPolynomial.C c))
      rw [MvPolynomial.rename_C]
    · intro j
      change splitVariable v.succ (MvPolynomial.rename Fin.succ (MvPolynomial.X j)) = _
      rw [MvPolynomial.rename_X, splitVariable_X]
      change (if j.succ = v.succ then Polynomial.X else Polynomial.C (MvPolynomial.X j.succ)) =
        Polynomial.map _ (splitVariable v (MvPolynomial.X j))
      rw [splitVariable_X]
      simp only [Fin.succ_inj]
      by_cases hj : j = v
      · simp [hj]
      · simp [hj]
  exact RingHom.congr_fun hh p

lemma trailingCoefficient_rename_succ {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    trailingCoefficient v.succ (MvPolynomial.rename Fin.succ p) =
      MvPolynomial.rename Fin.succ (trailingCoefficient v p) := by
  rw [trailingCoefficient_eq_split, splitVariable_rename_succ,
    polynomial_trailingCoeff_map_injective _ (MvPolynomial.rename_injective _ (Fin.succ_injective n)),
    ← trailingCoefficient_eq_split]
  rfl

end APSCounting893.Main
end Component_51

section Component_52

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def epsilonFormal (R : Aux) : MvPolynomial (Fin 3) ℂ :=
  (MvPolynomial.finSuccEquiv ℂ 3 R).trailingCoeff

noncomputable def wFormal (R : Aux) : MvPolynomial (Fin 2) ℂ :=
  (MvPolynomial.finSuccEquiv ℂ 2 (epsilonFormal R)).trailingCoeff

lemma trailingEpsilonResultant_eq (R : Aux) :
    trailingEpsilonResultant R = threeVariableSeries (epsilonFormal R) := by
  unfold trailingEpsilonResultant
  rw [trailingCoefficient_fin_zero]
  change MvPolynomial.eval₂ (MvPolynomial.C.comp HahnSeries.C)
      (fun v : Fin 4 => if v = 1 then MvPolynomial.X 0 else if v = 3 then MvPolynomial.X 1
        else if v = 2 then MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0)
      (MvPolynomial.rename Fin.succ (epsilonFormal R)) = _
  rw [MvPolynomial.eval₂_rename]
  change MvPolynomial.eval₂ _ _ (epsilonFormal R) = MvPolynomial.eval₂ _ _ (epsilonFormal R)
  apply MvPolynomial.eval₂_congr
  intro v e he hp
  fin_cases v <;> simp [Function.comp_def]

set_option maxRecDepth 4096 in
lemma wFormal_series_eq (R : Aux) :
    bivariateSeries (wFormal R) = bivariateOther (trailingCoefficient 0 (trailingEpsilonResultant R)) := by
  rw [trailingEpsilonResultant_eq, threeVariableSeries_trailing]
  rfl

lemma resultantCriterion_eq_formal (R : Aux) :
    resultantCriterion R = bivariateOther (trailingCoefficient 0 (wFormal R)) := by
  have h1 : trailingCoefficient (1 : Fin 4) (trailingCoefficient 0 R) =
      MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (wFormal R)) := by
    calc
      trailingCoefficient (1 : Fin 4) (trailingCoefficient 0 R) =
          trailingCoefficient (0 : Fin 3).succ (MvPolynomial.rename Fin.succ (epsilonFormal R)) := by
        rw [trailingCoefficient_fin_zero]
        rfl
      _ = MvPolynomial.rename Fin.succ (trailingCoefficient 0 (epsilonFormal R)) :=
        trailingCoefficient_rename_succ (0 : Fin 3) (epsilonFormal R)
      _ = MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (wFormal R)) := by
        exact congrArg (MvPolynomial.rename Fin.succ) (trailingCoefficient_fin_zero (epsilonFormal R))
  have h2 : trailingCoefficient (2 : Fin 4) (trailingCoefficient 1 (trailingCoefficient 0 R)) =
      MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (trailingCoefficient 0 (wFormal R))) := by
    rw [h1]
    calc
      trailingCoefficient (2 : Fin 4) (MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (wFormal R))) =
          MvPolynomial.rename Fin.succ (trailingCoefficient (1 : Fin 3) (MvPolynomial.rename Fin.succ (wFormal R))) :=
        trailingCoefficient_rename_succ (1 : Fin 3) (MvPolynomial.rename Fin.succ (wFormal R))
      _ = _ := congrArg (MvPolynomial.rename Fin.succ)
        (trailingCoefficient_rename_succ (0 : Fin 2) (wFormal R))

  unfold resultantCriterion nestedTrailing
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h2]
  change MvPolynomial.eval₂ Polynomial.C (fun i : Fin 4 => if i = 3 then Polynomial.X else 0)
    (MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (trailingCoefficient 0 (wFormal R)))) = _
  rw [MvPolynomial.eval₂_rename, MvPolynomial.eval₂_rename]
  change MvPolynomial.eval₂ _ _ (trailingCoefficient 0 (wFormal R)) =
    MvPolynomial.eval₂ _ _ (trailingCoefficient 0 (wFormal R))
  apply MvPolynomial.eval₂_congr
  intro i e he hp
  fin_cases i <;> simp [Function.comp_def]

end APSCounting893.Main
end Component_52

section Component_53

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def mvPolynomialToHahn {K σ : Type} [CommRing K] :
    MvPolynomial σ (HahnSeries ℚ K) →+* HahnSeries ℚ (MvPolynomial σ K) :=
  MvPolynomial.eval₂Hom (hahnCoefficientMap MvPolynomial.C) (fun i => HahnSeries.C (MvPolynomial.X i))

lemma mvPolynomialToHahn_C {K σ : Type} [CommRing K] (s : HahnSeries ℚ K) :
    mvPolynomialToHahn (MvPolynomial.C s : MvPolynomial σ (HahnSeries ℚ K)) =
      hahnCoefficientMap MvPolynomial.C s := by simp [mvPolynomialToHahn]

lemma mvPolynomialToHahn_X {K σ : Type} [CommRing K] (i : σ) :
    mvPolynomialToHahn (MvPolynomial.X i : MvPolynomial σ (HahnSeries ℚ K)) =
      HahnSeries.C (MvPolynomial.X i) := by simp [mvPolynomialToHahn]

lemma mvPolynomialToHahn_monomial {K σ : Type} [CommRing K]
    (e : σ →₀ ℕ) (s : HahnSeries ℚ K) :
    mvPolynomialToHahn (MvPolynomial.monomial e s) =
      hahnCoefficientMap MvPolynomial.C s * HahnSeries.C (MvPolynomial.monomial e (1 : K)) := by
  classical
  rw [mvPolynomialToHahn,MvPolynomial.eval₂Hom_monomial]
  have hp : e.prod (fun i k => (HahnSeries.C (MvPolynomial.X i) : HahnSeries ℚ (MvPolynomial σ K)) ^ k) =
      HahnSeries.C (MvPolynomial.monomial e (1 : K)) := by
    rw [MvPolynomial.monomial_eq,MvPolynomial.C_1,one_mul]
    simp only [Finsupp.prod,map_prod,map_pow]
  rw [hp]

lemma mvPolynomialToHahn_monomial_coeff {K σ : Type} [CommRing K]
    (e : σ →₀ ℕ) (s : HahnSeries ℚ K) (q : ℚ) :
    (mvPolynomialToHahn (MvPolynomial.monomial e s)).coeff q =
      MvPolynomial.monomial e (s.coeff q) := by
  rw [mvPolynomialToHahn_monomial,HahnSeries.C_apply,HahnSeries.coeff_mul_single,
    sub_zero,hahnCoefficientMap_coeff,MvPolynomial.C_mul_monomial, mul_one]

lemma mvPolynomialToHahn_coeff {K σ : Type} [CommRing K]
    (p : MvPolynomial σ (HahnSeries ℚ K)) (q : ℚ) :
    (mvPolynomialToHahn p).coeff q = ∑ e ∈ p.support, MvPolynomial.monomial e ((p.coeff e).coeff q) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum,HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact mvPolynomialToHahn_monomial_coeff e _ q

lemma mvPolynomialToHahn_regular {K σ : Type} [CommRing K] [IsDomain K]
    (p : MvPolynomial σ (HahnSeries ℚ K))
    (hp : ∀ e, 0 ≤ (p.coeff e).orderTop) : 0 ≤ (mvPolynomialToHahn p).orderTop := by
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro q hq
  rw [mvPolynomialToHahn_coeff]
  apply Finset.sum_eq_zero
  intro e he
  rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (hq.trans_le (hp e)),MvPolynomial.monomial_zero]

end APSCounting893.Main
end Component_53

section Component_54

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma threeVariableSeries_injective {K : Type} [CommRing K] :
    Function.Injective (threeVariableSeries (K := K)) := by
  intro p q hpq
  apply (MvPolynomial.finSuccEquiv K 2).injective
  apply Polynomial.map_injective bivariateSeries bivariateSeries_injective
  rw [← split_threeVariableSeries,← split_threeVariableSeries,hpq]

noncomputable def epsilonPolynomial (R : Aux) : Polynomial (MvPolynomial (Fin 2) PuiseuxAmbient) :=
  Polynomial.map threeVariableSeries (MvPolynomial.finSuccEquiv ℂ 3 R)

lemma epsilonPolynomial_trailingCoeff (R : Aux) :
    (epsilonPolynomial R).trailingCoeff = trailingEpsilonResultant R := by
  rw [epsilonPolynomial,polynomial_trailingCoeff_map_injective _ threeVariableSeries_injective,
    trailingEpsilonResultant_eq]
  rfl

noncomputable def epsilonResultantEvaluation : Aux →+* MvPolynomial (Fin 2) EpsilonAmbient :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (HahnSeries.C.comp HahnSeries.C))
    (fun v : Fin 4 => if v = 0 then MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : PuiseuxAmbient))
      else if v = 1 then MvPolynomial.X 0 else if v = 2 then
        MvPolynomial.C (HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ))) else MvPolynomial.X 1)

lemma polynomial_hahn_C {R : Type} [CommRing R] (r : R) :
    algebraMap (Polynomial R) (HahnSeries ℚ R) (Polynomial.C r) = HahnSeries.C r := by
  rw [Polynomial.algebraMap_hahnSeries_apply,Polynomial.coe_C,HahnSeries.ofPowerSeries_C]

lemma polynomial_hahn_X {R : Type} [CommRing R] :
    algebraMap (Polynomial R) (HahnSeries ℚ R) Polynomial.X = HahnSeries.single (1 : ℚ) (1 : R) := by
  rw [Polynomial.algebraMap_hahnSeries_apply,Polynomial.coe_X,HahnSeries.ofPowerSeries_X]

lemma epsilonPolynomial_evaluation (R : Aux) :
    mvPolynomialToHahn (epsilonResultantEvaluation R) =
      algebraMap (Polynomial (MvPolynomial (Fin 2) PuiseuxAmbient))
        (HahnSeries ℚ (MvPolynomial (Fin 2) PuiseuxAmbient)) (epsilonPolynomial R) := by
  let k := MvPolynomial (Fin 2) PuiseuxAmbient
  have hh : (mvPolynomialToHahn (σ := Fin 2) (K := PuiseuxAmbient)).comp epsilonResultantEvaluation =
      (algebraMap (Polynomial k) (HahnSeries ℚ k)).comp
        ((Polynomial.mapRingHom (threeVariableSeries (K := ℂ))).comp (MvPolynomial.finSuccEquiv ℂ 3).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc : MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) :=
        (MvPolynomial.finSuccEquiv ℂ 3).commutes c
      change mvPolynomialToHahn (epsilonResultantEvaluation (MvPolynomial.C c)) =
        algebraMap (Polynomial k) (HahnSeries ℚ k) (Polynomial.map threeVariableSeries
          (MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.C c)))
      rw [hc,Polynomial.map_C,polynomial_hahn_C (R := k)]
      simp [epsilonResultantEvaluation,mvPolynomialToHahn_C,threeVariableSeries,
        HahnSeries.C_apply,hahnCoefficientMap_single]
    · intro v
      refine Fin.cases ?_ (fun j => ?_) v
      · change mvPolynomialToHahn (epsilonResultantEvaluation (MvPolynomial.X 0)) =
          algebraMap (Polynomial k) (HahnSeries ℚ k) (Polynomial.map threeVariableSeries
            (MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.X 0)))
        rw [MvPolynomial.finSuccEquiv_X_zero,Polynomial.map_X,polynomial_hahn_X (R := k)]
        simp [epsilonResultantEvaluation,mvPolynomialToHahn_C,hahnCoefficientMap_single]
      · change mvPolynomialToHahn (epsilonResultantEvaluation (MvPolynomial.X j.succ)) =
          algebraMap (Polynomial k) (HahnSeries ℚ k) (Polynomial.map threeVariableSeries
            (MvPolynomial.finSuccEquiv ℂ 3 (MvPolynomial.X j.succ)))
        rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C,polynomial_hahn_C (R := k)]
        fin_cases j <;> simp [epsilonResultantEvaluation,mvPolynomialToHahn_C,mvPolynomialToHahn_X,
          threeVariableSeries,HahnSeries.C_apply,hahnCoefficientMap_single]
  exact RingHom.congr_fun hh R

lemma epsilonResultantEvaluation_leadingCoeff (R : Aux) :
    (mvPolynomialToHahn (epsilonResultantEvaluation R)).leadingCoeff = trailingEpsilonResultant R := by
  rw [epsilonPolynomial_evaluation,polynomial_hahn_leadingCoeff,epsilonPolynomial_trailingCoeff]

end APSCounting893.Main
end Component_54

section Component_55

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def quadraticEvaluationVector {K : Type} [Field K] {n : ℕ}
    (x : Fin n → K) : DegreeMonomial (n+1) 2 →₀ K :=
  Finsupp.equivFunOnFinite.symm (fun e => e.1.prod (fun j k => (Fin.cons 1 x : Fin (n+1) → K) j ^ k))

noncomputable def quadraticEvaluationLinearForm {K : Type} [Field K] {n : ℕ}
    (x : Fin n → K) : MvPolynomial (DegreeMonomial (n+1) 2) K :=
  MvPolynomial.sumSMulX (quadraticEvaluationVector x)

lemma quadraticEvaluationLinearForm_coeff {K : Type} [Field K] {n : ℕ}
    (x : Fin n → K) (e : DegreeMonomial (n+1) 2) :
    (quadraticEvaluationLinearForm x).coeff (Finsupp.single e 1) =
      e.1.prod (fun j k => (Fin.cons 1 x : Fin (n+1) → K) j ^ k) := by
  rw [quadraticEvaluationLinearForm,MvPolynomial.coeff_sumSMulX]
  simp [quadraticEvaluationVector]

lemma quadraticEvaluationLinearForm_irreducible {K : Type} [Field K] {n : ℕ}
    (x : Fin n → K) : Irreducible (quadraticEvaluationLinearForm x) := by
  classical
  let e0 : DegreeMonomial (n+1) 2 := ⟨Finsupp.single 0 2,by simp⟩
  have h0 : quadraticEvaluationVector x e0 = 1 := by simp [quadraticEvaluationVector,e0,Finsupp.single_apply,Fin.prod_univ_succ]
  apply MvPolynomial.irreducible_sumSMulX
  · exact ⟨e0,Finsupp.mem_support_iff.mpr (by rw [h0]; exact one_ne_zero)⟩
  · intro r hr
    exact isUnit_of_dvd_one (by rw [← h0]; exact hr e0)

lemma associated_of_unit_coefficient_eq {K σ : Type} [Field K]
    (p q : MvPolynomial σ K) (e : σ →₀ ℕ) (hp : p.coeff e = 1) (hq : q.coeff e = 1)
    (hassoc : Associated p q) : p = q := by
  obtain ⟨u,hu⟩ := hassoc
  have hdeg := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp u.isUnit).2
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  let c := MvPolynomial.coeff 0 (u : MvPolynomial σ K)
  change (u : MvPolynomial σ K) = MvPolynomial.C c at hC
  have he : p * MvPolynomial.C c = q := by rw [hC] at hu; exact hu
  have hc : c = 1 := by
    have hh := congrArg (MvPolynomial.coeff e) he
    rw [mul_comm p,MvPolynomial.coeff_C_mul,hp,hq,mul_one] at hh
    exact hh
  simpa only [hc,MvPolynomial.C_1,mul_one] using he

lemma quadraticEvaluationLinearForm_associated_injective {K : Type} [Field K] {n : ℕ}
    (x y : Fin n → K)
    (h : Associated (quadraticEvaluationLinearForm x) (quadraticEvaluationLinearForm y)) : x = y := by
  classical
  let e0 : DegreeMonomial (n+1) 2 := ⟨Finsupp.single 0 2,by simp⟩
  have hx : (quadraticEvaluationLinearForm x).coeff (Finsupp.single e0 1) = 1 := by
    rw [quadraticEvaluationLinearForm_coeff]
    simp [e0]
  have hy : (quadraticEvaluationLinearForm y).coeff (Finsupp.single e0 1) = 1 := by
    rw [quadraticEvaluationLinearForm_coeff]
    simp [e0]
  have he := associated_of_unit_coefficient_eq _ _ _ hx hy h
  funext j
  let ej : DegreeMonomial (n+1) 2 := ⟨Finsupp.single 0 1 + Finsupp.single j.succ 1,by simp⟩
  have hh := congrArg (MvPolynomial.coeff (Finsupp.single ej 1)) he
  rw [quadraticEvaluationLinearForm_coeff,quadraticEvaluationLinearForm_coeff] at hh
  have hp (z : Fin n → K) : ej.1.prod (fun k l => (Fin.cons 1 z : Fin (n+1) → K) k ^ l) = z j := by
    dsimp only [ej]
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp
  simpa only [hp] using hh

end APSCounting893.Main
end Component_55

section Component_56

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def genericQuadraticForm (K : Type) [CommRing K] (n : ℕ) :
    MvPolynomial (Fin (n+1)) (MvPolynomial (DegreeMonomial (n+1) 2) K) :=
  ∑ e : DegreeMonomial (n+1) 2, MvPolynomial.monomial e.1 (MvPolynomial.X e)

noncomputable def quadraticForm {K : Type} [CommRing K] {n : ℕ}
    (a : DegreeMonomial (n+1) 2 → K) : MvPolynomial (Fin (n+1)) K :=
  ∑ e : DegreeMonomial (n+1) 2, MvPolynomial.monomial e.1 (a e)

lemma genericQuadraticForm_homogeneous {K : Type} [CommRing K] (n : ℕ) :
    (genericQuadraticForm K n).IsHomogeneous 2 := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  exact MvPolynomial.isHomogeneous_monomial _ e.2

lemma quadraticForm_homogeneous {K : Type} [CommRing K] {n : ℕ}
    (a : DegreeMonomial (n+1) 2 → K) : (quadraticForm a).IsHomogeneous 2 := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  exact MvPolynomial.isHomogeneous_monomial _ e.2

lemma genericQuadraticForm_specialization {K : Type} [CommRing K] {n : ℕ}
    (a : DegreeMonomial (n+1) 2 → K) :
    MvPolynomial.map (MvPolynomial.eval a) (genericQuadraticForm K n) = quadraticForm a := by
  simp only [genericQuadraticForm,quadraticForm,map_sum,MvPolynomial.map_monomial,MvPolynomial.eval_X]

lemma quadraticForm_coefficients {K : Type} [CommRing K] {n : ℕ}
    (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous 2) :
    quadraticForm (fun e : DegreeMonomial (n+1) 2 => H.coeff e.1) = H :=
  (homogeneous_sum_monomials H hH).symm

lemma quadraticEvaluationLinearForm_eval {K : Type} [Field K] {n : ℕ}
    (x : Fin n → K) (a : DegreeMonomial (n+1) 2 → K) :
    MvPolynomial.eval a (quadraticEvaluationLinearForm x) =
      MvPolynomial.eval (Fin.cons 1 x) (quadraticForm a) := by
  classical
  simp only [quadraticEvaluationLinearForm,MvPolynomial.sumSMulX,Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype (quadraticEvaluationVector x) (fun i c => c • MvPolynomial.X i) (fun _ => zero_smul K _)]
  simp only [map_sum,MvPolynomial.smul_eval,MvPolynomial.eval_X,quadraticForm,
    MvPolynomial.eval_sum,MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro e he
  have hv : quadraticEvaluationVector x e =
      e.1.prod (fun j k => (Fin.cons 1 x : Fin (n+1) → K) j ^ k) := by
    simp [quadraticEvaluationVector]
  rw [hv,mul_comm]

lemma quadraticEvaluationLinearForm_eval_coefficients {K : Type} [Field K] {n : ℕ}
    (x : Fin n → K) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous 2) :
    MvPolynomial.eval (fun e : DegreeMonomial (n+1) 2 => H.coeff e.1) (quadraticEvaluationLinearForm x) =
      MvPolynomial.eval (Fin.cons 1 x) H := by
  rw [quadraticEvaluationLinearForm_eval,quadraticForm_coefficients H hH]

lemma quadraticForm_pure_zero {K : Type} [CommRing K] {n : ℕ} :
    quadraticForm (fun e : DegreeMonomial (n+1) 2 => if e.1 = Finsupp.single 0 2 then (1 : K) else 0) =
      MvPolynomial.X (0 : Fin (n+1)) ^ 2 := by
  classical
  let e0 : DegreeMonomial (n+1) 2 := ⟨Finsupp.single 0 2,by simp⟩
  unfold quadraticForm
  rw [Finset.sum_eq_single e0]
  · simp [e0,MvPolynomial.X_pow_eq_monomial]
  · intro e he hne
    have hh : e.1 ≠ Finsupp.single 0 2 := by intro h; exact hne (Subtype.ext h)
    simp [hh]
  · simp

end APSCounting893.Main
end Component_56

section Component_57

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma homogeneousResultant_last_zero_iff {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (G : Fin n → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i))
    (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous 2) :
    homogeneousResultant (Fin.lastCases 2 d) (Fin.lastCases H G) = 0 ↔
      ∃ x : Fin (n+1) → K, x ≠ 0 ∧ (∀ i, MvPolynomial.eval x (G i) = 0) ∧ MvPolynomial.eval x H = 0 := by
  have hdeg (i : Fin (n+1)) : 0 < Fin.lastCases 2 d i := by
    refine Fin.lastCases (by simp) (fun i => ?_) i
    simpa using hd i
  have hhom (i : Fin (n+1)) : (Fin.lastCases H G i : MvPolynomial (Fin (n+1)) K).IsHomogeneous (Fin.lastCases 2 d i : ℕ) := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hH
    · simpa using hG i
  rw [homogeneousResultant_zero_iff _ hdeg _ hhom]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  constructor
  · intro hall
    exact ⟨fun i => by simpa using hall i.castSucc,by simpa using hall (Fin.last n)⟩
  · rintro ⟨hgs,hhs⟩ i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hhs
    · simpa using hgs i

end APSCounting893.Main
end Component_57

section Component_58

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace APSCounting893.Main

lemma associated_finite_factor_powers {A ι : Type} [CommMonoidWithZero A] [UniqueFactorizationMonoid A]
    (S : Finset ι) (L : ι → A) (p : A) (hp : p ≠ 0)
    (hfactors : ∀ q : A, Irreducible q → q ∣ p → ∃ z ∈ S, Associated q (L z)) :
    ∃ μ : ι → ℕ, Associated p (∏ z ∈ S, L z ^ μ z) := by
  classical
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hp rfl).elim
  | unit p hu =>
    refine ⟨fun _ => 0,?_⟩
    simpa only [pow_zero,Finset.prod_const_one] using (show Associated p 1 from associated_one_iff_isUnit.mpr hu)
  | mul a q ha hq ih =>
    obtain ⟨z,hz,hzq⟩ := hfactors q hq (dvd_mul_right q a)
    have haFactors (r : A) (hr : Irreducible r) (hra : r ∣ a) :
        ∃ z ∈ S, Associated r (L z) := hfactors r hr (hra.trans (dvd_mul_left a q))
    obtain ⟨μ,hμ⟩ := ih ha haFactors
    let ν : ι → ℕ := fun j => μ j + if j = z then 1 else 0
    refine ⟨ν,?_⟩
    have hprod : (∏ j ∈ S, L j ^ ν j) = L z * (∏ j ∈ S, L j ^ μ j) := by
      simp only [ν,pow_add,Finset.prod_mul_distrib]
      simp [hz,mul_comm]
    rw [hprod]
    exact Associated.mul_mul hzq hμ

lemma associated_positive_finite_factor_powers {A ι : Type} [CommMonoidWithZero A]
    [UniqueFactorizationMonoid A] [Nontrivial A]
    (S : Finset ι) (L : ι → A) (hL : ∀ z ∈ S, Irreducible (L z))
    (hpair : ∀ z ∈ S, ∀ w ∈ S, Associated (L z) (L w) → z = w)
    (p : A) (hp : p ≠ 0)
    (hdiv : ∀ z ∈ S, L z ∣ p)
    (hfactors : ∀ q : A, Irreducible q → q ∣ p → ∃ z ∈ S, Associated q (L z)) :
    ∃ μ : ι → ℕ, (∀ z ∈ S, 0 < μ z) ∧ Associated p (∏ z ∈ S, L z ^ μ z) := by
  classical
  obtain ⟨μ,hμ⟩ := associated_finite_factor_powers S L p hp hfactors
  refine ⟨μ,?_,hμ⟩
  intro z hz
  by_contra hzero
  have hμz : μ z = 0 := by omega
  have hd : L z ∣ ∏ w ∈ S, L w ^ μ w := hμ.dvd_iff_dvd_right.mp (hdiv z hz)
  obtain ⟨w,hw,hdw⟩ := (hL z hz).prime.dvd_finsetProd_iff (fun w => L w ^ μ w) |>.mp hd
  have hdL : L z ∣ L w := (hL z hz).prime.dvd_of_dvd_pow hdw
  have hzw : z = w := hpair z hz w hw ((hL z hz).associated_of_dvd (hL w hw) hdL)
  subst w
  rw [hμz,pow_zero] at hdw
  exact (hL z hz).not_isUnit (isUnit_of_dvd_one hdw)

end APSCounting893.Main
end Component_58

section Component_59

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma irreducible_dvd_of_zero_locus_inclusion {K σ : Type} [Field K] [IsAlgClosed K] [Finite σ]
    (q p : MvPolynomial σ K) (hq : Irreducible q)
    (hv : ∀ x : σ → K, MvPolynomial.eval x q = 0 → MvPolynomial.eval x p = 0) : q ∣ p := by
  haveI : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq.prime
  have hp : p ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K (Ideal.span {q})) := by
    intro x hx
    apply hv x
    have hh := hx q (Ideal.subset_span (Set.mem_singleton q))
    simpa only [MvPolynomial.aeval_eq_eval] using hh
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus,Ideal.mem_span_singleton] at hp
  exact hp

lemma polynomial_factors_of_finite_irreducible_zero_locus {K σ ι : Type}
    [Field K] [IsAlgClosed K] [Finite σ]
    (S : Finset ι) (L : ι → MvPolynomial σ K) (hL : ∀ z ∈ S, Irreducible (L z))
    (hpair : ∀ z ∈ S, ∀ w ∈ S, Associated (L z) (L w) → z = w)
    (p : MvPolynomial σ K) (hp : p ≠ 0)
    (hzero : ∀ x : σ → K, MvPolynomial.eval x p = 0 ↔ ∃ z ∈ S, MvPolynomial.eval x (L z) = 0) :
    ∃ (μ : ι → ℕ) (c : K), c ≠ 0 ∧ (∀ z ∈ S, 0 < μ z) ∧
      p = MvPolynomial.C c * ∏ z ∈ S, L z ^ μ z := by
  classical
  have hdiv (z : ι) (hz : z ∈ S) : L z ∣ p :=
    irreducible_dvd_of_zero_locus_inclusion (L z) p (hL z hz)
      (fun x hx => (hzero x).mpr ⟨z,hz,hx⟩)
  have hfactors (q : MvPolynomial σ K) (hq : Irreducible q) (hqp : q ∣ p) :
      ∃ z ∈ S, Associated q (L z) := by
    have hprod : q ∣ ∏ z ∈ S, L z := irreducible_dvd_of_zero_locus_inclusion q _ hq (by
      intro x hx
      have hpx : MvPolynomial.eval x p = 0 := by
        obtain ⟨a,rfl⟩ := hqp
        rw [map_mul,hx,zero_mul]
      obtain ⟨z,hz,hzx⟩ := (hzero x).mp hpx
      rw [map_prod]
      exact Finset.prod_eq_zero hz hzx)
    obtain ⟨z,hz,hqz⟩ := (hq.prime.dvd_finsetProd_iff L).mp hprod
    exact ⟨z,hz,hq.associated_of_dvd (hL z hz) hqz⟩
  obtain ⟨μ,hμ,hassoc⟩ := associated_positive_finite_factor_powers S L hL hpair p hp hdiv hfactors
  obtain ⟨u,hu⟩ := hassoc.symm
  have hunit : IsUnit (u : MvPolynomial σ K) := u.isUnit
  have hdegree := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
  let c : K := MvPolynomial.coeff 0 (u : MvPolynomial σ K)
  have hc : c ≠ 0 := by
    intro hc
    have hu0 : (u : MvPolynomial σ K) = 0 := by
      rw [hC]
      change MvPolynomial.C c = 0
      rw [hc,map_zero]
    exact u.ne_zero hu0
  refine ⟨μ,c,hc,hμ,?_⟩
  rw [← hu,hC,mul_comm]

end APSCounting893.Main
end Component_59

section Component_60

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def quadraticResultant {K : Type} [CommRing K] {n : ℕ}
    (d : Fin n → ℕ) (G : Fin n → MvPolynomial (Fin (n+1)) K) :
    MvPolynomial (DegreeMonomial (n+1) 2) K :=
  homogeneousResultant (Fin.lastCases 2 d) (Fin.lastCases (genericQuadraticForm K n)
    (fun i => MvPolynomial.map MvPolynomial.C (G i)))

lemma quadraticResultant_specialization {K : Type} [CommRing K] {n : ℕ}
    (d : Fin n → ℕ) (G : Fin n → MvPolynomial (Fin (n+1)) K)
    (a : DegreeMonomial (n+1) 2 → K) :
    MvPolynomial.eval a (quadraticResultant d G) =
      homogeneousResultant (Fin.lastCases 2 d) (Fin.lastCases (quadraticForm a) G) := by
  unfold quadraticResultant
  rw [homogeneousResultant_map]
  apply congrArg (homogeneousResultant (Fin.lastCases 2 d))
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.lastCases_last,genericQuadraticForm_specialization]
  · simp only [Fin.lastCases_castSucc]
    apply MvPolynomial.ext
    intro e
    rw [MvPolynomial.coeff_map,MvPolynomial.coeff_map,MvPolynomial.eval_C]

lemma quadraticResultant_zero_iff_affine {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (G : Fin n → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hnoInf : ∀ z : Fin (n+1) → K, z 0 = 0 → (∀ i, MvPolynomial.eval z (G i) = 0) → z = 0)
    (S : Finset (Fin n → K)) (hS : (S : Set _) = {x | ∀ i, MvPolynomial.eval (Fin.cons 1 x) (G i) = 0})
    (a : DegreeMonomial (n+1) 2 → K) :
    MvPolynomial.eval a (quadraticResultant d G) = 0 ↔
      ∃ x ∈ S, MvPolynomial.eval a (quadraticEvaluationLinearForm x) = 0 := by
  classical
  rw [quadraticResultant_specialization,homogeneousResultant_last_zero_iff d hd G hG _ (quadraticForm_homogeneous a)]
  constructor
  · rintro ⟨z,hz,hGs,hHa⟩
    have hz0 : z 0 ≠ 0 := by intro h; exact hz (hnoInf z h hGs)
    let x : Fin n → K := fun j => (z 0)⁻¹ * z j.succ
    have hpoint : (Fin.cons 1 x : Fin (n+1) → K) = fun j => (z 0)⁻¹ * z j := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [hz0]
      · rfl
    have hrootx (i : Fin n) : MvPolynomial.eval (Fin.cons 1 x) (G i) = 0 := by
      change MvPolynomial.eval₂ (RingHom.id K) (Fin.cons 1 x) (G i) = 0
      rw [hpoint,homogeneous_eval₂_scaled _ _ (hG i),MvPolynomial.eval₂_id,hGs i,mul_zero]
    have hxin : x ∈ S := by
      change x ∈ (S : Set _)
      rw [hS]
      exact hrootx
    refine ⟨x,hxin,?_⟩
    rw [quadraticEvaluationLinearForm_eval]
    change MvPolynomial.eval₂ (RingHom.id K) (Fin.cons 1 x) (quadraticForm a) = 0
    rw [hpoint,homogeneous_eval₂_scaled _ _ (quadraticForm_homogeneous a),MvPolynomial.eval₂_id,hHa,mul_zero]
  · rintro ⟨x,hx,hHa⟩
    have hrootx : ∀ i, MvPolynomial.eval (Fin.cons 1 x) (G i) = 0 := by
      have hh : x ∈ (S : Set _) := hx
      rw [hS] at hh
      exact hh
    refine ⟨Fin.cons 1 x,?_,hrootx,?_⟩
    · intro hh
      have h0 := congrFun hh 0
      simpa using h0
    · rwa [quadraticEvaluationLinearForm_eval] at hHa

lemma quadraticResultant_factorization {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (G : Fin n → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hnoInf : ∀ z : Fin (n+1) → K, z 0 = 0 → (∀ i, MvPolynomial.eval z (G i) = 0) → z = 0)
    (S : Finset (Fin n → K)) (hS : (S : Set _) = {x | ∀ i, MvPolynomial.eval (Fin.cons 1 x) (G i) = 0}) :
    ∃ (μ : (Fin n → K) → ℕ) (c : K), c ≠ 0 ∧ (∀ x ∈ S, 0 < μ x) ∧
      quadraticResultant d G = MvPolynomial.C c * ∏ x ∈ S, quadraticEvaluationLinearForm x ^ μ x := by
  classical
  have hzero := quadraticResultant_zero_iff_affine d hd G hG hnoInf S hS
  have hp : quadraticResultant d G ≠ 0 := by
    intro hp
    let a : DegreeMonomial (n+1) 2 → K := fun e => if e.1 = Finsupp.single 0 2 then 1 else 0
    obtain ⟨x,hx,hh⟩ := (hzero a).mp (by rw [hp,map_zero])
    rw [quadraticEvaluationLinearForm_eval,quadraticForm_pure_zero] at hh
    simpa using hh
  exact polynomial_factors_of_finite_irreducible_zero_locus S quadraticEvaluationLinearForm
    (fun x hx => quadraticEvaluationLinearForm_irreducible x)
    (fun x hx y hy h => quadraticEvaluationLinearForm_associated_injective x y h)
    (quadraticResultant d G) hp hzero

end APSCounting893.Main
end Component_60

section Component_61

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma quadraticEvaluationLinearForm_eval₂ {K B : Type} [Field K] [CommRing B] {n : ℕ}
    (f : K →+* B) (x : Fin n → K) (a : DegreeMonomial (n+1) 2 → B) :
    MvPolynomial.eval₂ f a (quadraticEvaluationLinearForm x) =
      MvPolynomial.eval (fun j => f ((Fin.cons 1 x : Fin (n+1) → K) j)) (quadraticForm a) := by
  classical
  simp only [quadraticEvaluationLinearForm,MvPolynomial.sumSMulX,Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype (quadraticEvaluationVector x) (fun i c => c • MvPolynomial.X i) (fun _ => zero_smul K _)]
  simp only [MvPolynomial.eval₂_sum,quadraticForm,MvPolynomial.eval_sum,MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro e he
  rw [MvPolynomial.smul_eq_C_mul,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_X]
  have hv : quadraticEvaluationVector x e =
      e.1.prod (fun j k => (Fin.cons 1 x : Fin (n+1) → K) j ^ k) := by simp [quadraticEvaluationVector]
  rw [hv]
  simp only [Finsupp.prod,map_prod,map_pow]
  exact mul_comm _ _

lemma quadraticEvaluationLinearForm_eval₂_coefficients {K B : Type} [Field K] [CommRing B] {n : ℕ}
    (f : K →+* B) (x : Fin n → K) (H : MvPolynomial (Fin (n+1)) B) (hH : H.IsHomogeneous 2) :
    MvPolynomial.eval₂ f (fun e : DegreeMonomial (n+1) 2 => H.coeff e.1) (quadraticEvaluationLinearForm x) =
      MvPolynomial.eval (fun j => f ((Fin.cons 1 x : Fin (n+1) → K) j)) H := by
  rw [quadraticEvaluationLinearForm_eval₂,quadraticForm_coefficients H hH]

lemma quadraticResultant_substitution {K B : Type} [CommRing K] [CommRing B] {n : ℕ}
    (f : K →+* B) (d : Fin n → ℕ) (G : Fin n → MvPolynomial (Fin (n+1)) K)
    (H : MvPolynomial (Fin (n+1)) B) (hH : H.IsHomogeneous 2) :
    MvPolynomial.eval₂ f (fun e : DegreeMonomial (n+1) 2 => H.coeff e.1) (quadraticResultant d G) =
      homogeneousResultant (Fin.lastCases 2 d)
        (Fin.lastCases H (fun i => MvPolynomial.map f (G i))) := by
  unfold quadraticResultant
  change (MvPolynomial.eval₂Hom f (fun e : DegreeMonomial (n+1) 2 => H.coeff e.1))
    (homogeneousResultant (Fin.lastCases 2 d) (Fin.lastCases (genericQuadraticForm K n)
      (fun i => MvPolynomial.map MvPolynomial.C (G i)))) = _
  rw [homogeneousResultant_map]
  apply congrArg (homogeneousResultant (Fin.lastCases 2 d))
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.lastCases_last,genericQuadraticForm,map_sum,MvPolynomial.map_monomial,MvPolynomial.eval₂Hom_X']
    exact quadraticForm_coefficients H hH
  · simp only [Fin.lastCases_castSucc,MvPolynomial.map_map]
    have hc : (MvPolynomial.eval₂Hom f (fun e : DegreeMonomial (n+1) 2 => H.coeff e.1)).comp MvPolynomial.C = f := by
      apply RingHom.ext
      intro c
      exact MvPolynomial.eval₂_C _ _ _
    rw [hc]

end APSCounting893.Main
end Component_61

section Component_62

set_option autoImplicit false
set_option maxHeartbeats 4000000
open MvPolynomial
namespace APSCounting893.Main

lemma homogeneousResultant_quadratic_product_over_ring {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (G : Fin n → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i))
    (hnoInf : ∀ z : Fin (n+1) → K, z 0 = 0 → (∀ i, MvPolynomial.eval z (G i) = 0) → z = 0)
    (S : Finset (Fin n → K)) (hS : (S : Set _) = {x | ∀ i, MvPolynomial.eval (Fin.cons 1 x) (G i) = 0}) :
    ∃ (μ : (Fin n → K) → ℕ) (c : K), c ≠ 0 ∧ (∀ x ∈ S, 0 < μ x) ∧
      ∀ (B : Type) [CommRing B] (f : K →+* B) (H : MvPolynomial (Fin (n+1)) B), H.IsHomogeneous 2 →
        homogeneousResultant (Fin.lastCases 2 d) (Fin.lastCases H (fun i => MvPolynomial.map f (G i))) =
          f c * ∏ x ∈ S, MvPolynomial.eval (fun j => f ((Fin.cons 1 x : Fin (n+1) → K) j)) H ^ μ x := by
  classical
  obtain ⟨μ,c,hc,hμ,hfactor⟩ := quadraticResultant_factorization d hd G hG hnoInf S hS
  refine ⟨μ,c,hc,hμ,?_⟩
  intro B inst f H hH
  have hh := congrArg (MvPolynomial.eval₂Hom f (fun e : DegreeMonomial (n+1) 2 => H.coeff e.1)) hfactor
  change MvPolynomial.eval₂ f (fun e : DegreeMonomial (n+1) 2 => H.coeff e.1) (quadraticResultant d G) =
    MvPolynomial.eval₂ f (fun e : DegreeMonomial (n+1) 2 => H.coeff e.1)
      (MvPolynomial.C c * ∏ x ∈ S, quadraticEvaluationLinearForm x ^ μ x) at hh
  rw [quadraticResultant_substitution f d G H hH] at hh
  simpa only [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_prod,MvPolynomial.eval₂_pow,
    quadraticEvaluationLinearForm_eval₂_coefficients f _ H hH] using hh

end APSCounting893.Main
end Component_62

section Component_63

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma HForm_homogeneous (F : RawMap) (lambda : Affine ℂ (F.n+1)) :
    (HForm F lambda).IsHomogeneous 2 := by
  classical
  unfold HForm
  apply MvPolynomial.IsHomogeneous.add
  · apply MvPolynomial.IsHomogeneous.sub
    · simpa only [zero_add] using
        (MvPolynomial.isHomogeneous_C (Fin (F.n+(F.n+1)+1)) (MvPolynomial.X (3 : Fin 4) : Aux)).mul
          (MvPolynomial.isHomogeneous_X_pow (0 : Fin (F.n+(F.n+1)+1)) 2)
    · have hlin : (∑ j : Fin (F.n+1), MvPolynomial.C (MvPolynomial.C (lambda j) : Aux) *
          MvPolynomial.X (j.natAdd F.n).succ).IsHomogeneous 1 := by
        apply MvPolynomial.IsHomogeneous.sum
        intro j hj
        simpa only [zero_add] using
          (MvPolynomial.isHomogeneous_C (Fin (F.n+(F.n+1)+1)) (MvPolynomial.C (lambda j) : Aux)).mul
            (MvPolynomial.isHomogeneous_X Aux (j.natAdd F.n).succ)
      exact (MvPolynomial.isHomogeneous_X Aux (0 : Fin (F.n+(F.n+1)+1))).mul hlin
  · apply MvPolynomial.IsHomogeneous.sum
    intro j hj
    simpa only [zero_add] using
      (MvPolynomial.isHomogeneous_C (Fin (F.n+(F.n+1)+1)) (MvPolynomial.X (1 : Fin 4) ^ (j.val+1) : Aux)).mul
        (MvPolynomial.isHomogeneous_X_pow j.succ 2)

lemma map_homogenize_congr {R B : Type} [CommRing R] [CommRing B] {n : ℕ}
    (f g : R →+* B) (p : MvPolynomial (Fin n) R) (d : ℕ)
    (h : MvPolynomial.map f p = MvPolynomial.map g p) :
    MvPolynomial.map f (homogenizeAll d p) = MvPolynomial.map g (homogenizeAll d p) := by
  classical
  simp only [homogenizeAll,map_sum,MvPolynomial.map_monomial]
  apply Finset.sum_congr rfl
  intro e he
  have hh := congrArg (MvPolynomial.coeff e) h
  simpa only [MvPolynomial.coeff_map] using congrArg
    (MvPolynomial.monomial (Finsupp.single 0 (d-e.sum (fun _ k => k)) + e.mapDomain Fin.succ)) hh

lemma epsilonResultantEvaluation_perturbed (F : RawMap) (c alpha : Affine ℂ F.n)
    (d : Fin (F.n+(F.n+1)) → ℕ) (i : Fin (F.n+(F.n+1))) :
    (MvPolynomial.map epsilonResultantEvaluation (perturbedEquation F c alpha d i) :
      MvPolynomial (Fin (F.n+(F.n+1)+1)) (MvPolynomial (Fin 2) EpsilonAmbient)) =
      MvPolynomial.map MvPolynomial.C (MvPolynomial.map epsilonAuxHom (perturbedEquation F c alpha d i)) := by
  have hcoeff : epsilonResultantEvaluation.comp
      (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      ((MvPolynomial.C : EpsilonAmbient →+* MvPolynomial (Fin 2) EpsilonAmbient).comp epsilonAuxHom).comp
        (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [epsilonResultantEvaluation,epsilonAuxHom]
    · simp [epsilonResultantEvaluation,epsilonAuxHom]
  have heq : MvPolynomial.map epsilonResultantEvaluation (equationWithAux F c alpha i) =
      MvPolynomial.map ((MvPolynomial.C : EpsilonAmbient →+* MvPolynomial (Fin 2) EpsilonAmbient).comp epsilonAuxHom)
        (equationWithAux F c alpha i) := by
    rw [equationWithAux,MvPolynomial.map_map,MvPolynomial.map_map,hcoeff]
  rw [MvPolynomial.map_map,perturbedEquation,map_add,map_add]
  apply congrArg₂ (fun a b : MvPolynomial (Fin (F.n+(F.n+1)+1)) (MvPolynomial (Fin 2) EpsilonAmbient) => a+b)
  · change MvPolynomial.map epsilonResultantEvaluation (homogenizeAll (d i) (equationWithAux F c alpha i)) =
      MvPolynomial.map ((MvPolynomial.C : EpsilonAmbient →+* MvPolynomial (Fin 2) EpsilonAmbient).comp epsilonAuxHom)
        (homogenizeAll (d i) (equationWithAux F c alpha i))
    exact map_homogenize_congr (R := Aux) (B := MvPolynomial (Fin 2) EpsilonAmbient)
      (n := F.n+(F.n+1)) epsilonResultantEvaluation
      ((MvPolynomial.C : EpsilonAmbient →+* MvPolynomial (Fin 2) EpsilonAmbient).comp epsilonAuxHom)
      (equationWithAux F c alpha i) (d i) heq
  · simp [epsilonResultantEvaluation,epsilonAuxHom]

noncomputable def epsilonHAtPoint (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (q : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) : MvPolynomial (Fin 2) EpsilonAmbient := by
  classical
  exact MvPolynomial.X (1 : Fin 2) * MvPolynomial.C (σ := Fin 2) (q 0 ^ 2) -
    MvPolynomial.C (σ := Fin 2) (q 0 * ∑ j : Fin (F.n+1), (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient) ((HahnSeries.C : ℂ →+* PuiseuxAmbient) (lambda j)) * q (j.natAdd F.n).succ) +
    ∑ j : Fin (F.n+(F.n+1)), MvPolynomial.X (0 : Fin 2) ^ (j.val+1) * MvPolynomial.C (σ := Fin 2) (q j.succ ^ 2)

lemma epsilonHForm_evaluation (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (q : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) :
    MvPolynomial.eval (fun j => MvPolynomial.C (q j))
      (MvPolynomial.map epsilonResultantEvaluation (HForm F lambda)) = epsilonHAtPoint F lambda q := by
  classical
  rw [MvPolynomial.eval_map]
  simp [HForm,epsilonHAtPoint,epsilonResultantEvaluation,map_sum,map_mul,map_pow,
    MvPolynomial.eval₂_sub,MvPolynomial.eval₂_add,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,MvPolynomial.eval₂_sum]
  left
  apply Finset.sum_congr rfl
  intro j hj
  rw [← map_mul]
  congr 1
  exact HahnSeries.C_mul_eq_smul

end APSCounting893.Main
end Component_63

section Component_64

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

noncomputable def regularHahnSubring (R : Type) [CommRing R] [IsDomain R] : Subring (HahnSeries ℚ R) where
  carrier := {x | 0 ≤ x.orderTop}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {x y} hx hy := by
    change 0 ≤ (x+y).orderTop
    exact (le_min hx hy).trans HahnSeries.min_orderTop_le_orderTop_add
  neg_mem' hx := by simpa using hx
  mul_mem' hx hy := hahn_regular_mul hx hy

noncomputable def regularHahnResidueHom (R : Type) [CommRing R] [IsDomain R] :
    regularHahnSubring R →+* R where
  toFun x := x.1.coeff 0
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    apply hahn_coeff_zero_mul_regular
    · exact x.2
    · exact y.2

lemma regularHahnSubring_C {R : Type} [CommRing R] [IsDomain R] (r : R) :
    0 ≤ (HahnSeries.C r : HahnSeries ℚ R).orderTop := by
  rw [HahnSeries.zero_le_orderTop_iff,HahnSeries.order_C]

lemma leadingCoeff_eq_coeff_zero_of_regular {R : Type} [CommRing R] [IsDomain R]
    (x : HahnSeries ℚ R) (hx : 0 ≤ x.orderTop) (hc : x.coeff 0 ≠ 0) : x.leadingCoeff = x.coeff 0 := by
  have htop : x.orderTop = 0 := by
    apply HahnSeries.orderTop_eq_of_le
    · exact hc
    · intro q hq
      by_contra h
      have hqneg : q < 0 := lt_of_not_ge h
      have hcast : (q : WithTop ℚ) < 0 := by exact_mod_cast hqneg
      exact hq (HahnSeries.coeff_eq_zero_of_lt_orderTop (hcast.trans_le hx))
  have hx0 : x ≠ 0 := by intro h; exact hc (by simp [h])
  have ho : x.order = 0 := by
    have hh := HahnSeries.order_eq_orderTop_of_ne_zero hx0
    rw [htop] at hh
    exact_mod_cast hh
  simp only [HahnSeries.leadingCoeff_eq,ho]

end APSCounting893.Main
end Component_64

section Component_65

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def coefficientToRegularPolynomialHahn {K σ : Type} [Field K] :
    nonnegativeHahnRing K →+* regularHahnSubring (MvPolynomial σ K) where
  toFun x := ⟨hahnCoefficientMap MvPolynomial.C x.1,hahnCoefficientMap_regular _ _ x.2⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_one' := by apply Subtype.ext; exact map_one _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

noncomputable def mvPolynomialToRegularHahn {K σ : Type} [Field K] :
    MvPolynomial σ (nonnegativeHahnRing K) →+* regularHahnSubring (MvPolynomial σ K) :=
  MvPolynomial.eval₂Hom coefficientToRegularPolynomialHahn
    (fun i => ⟨HahnSeries.C (MvPolynomial.X i),regularHahnSubring_C _⟩)

lemma mvPolynomialToRegularHahn_C {K σ : Type} [Field K] (x : nonnegativeHahnRing K) :
    mvPolynomialToRegularHahn (MvPolynomial.C x : MvPolynomial σ (nonnegativeHahnRing K)) =
      coefficientToRegularPolynomialHahn x := by
  simp [mvPolynomialToRegularHahn]

lemma mvPolynomialToRegularHahn_X {K σ : Type} [Field K] (i : σ) :
    mvPolynomialToRegularHahn (MvPolynomial.X i : MvPolynomial σ (nonnegativeHahnRing K)) =
      ⟨HahnSeries.C (MvPolynomial.X i),regularHahnSubring_C _⟩ := by
  simp [mvPolynomialToRegularHahn]

lemma mvPolynomialToRegularHahn_underlying {K σ : Type} [Field K]
    (p : MvPolynomial σ (nonnegativeHahnRing K)) :
    (mvPolynomialToRegularHahn p).1 =
      mvPolynomialToHahn (MvPolynomial.map (nonnegativeHahnRing K).subtype p) := by
  have hh : (regularHahnSubring (MvPolynomial σ K)).subtype.comp mvPolynomialToRegularHahn =
      (mvPolynomialToHahn (σ := σ)).comp (MvPolynomial.map (nonnegativeHahnRing K).subtype) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      rw [RingHom.comp_apply,RingHom.comp_apply,mvPolynomialToRegularHahn_C,MvPolynomial.map_C]
      change hahnCoefficientMap MvPolynomial.C x.1 = mvPolynomialToHahn (MvPolynomial.C x.1)
      rw [mvPolynomialToHahn_C]
    · intro i
      rw [RingHom.comp_apply,RingHom.comp_apply,mvPolynomialToRegularHahn_X,MvPolynomial.map_X]
      change HahnSeries.C (MvPolynomial.X i) = mvPolynomialToHahn (MvPolynomial.X i)
      rw [mvPolynomialToHahn_X]
  exact RingHom.congr_fun hh p

lemma mvPolynomialToRegularHahn_residue {K σ : Type} [Field K]
    (p : MvPolynomial σ (nonnegativeHahnRing K)) :
    (mvPolynomialToRegularHahn p).1.coeff 0 = MvPolynomial.map (hahnResidueHom K) p := by
  have hh : (regularHahnResidueHom (MvPolynomial σ K)).comp mvPolynomialToRegularHahn =
      MvPolynomial.map (hahnResidueHom K) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      rw [RingHom.comp_apply,mvPolynomialToRegularHahn_C,MvPolynomial.map_C]
      change (hahnCoefficientMap MvPolynomial.C x.1).coeff 0 = MvPolynomial.C (hahnResidueHom K x)
      rfl
    · intro i
      rw [RingHom.comp_apply,mvPolynomialToRegularHahn_X,MvPolynomial.map_X]
      change (HahnSeries.C (MvPolynomial.X i) : HahnSeries ℚ (MvPolynomial σ K)).coeff 0 = MvPolynomial.X i
      simp [HahnSeries.C_apply]
  exact RingHom.congr_fun hh p

end APSCounting893.Main
end Component_65

section Component_66

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma regular_polynomial_hahn_leadingCoeff {K σ : Type} [Field K]
    (p : MvPolynomial σ (nonnegativeHahnRing K))
    (hp : MvPolynomial.map (hahnResidueHom K) p ≠ 0) :
    (mvPolynomialToHahn (MvPolynomial.map (nonnegativeHahnRing K).subtype p)).leadingCoeff =
      MvPolynomial.map (hahnResidueHom K) p := by
  rw [← mvPolynomialToRegularHahn_underlying]
  have hreg : 0 ≤ (mvPolynomialToRegularHahn p).1.orderTop := (mvPolynomialToRegularHahn p).2
  have hcoeff := mvPolynomialToRegularHahn_residue p
  rw [leadingCoeff_eq_coeff_zero_of_regular _ hreg (by rw [hcoeff]; exact hp),hcoeff]

lemma mvPolynomialToHahn_scalar_regular_product_leadingCoeff {K σ ι : Type} [Field K]
    (c : HahnSeries ℚ K) (s : Finset ι) (p : ι → MvPolynomial σ (nonnegativeHahnRing K)) (μ : ι → ℕ)
    (hp : ∀ i ∈ s, MvPolynomial.map (hahnResidueHom K) (p i) ≠ 0) :
    (mvPolynomialToHahn (MvPolynomial.C c *
      ∏ i ∈ s, MvPolynomial.map (nonnegativeHahnRing K).subtype (p i) ^ μ i)).leadingCoeff =
        MvPolynomial.C c.leadingCoeff * ∏ i ∈ s, MvPolynomial.map (hahnResidueHom K) (p i) ^ μ i := by
  classical
  let P := ∏ i ∈ s, p i ^ μ i
  have hP : MvPolynomial.map (hahnResidueHom K) P ≠ 0 := by
    simp only [P,map_prod,map_pow]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hp i hi))
  have hmap : (∏ i ∈ s, MvPolynomial.map (nonnegativeHahnRing K).subtype (p i) ^ μ i) =
      MvPolynomial.map (nonnegativeHahnRing K).subtype P := by simp only [P,map_prod,map_pow]
  rw [hmap,map_mul,mvPolynomialToHahn_C,HahnSeries.leadingCoeff_mul,
    hahnCoefficientMap_leadingCoeff MvPolynomial.C (MvPolynomial.C_injective σ K),
    regular_polynomial_hahn_leadingCoeff P hP]
  simp only [P,map_prod,map_pow]

end APSCounting893.Main
end Component_66

section Component_67

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma epsilonHAtPoint_rescale (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (z : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) (a : EpsilonAmbient) :
    epsilonHAtPoint F lambda (a • z) = MvPolynomial.C (a^2) * epsilonHAtPoint F lambda z := by
  have hsum : (∑ j : Fin (F.n+1), (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient) ((HahnSeries.C : ℂ →+* PuiseuxAmbient) (lambda j)) * (a*z (j.natAdd F.n).succ)) =
      a * ∑ j : Fin (F.n+1), (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient) ((HahnSeries.C : ℂ →+* PuiseuxAmbient) (lambda j)) * z (j.natAdd F.n).succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdiag : (∑ j : Fin (F.n+(F.n+1)),
      MvPolynomial.X (0 : Fin 2) ^ (j.val+1) * MvPolynomial.C ((a*z j.succ)^2)) =
      MvPolynomial.C (a^2) * ∑ j : Fin (F.n+(F.n+1)),
        MvPolynomial.X (0 : Fin 2) ^ (j.val+1) * MvPolynomial.C (z j.succ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_pow, map_mul]
    ring
  simp only [epsilonHAtPoint, Pi.smul_apply, smul_eq_mul]
  rw [hsum, hdiag]
  rw [mul_pow, map_mul]
  have hterm : (a*z 0) * (a * ∑ j, (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient) ((HahnSeries.C : ℂ →+* PuiseuxAmbient) (lambda j)) * z (j.natAdd F.n).succ) =
      a^2 * (z 0 * ∑ j, (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient) ((HahnSeries.C : ℂ →+* PuiseuxAmbient) (lambda j)) * z (j.natAdd F.n).succ) := by ring
  rw [hterm, map_mul]
  ring

noncomputable def regularHAtPoint (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (q : Fin (F.n+(F.n+1)+1) → nonnegativeHahnRing PuiseuxAmbient) :
    MvPolynomial (Fin 2) (nonnegativeHahnRing PuiseuxAmbient) := by
  classical
  exact MvPolynomial.X (1 : Fin 2) * MvPolynomial.C (σ := Fin 2) (q 0 ^ 2) -
    MvPolynomial.C (σ := Fin 2) (q 0 * ∑ j : Fin (F.n+1),
      hahnConstantLift PuiseuxAmbient (HahnSeries.C (lambda j)) * q (j.natAdd F.n).succ) +
    ∑ j : Fin (F.n+(F.n+1)), MvPolynomial.X (0 : Fin 2) ^ (j.val+1) * MvPolynomial.C (σ := Fin 2) (q j.succ ^ 2)

lemma regularHAtPoint_val (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (q : Fin (F.n+(F.n+1)+1) → nonnegativeHahnRing PuiseuxAmbient) :
    MvPolynomial.map (nonnegativeHahnRing PuiseuxAmbient).subtype (regularHAtPoint F lambda q) =
      epsilonHAtPoint F lambda (fun j => (q j).1) := by
  classical
  simp [regularHAtPoint,epsilonHAtPoint,hahnConstantLift,map_sum,map_mul,map_pow]
  left
  apply Finset.sum_congr rfl
  intro j hj
  rw [← map_mul]
  congr 1
  exact HahnSeries.C_mul_eq_smul

lemma regularHAtPoint_residue (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (q : Fin (F.n+(F.n+1)+1) → nonnegativeHahnRing PuiseuxAmbient) :
    MvPolynomial.map (hahnResidueHom PuiseuxAmbient) (regularHAtPoint F lambda q) =
      HAtPoint F lambda (fun j => (q j).1.coeff 0) := by
  classical
  simp [regularHAtPoint,HAtPoint,hahnResidue_constant,hahnResidueHom,hahnConstantLift,map_sum,map_mul,map_pow]
  left
  apply Finset.sum_congr rfl
  intro j hj
  rw [← map_mul]
  congr 1
  exact HahnSeries.C_mul_eq_smul

end APSCounting893.Main
end Component_67

section Component_68

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma epsilon_generic_product (F : RawMap) (c alpha : Affine ℂ F.n)
    (lambda : Affine ℂ (F.n+1)) (d : Fin (F.n+(F.n+1)) → ℕ)
    (hd : HomogenizingDegrees F c alpha d)
    (S : Finset (Fin (F.n+(F.n+1)) → EpsilonAmbient))
    (hS : (S : Set _) = {x | ∀ i, MvPolynomial.eval₂ epsilonAuxHom (Fin.cons 1 x)
      (perturbedEquation F c alpha d i) = 0}) :
    ∃ (μ : (Fin (F.n+(F.n+1)) → EpsilonAmbient) → ℕ) (b : EpsilonAmbient),
      b ≠ 0 ∧ (∀ x ∈ S, 0 < μ x) ∧
      epsilonResultantEvaluation (resultantFor F c alpha lambda d) =
        MvPolynomial.C b * ∏ x ∈ S, epsilonHAtPoint F lambda (Fin.cons 1 x) ^ μ x := by
  classical
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  letI : CharZero PuiseuxAmbient := charZero_of_injective_ringHom (HahnSeries.C : ℂ →+* PuiseuxAmbient).injective
  letI : IsAlgClosed EpsilonAmbient := HahnSeries.isAlgClosed_rat
  letI : CharZero EpsilonAmbient := charZero_of_injective_ringHom (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient).injective
  let G : Fin (F.n+(F.n+1)) → MvPolynomial (Fin (F.n+(F.n+1)+1)) EpsilonAmbient :=
    fun i => MvPolynomial.map epsilonAuxHom (perturbedEquation F c alpha d i)
  have hG (i : Fin (F.n+(F.n+1))) : (G i).IsHomogeneous (d i) :=
    epsilon_perturbed_homogeneous F c alpha d hd i
  have hnoInf (q : Fin (F.n+(F.n+1)+1) → EpsilonAmbient) (hq : q 0 = 0)
      (hroot : ∀ i, MvPolynomial.eval q (G i) = 0) : q = 0 := by
    apply epsilon_perturbed_no_infinity F c alpha d hd q hq
    simpa only [G,MvPolynomial.eval_map] using hroot
  have hS' : (S : Set _) = {x | ∀ i, MvPolynomial.eval (Fin.cons 1 x) (G i) = 0} := by
    simpa only [G,MvPolynomial.eval_map] using hS
  obtain ⟨μ,b,hb,hμ,hprod⟩ := homogeneousResultant_quadratic_product_over_ring d
    (fun i => (hd i).1) G hG hnoInf S hS'
  refine ⟨μ,b,hb,hμ,?_⟩
  have hh := hprod (MvPolynomial (Fin 2) EpsilonAmbient) MvPolynomial.C
    (MvPolynomial.map epsilonResultantEvaluation (HForm F lambda)) ((HForm_homogeneous F lambda).map _)
  have he : (fun i => MvPolynomial.map epsilonResultantEvaluation
      (Fin.lastCases (HForm F lambda) (perturbedEquation F c alpha d) i)) =
      Fin.lastCases (MvPolynomial.map epsilonResultantEvaluation (HForm F lambda))
        (fun i => MvPolynomial.map MvPolynomial.C (G i)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
    · simpa only [Fin.lastCases_castSucc,G] using epsilonResultantEvaluation_perturbed F c alpha d j
  unfold resultantFor
  rw [homogeneousResultant_map,he]
  rw [hh]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  rw [epsilonHForm_evaluation]

end APSCounting893.Main
end Component_68

section Component_69

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma coefficientIn_HAtPoint_zero (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) :
    coefficientIn (0 : Fin 2) 0 (HAtPoint F lambda z) =
      X 1 * C (z 0 ^ 2) - C (z 0 * ∑ j : Fin (F.n + 1),
        HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) := by
  classical
  simp [HAtPoint, coefficientIn_add, coefficientIn_sub, coefficientIn_sum,
    coefficientIn_zero_mul, coefficientIn_zero_C, coefficientIn_zero_X, coefficientIn_zero_pow]

lemma trailing_HAtPoint_affine (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) (hz : z 0 ≠ 0) :
    trailingCoefficient (0 : Fin 2) (HAtPoint F lambda z) =
      X 1 * C (z 0 ^ 2) - C (z 0 * ∑ j : Fin (F.n + 1),
        HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) := by
  have hnonzero : coefficientIn (0 : Fin 2) 0 (HAtPoint F lambda z) ≠ 0 := by
    rw [coefficientIn_HAtPoint_zero]
    intro h
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)) h
    rw [mul_comm (X 1) (C (z 0 ^ 2)), coeff_sub, coeff_C_mul] at hc
    have hm : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 :=
      Ne.symm (Finsupp.single_ne_zero.mpr Nat.one_ne_zero)
    simp only [coeff_X_same, mul_one, coeff_C, if_neg hm, sub_zero, coeff_zero] at hc
    exact pow_ne_zero 2 hz hc
  rw [trailingCoefficient_eq_of_zero_coeff _ _ hnonzero, coefficientIn_HAtPoint_zero]

lemma trailing_HAtPoint_chart_one (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) (hz : z 0 = 1) :
    trailingCoefficient (0 : Fin 2) (HAtPoint F lambda z) =
      X 1 - C (∑ j : Fin (F.n + 1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) := by
  rw [trailing_HAtPoint_affine F lambda z (by rw [hz]; exact one_ne_zero), hz]
  simp

lemma trailingCoefficient_self_X {K : Type} [CommRing K] [Nontrivial K] {n : ℕ}
    (v : Fin n) : trailingCoefficient v (X v : MvPolynomial (Fin n) K) = 1 := by
  classical
  have hcoef : coefficientIn v 1 (X v : MvPolynomial (Fin n) K) = 1 := by
    change coefficientIn v 1 (monomial (Finsupp.single v 1) 1) = _
    rw [coefficientIn_monomial]
    simp
  have he := trailingCoefficient_eq_of_min v (X v : MvPolynomial (Fin n) K) 1
    (by rw [hcoef]; exact one_ne_zero) (fun j hj => by
      have hj0 : j = 0 := by omega
      subst j
      simp [coefficientIn_zero_X])
  exact he.trans hcoef

end APSCounting893.Main
end Component_69

section Component_70

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma coefficientIn_zero_diagonal {K : Type} [CommRing K] {n N : ℕ}
    (v : Fin n) (z : Fin N → K) :
    coefficientIn v 0 (∑ j : Fin N, X v ^ (j.val + 1) * C (z j ^ 2)) = 0 := by
  classical
  simp [coefficientIn_sum, coefficientIn_zero_mul, coefficientIn_zero_pow,
    coefficientIn_zero_X, coefficientIn_zero_C]

lemma diagonal_form_cons {K : Type} [CommRing K] {n N : ℕ}
    (v : Fin n) (z : Fin (N + 1) → K) :
    (∑ j : Fin (N + 1), X v ^ (j.val + 1) * C (z j ^ 2)) =
      X v * (C (z 0 ^ 2) + ∑ j : Fin N, X v ^ (j.val + 1) * C (z j.succ ^ 2)) := by
  classical
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, zero_add, pow_one, Fin.val_succ]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_succ]
  ring

lemma trailing_diagonal_constant {K : Type} [Field K] {n N : ℕ}
    (v : Fin n) (z : Fin N → K) (hz : z ≠ 0) :
    ∃ c : K, c ≠ 0 ∧
      trailingCoefficient v (∑ j : Fin N, X v ^ (j.val + 1) * C (z j ^ 2)) = C c := by
  classical
  induction N with
  | zero =>
    exact False.elim (hz (funext (fun j => Fin.elim0 j)))
  | succ N ih =>
    rw [diagonal_form_cons, trailingCoefficient_mul, trailingCoefficient_self_X, one_mul]
    by_cases hhead : z 0 = 0
    · have htail : (fun j : Fin N => z j.succ) ≠ 0 := by
        intro h
        apply hz
        funext j
        exact Fin.cases hhead (fun k => congrFun h k) j
      obtain ⟨c, hc, hct⟩ := ih (fun j => z j.succ) htail
      refine ⟨c, hc, ?_⟩
      simpa only [hhead, zero_pow (by decide : 2 ≠ 0), map_zero, zero_add] using hct
    · have hc : z 0 ^ 2 ≠ 0 := pow_ne_zero 2 hhead
      refine ⟨z 0 ^ 2, hc, ?_⟩
      have hcoef : coefficientIn v 0
          (C (z 0 ^ 2) + ∑ j : Fin N, X v ^ (j.val + 1) * C (z j.succ ^ 2)) = C (z 0 ^ 2) := by
        rw [coefficientIn_add, coefficientIn_zero_C, coefficientIn_zero_diagonal, add_zero]
      have hcoeff : coefficientIn v 0
          (C (z 0 ^ 2) + ∑ j : Fin N, X v ^ (j.val + 1) * C (z j.succ ^ 2)) ≠ 0 := by
        rw [hcoef]
        intro hzC
        have hh := congrArg (MvPolynomial.coeff (0 : Fin n →₀ ℕ)) hzC
        apply hc
        simpa only [coeff_C, if_pos rfl, ite_true, coeff_zero] using hh
      rw [trailingCoefficient_eq_of_zero_coeff _ _ hcoeff, hcoef]

lemma trailing_HAtPoint_infinity (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) (hz : z ≠ 0) (h0 : z 0 = 0) :
    ∃ c : PuiseuxAmbient, c ≠ 0 ∧ trailingCoefficient (0 : Fin 2) (HAtPoint F lambda z) = C c := by
  have htail : (fun j : Fin (F.n + (F.n + 1)) => z j.succ) ≠ 0 := by
    intro h
    apply hz
    funext j
    exact Fin.cases h0 (fun k => congrFun h k) j
  obtain ⟨c, hc, hct⟩ := trailing_diagonal_constant (0 : Fin 2) (fun j => z j.succ) htail
  refine ⟨c, hc, ?_⟩
  simpa only [HAtPoint, h0, zero_pow (by decide : 2 ≠ 0), map_zero, mul_zero, zero_mul,
    sub_zero, sub_self, zero_add] using hct

end APSCounting893.Main
end Component_70

section Component_71

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma HAtPoint_ne_zero (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (z : Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) (hz : z ≠ 0) : HAtPoint F lambda z ≠ 0 := by
  intro hzero
  by_cases h0 : z 0 = 0
  · obtain ⟨c,hc,hh⟩ := trailing_HAtPoint_infinity F lambda z hz h0
    rw [hzero] at hh
    have hc0 : c = 0 := by
      apply MvPolynomial.C_injective (Fin 2) PuiseuxAmbient
      simpa only [trailingCoefficient,Finset.not_nonempty_empty,not_false_eq_true,
        dif_neg, MvPolynomial.support_zero,MvPolynomial.C_0] using hh.symm
    exact hc hc0
  · have hh := congrArg (coefficientIn (0 : Fin 2) 0) hzero
    rw [coefficientIn_HAtPoint_zero] at hh
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)) hh
    rw [mul_comm (MvPolynomial.X 1) (MvPolynomial.C (z 0 ^ 2)),coeff_sub,coeff_C_mul] at hc
    have hm : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 :=
      Ne.symm (Finsupp.single_ne_zero.mpr Nat.one_ne_zero)
    simp [hm,coefficientIn, MvPolynomial.coeff_sum, MvPolynomial.coeff_C] at hc
    exact h0 hc

end APSCounting893.Main
end Component_71

section Component_72

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma epsilon_product_regular_rescaling {ι : Type} (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (s : Finset ι) (v Q : ι → Fin (F.n+(F.n+1)+1) → EpsilonAmbient)
    (a : ι → EpsilonAmbient) (ha : ∀ x ∈ s, a x ≠ 0)
    (hQ : ∀ x ∈ s, Q x = a x • v x) (μ : ι → ℕ) (b : EpsilonAmbient) (hb : b ≠ 0) :
    ∃ b' : EpsilonAmbient, b' ≠ 0 ∧
      MvPolynomial.C b * ∏ x ∈ s, epsilonHAtPoint F lambda (v x)^μ x =
        MvPolynomial.C b' * ∏ x ∈ s, epsilonHAtPoint F lambda (Q x)^μ x := by
  classical
  refine ⟨b * ∏ x ∈ s, ((a x)⁻¹ ^ 2)^μ x,?_,?_⟩
  · exact mul_ne_zero hb (Finset.prod_ne_zero_iff.mpr (fun x hx => pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero (ha x hx)))))
  · have hv (x : ι) (hx : x ∈ s) : v x = (a x)⁻¹ • Q x := by
      rw [hQ x hx,inv_smul_smul₀ (ha x hx)]
    calc
      _ = MvPolynomial.C b * ∏ x ∈ s,
          (MvPolynomial.C ((a x)⁻¹^2) * epsilonHAtPoint F lambda (Q x)) ^ μ x := by
        congr 1
        apply Finset.prod_congr rfl
        intro x hx
        rw [hv x hx,epsilonHAtPoint_rescale]
      _ = _ := by
        simp only [mul_pow,Finset.prod_mul_distrib,← map_pow,← map_prod]
        rw [map_mul,mul_assoc]

lemma epsilon_regular_product_leadingCoeff {ι : Type} (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (s : Finset ι) (Q : ι → Fin (F.n+(F.n+1)+1) → EpsilonAmbient)
    (hreg : ∀ x j, 0 ≤ (Q x j).orderTop)
    (hunit : ∀ x ∈ s, ∃ j, (Q x j).orderTop = 0)
    (μ : ι → ℕ) (b : EpsilonAmbient) :
    (mvPolynomialToHahn (MvPolynomial.C b * ∏ x ∈ s, epsilonHAtPoint F lambda (Q x)^μ x)).leadingCoeff =
      MvPolynomial.C b.leadingCoeff * ∏ x ∈ s,
        HAtPoint F lambda (fun j => (Q x j).coeff 0)^μ x := by
  classical
  let q : ι → Fin (F.n+(F.n+1)+1) → nonnegativeHahnRing PuiseuxAmbient :=
    fun x j => ⟨Q x j,hreg x j⟩
  have hne (x : ι) (hx : x ∈ s) : (fun j => (Q x j).coeff 0) ≠ 0 := by
    obtain ⟨j,hj⟩ := hunit x hx
    intro hh
    have hcoeff : (Q x j).coeff 0 ≠ 0 := by
      exact HahnSeries.coeff_orderTop_ne hj
    exact hcoeff (congrFun hh j)
  have hh := mvPolynomialToHahn_scalar_regular_product_leadingCoeff b s
    (fun x => regularHAtPoint F lambda (q x)) μ (by
      intro x hx
      rw [regularHAtPoint_residue]
      exact HAtPoint_ne_zero F lambda _ (hne x hx))
  simpa only [regularHAtPoint_val,regularHAtPoint_residue,q] using hh

end APSCounting893.Main
end Component_72

section Component_73
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main
lemma HAtPoint_rescale (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (z : Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) (a : PuiseuxAmbient) :
    HAtPoint F lambda (a • z) = MvPolynomial.C (a^2) * HAtPoint F lambda z := by
  have hsum : (∑ j : Fin (F.n+1), HahnSeries.C (lambda j) * (a*z (j.natAdd F.n).succ)) =
      a * ∑ j : Fin (F.n+1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdiag : (∑ j : Fin (F.n+(F.n+1)),
      MvPolynomial.X (0 : Fin 2) ^ (j.val+1) * MvPolynomial.C ((a*z j.succ)^2)) =
      MvPolynomial.C (a^2) * ∑ j : Fin (F.n+(F.n+1)),
        MvPolynomial.X (0 : Fin 2) ^ (j.val+1) * MvPolynomial.C (z j.succ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_pow, map_mul]
    ring
  simp only [HAtPoint, Pi.smul_apply, smul_eq_mul]
  rw [hsum, hdiag]
  rw [mul_pow, map_mul]
  have hterm : (a*z 0) * (a * ∑ j, HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) =
      a^2 * (z 0 * ∑ j, HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) := by ring
  rw [hterm, map_mul]
  ring

lemma HAtPoint_projective_product (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (S : Finset (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient))
    (mu : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → ℕ)
    (reps : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient))
    (hreps : ∀ z ∈ S, ∃ a : PuiseuxAmbient, a ≠ 0 ∧ reps z = a • z) :
    ∃ c : PuiseuxAmbient, c ≠ 0 ∧
      (∏ z ∈ S, HAtPoint F lambda (reps z) ^ mu z) =
        MvPolynomial.C c * ∏ z ∈ S, HAtPoint F lambda z ^ mu z := by
  classical
  have hex : ∀ z, ∃ a : PuiseuxAmbient, a ≠ 0 ∧ (z ∈ S → reps z = a • z) := by
    intro z
    by_cases hz : z ∈ S
    · obtain ⟨a, ha, he⟩ := hreps z hz
      exact ⟨a, ha, fun _ => he⟩
    · exact ⟨1, one_ne_zero, fun h => False.elim (hz h)⟩
  choose a ha using hex
  refine ⟨∏ z ∈ S, (a z ^ 2) ^ mu z,
    Finset.prod_ne_zero_iff.mpr (fun z hz => pow_ne_zero _ (pow_ne_zero _ (ha z).1)), ?_⟩
  calc
    ∏ z ∈ S, HAtPoint F lambda (reps z) ^ mu z =
        ∏ z ∈ S, (MvPolynomial.C (a z ^ 2) * HAtPoint F lambda z) ^ mu z := by
      apply Finset.prod_congr rfl
      intro z hz
      rw [(ha z).2 hz, HAtPoint_rescale]
    _ = _ := by
      simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]


end APSCounting893.Main
end Component_73

section Component_74

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma HAtPoint_indexed_rescaling_product {ι : Type} (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (s : Finset ι) (v Q : ι → Fin (F.n+(F.n+1)+1) → PuiseuxAmbient)
    (a : ι → PuiseuxAmbient) (ha : ∀ x ∈ s, a x ≠ 0)
    (hQ : ∀ x ∈ s, Q x = a x • v x) (μ : ι → ℕ) (b : PuiseuxAmbient) (hb : b ≠ 0) :
    ∃ b' : PuiseuxAmbient, b' ≠ 0 ∧
      MvPolynomial.C b * ∏ x ∈ s, HAtPoint F lambda (v x)^μ x =
        MvPolynomial.C b' * ∏ x ∈ s, HAtPoint F lambda (Q x)^μ x := by
  classical
  refine ⟨b * ∏ x ∈ s, ((a x)⁻¹ ^ 2)^μ x,?_,?_⟩
  · exact mul_ne_zero hb (Finset.prod_ne_zero_iff.mpr (fun x hx => pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero (ha x hx)))))
  · have hv (x : ι) (hx : x ∈ s) : v x = (a x)⁻¹ • Q x := by
      rw [hQ x hx,inv_smul_smul₀ (ha x hx)]
    calc
      _ = MvPolynomial.C b * ∏ x ∈ s,
          (MvPolynomial.C ((a x)⁻¹^2) * HAtPoint F lambda (Q x)) ^ μ x := by
        congr 1
        apply Finset.prod_congr rfl
        intro x hx
        rw [hv x hx,HAtPoint_rescale]
      _ = _ := by
        simp only [mul_pow,Finset.prod_mul_distrib,← map_pow,← map_prod]
        rw [map_mul,mul_assoc]


end APSCounting893.Main
end Component_74

section Component_75

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

open Classical in
lemma positive_product_regroup {α β R : Type} [CommMonoid R]
    (s : Finset α) (r : α → β) (mu : α → ℕ) (hmu : ∀ z ∈ s, 0 < mu z) (f : β → R) :
    ∃ M : β → ℕ, (∀ y ∈ s.image r, 0 < M y) ∧
      (∏ z ∈ s, f (r z) ^ mu z) = ∏ y ∈ s.image r, f y ^ M y := by
  classical
  let M : β → ℕ := fun y => ∑ z ∈ s.filter (fun z => r z = y), mu z
  refine ⟨M, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact lt_of_lt_of_le (hmu z hz) (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨hz, rfl⟩))
  · symm
    calc
      ∏ y ∈ s.image r, f y ^ M y =
          ∏ y ∈ s.image r, ∏ z ∈ s.filter (fun z => r z = y), f (r z) ^ mu z := by
        apply Finset.prod_congr rfl
        intro y hy
        rw [show M y = ∑ z ∈ s.filter (fun z => r z = y), mu z from rfl,
          ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
      _ = ∏ z ∈ s, f (r z) ^ mu z :=
        Finset.prod_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem r hz) _

end APSCounting893.Main
end Component_75

section Component_76

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma epsilon_center_product (F : RawMap) (c alpha : Affine ℂ F.n)
    (lambda : Affine ℂ (F.n+1)) (d : Fin (F.n+(F.n+1)) → ℕ)
    (hd : HomogenizingDegrees F c alpha d)
    (S : Finset (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient))
    (hS : (S : Set _) = epsilonLimitSet F c alpha d) :
    S.Nonempty ∧ ∃ (μ : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → ℕ) (b : PuiseuxAmbient),
      b ≠ 0 ∧ (∀ z ∈ S, 0 < μ z) ∧
      trailingEpsilonResultant (resultantFor F c alpha lambda d) =
        MvPolynomial.C b * ∏ z ∈ S, HAtPoint F lambda z ^ μ z := by
  classical
  letI : DecidableEq (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) := Classical.decEq _
  obtain ⟨A,hAne,hA,Q,a,ha,hQ,hreg,hunit,himage⟩ := epsilon_limit_data F c alpha d hd
  obtain ⟨μ,b,hb,hμ,hprod⟩ := epsilon_generic_product F c alpha lambda d hd A hA
  let v : A → Fin (F.n+(F.n+1)+1) → EpsilonAmbient := fun x => Fin.cons 1 x.1
  have hprod' : epsilonResultantEvaluation (resultantFor F c alpha lambda d) =
      MvPolynomial.C b * ∏ x : A, epsilonHAtPoint F lambda (v x)^μ x.1 := by
    have hattach : A.attach = Finset.univ := by ext x; simp
    have he := Finset.prod_attach A (fun x => epsilonHAtPoint F lambda (Fin.cons 1 x)^μ x)
    rw [hattach] at he
    exact hprod.trans (congrArg (fun p => MvPolynomial.C b * p) he.symm)
  obtain ⟨b',hb',hprodQ⟩ := epsilon_product_regular_rescaling F lambda Finset.univ v Q a
    (fun x _ => ha x) (fun x _ => hQ x) (fun x => μ x.1) b hb
  let r : A → Fin (F.n+(F.n+1)+1) → PuiseuxAmbient := fun x j => (Q x j).coeff 0
  let center : A → Fin (F.n+(F.n+1)+1) → PuiseuxAmbient := fun x => projectiveRepresentative (r x)
  have hr (x : A) : r x ≠ 0 := by
    obtain ⟨j,hj⟩ := hunit x
    intro hh
    exact HahnSeries.coeff_orderTop_ne hj (congrFun hh j)
  have hex (x : A) : ∃ β : PuiseuxAmbient, β ≠ 0 ∧ center x = β • r x :=
    projectiveRepresentative_rescaling (r x) (hr x)
  choose β hβ hcenter using hex
  have htc : trailingEpsilonResultant (resultantFor F c alpha lambda d) =
      MvPolynomial.C b'.leadingCoeff * ∏ x : A, HAtPoint F lambda (r x)^μ x.1 := by
    rw [← epsilonResultantEvaluation_leadingCoeff,hprod',hprodQ]
    exact epsilon_regular_product_leadingCoeff F lambda Finset.univ Q
      (fun x j => (hreg x j).2) (fun x _ => hunit x) (fun x => μ x.1) b'
  obtain ⟨b'',hb'',hprodCenter⟩ := HAtPoint_indexed_rescaling_product F lambda Finset.univ r center β
    (fun x _ => hβ x) (fun x _ => hcenter x) (fun x => μ x.1) b'.leadingCoeff
    (HahnSeries.leadingCoeff_ne_zero.mpr hb')
  have hImageFin : @Finset.image A (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient)
      (Classical.decEq _) center Finset.univ = S := by
    apply Finset.coe_injective
    rw [Finset.coe_image,Finset.coe_univ,Set.image_univ,hS,himage]
  have hmu (x : A) (_ : x ∈ Finset.univ) : 0 < μ x.1 := hμ x.1 x.2
  obtain ⟨M,hM,hregroup⟩ := positive_product_regroup Finset.univ center (fun x => μ x.1) hmu
    (fun z => HAtPoint F lambda z)
  have hM' : ∀ z ∈ S, 0 < M z := fun z hz => hM z (hImageFin.symm ▸ hz)
  have hregroup' : (∏ z : A, HAtPoint F lambda (center z)^μ z.1) =
      ∏ y ∈ S, HAtPoint F lambda y ^ M y := hregroup.trans
        (congrArg (fun t => ∏ y ∈ t, HAtPoint F lambda y ^ M y) hImageFin)
  have hSne : S.Nonempty := by
    obtain ⟨x,hx⟩ := hAne
    refine ⟨center ⟨x,hx⟩,?_⟩
    change center ⟨x,hx⟩ ∈ (S : Set _)
    rw [hS,himage]
    exact ⟨⟨x,hx⟩,rfl⟩
  refine ⟨hSne,M,b'',hb'',hM',?_⟩
  rw [htc,hprodCenter,hregroup']

end APSCounting893.Main
end Component_76

section Component_77

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma HAtPoint_absorb_scalar (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (S : Finset (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient)) (hne : S.Nonempty)
    (mu : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → ℕ)
    (hmu : ∀ z ∈ S, 0 < mu z) (c : PuiseuxAmbient) (hc : c ≠ 0) :
    ∃ repr : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) →
      (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient),
      (∀ z ∈ S, ∃ a : PuiseuxAmbient, a ≠ 0 ∧ repr z = a • z) ∧
      (∏ z ∈ S, HAtPoint F lambda (repr z)^mu z) =
        MvPolynomial.C c * ∏ z ∈ S, HAtPoint F lambda z ^ mu z := by
  classical
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  obtain ⟨z0,hz0⟩ := hne
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq c (show 0 < 2*mu z0 from Nat.mul_pos (by decide) (hmu z0 hz0))
  have hane : a ≠ 0 := by
    intro h
    rw [h,zero_pow (Nat.ne_of_gt (Nat.mul_pos (by decide) (hmu z0 hz0)))] at ha
    exact hc ha.symm
  let repr := fun z => (if z = z0 then a else 1) • z
  refine ⟨repr,?_,?_⟩
  · intro z hz
    refine ⟨if z = z0 then a else 1,?_,rfl⟩
    split_ifs
    · exact hane
    · exact one_ne_zero
  · calc
      (∏ z ∈ S, HAtPoint F lambda (repr z)^mu z) =
          ∏ z ∈ S, (MvPolynomial.C (((if z=z0 then a else 1)^2)^mu z) * HAtPoint F lambda z ^ mu z) := by
        apply Finset.prod_congr rfl
        intro z hz
        rw [show repr z = (if z=z0 then a else 1) • z from rfl,HAtPoint_rescale,mul_pow]
        simp only [map_pow]
      _ = (∏ z ∈ S, MvPolynomial.C (((if z=z0 then a else 1)^2)^mu z)) *
          ∏ z ∈ S, HAtPoint F lambda z ^ mu z := Finset.prod_mul_distrib
      _ = _ := by
        congr 1
        rw [← map_prod]
        congr 1
        have he : (fun z => ((if z=z0 then a else 1)^2)^mu z) =
            fun z => if z=z0 then a^(2*mu z0) else 1 := by
          funext z
          split_ifs with hz
          · subst z; rw [← pow_mul]
          · simp
        rw [he,Finset.prod_ite_eq_of_mem' S z0 (fun _ => a^(2*mu z0)) hz0,ha]

end APSCounting893.Main
end Component_77

section Component_78
set_option autoImplicit false
open APSCounting893.Main
theorem solution
    (F : ReducedMap) (D : LineData F) (lambda : Affine ℂ (F.n+1))
    (hsep : Set.InjOn (separatingForm lambda) (zeroFiber F D.c ∪ {0}))
    (degrees : Fin (F.n+(F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees)
    (S : Finset (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient))
    (hS : (S : Set _) = epsilonLimitSet F D.c D.alpha degrees) :
    ∃ (mu : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → ℕ)
      (representatives : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) →
        (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient)),
      (∀ z ∈ S, 0 < mu z ∧ ∃ a : PuiseuxAmbient, a ≠ 0 ∧ representatives z = a • z) ∧
      trailingEpsilonResultant (resultantFor F D.c D.alpha lambda degrees) =
        ∏ z ∈ S, HAtPoint F lambda (representatives z) ^ mu z  := by
  obtain ⟨hne,mu,b,hb,hmu,hprod⟩ := epsilon_center_product F D.c D.alpha lambda degrees hdegrees S hS
  obtain ⟨repr,hrepr,heq⟩ := HAtPoint_absorb_scalar F lambda S hne mu hmu b hb
  exact ⟨mu,repr,fun z hz => ⟨hmu z hz,hrepr z hz⟩,hprod.trans heq.symm⟩
end Component_78

open APSCounting893.Main

