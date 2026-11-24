-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:06.644319+00:00
-- url     : https://prove2.me/theorems/2cf59f95-2bbd-4833-937a-7860e8aad149
-- title:
--   Height Objects
-- statement:
--   Definitions and structural lemmas for Height Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
abbrev blockIdx (n : ι → ℕ) : ι → Type := fun k ↦ Fin (n k + 1)
def flatCone {F : Type*} (z : Cone n F) : Coord n → F := fun p ↦ z p.1 p.2
def unflatCone {F : Type*} (w : Coord n → F) : Cone n F := fun k i ↦ w ⟨k, i⟩
@[simp] theorem unflatCone_flatCone {F : Type*} (z : Cone n F) : unflatCone (flatCone z) = z := rfl
@[simp] theorem flatCone_unflatCone {F : Type*} (w : Coord n → F) : flatCone (unflatCone w) = w := rfl
theorem blockNonzero_unflatCone_iff {F : Type*} [Zero F] (w : Coord n → F) :
    BlockNonzero (unflatCone w) ↔ ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 :=
  forall_congr' fun _ ↦ Function.ne_iff
variable [Fintype ι] [DecidableEq ι]
theorem weight_coordDeg_apply (d : Coord n →₀ ℕ) (k : ι) :
    Finsupp.weight (coordDeg n) d k = ∑ i, d ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; exact zero_smul _ _), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [coordDeg]
  · intro j _ hj
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp [coordDeg, Pi.single_apply, Ne.symm hj]
  · simp
theorem geoMultiHomog_iff (f : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) :
    Geo.IsMultiHomog (ι := blockIdx n) f a ↔ IsWeightedHomogeneous (coordDeg n) f a := by
  constructor
  · intro h d hd
    funext k
    rw [weight_coordDeg_apply]
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    rw [← weight_coordDeg_apply, h (mem_support_iff.mp hm)]
theorem ArithVariety.isMultiProjPrime (P : ArithVariety n) :
    Geo.IsMultiProjPrime (ι := blockIdx n) P.ideal := by
  classical
  refine ⟨P.isPrime, ⟨{f | f ∈ P.ideal ∧ ∃ a, Geo.IsMultiHomog (ι := blockIdx n) f a},
    fun f hf ↦ hf.2, le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.mpr fun f hf ↦ hf.1)⟩, P.relevant⟩
  rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  refine Ideal.sum_mem _ fun m _ ↦ Ideal.subset_span ⟨P.homogeneous f hf m, m, ?_⟩
  exact (geoMultiHomog_iff _ m).mpr (weightedHomogeneousComponent_isWeightedHomogeneous m f)
namespace HermLine
open Classical in

def toGeo (A : HermLine n) : Geo.HermLine (blockIdx n) where
  a := A.deg
  h w := if BlockNonzero (unflatCone w) then A.metric (unflatCone w) else 0
  pos w hw := by
    have hw' : BlockNonzero (unflatCone w) := (blockNonzero_unflatCone_iff w).mpr hw
    rw [if_pos hw']
    exact A.metric_pos _ hw'
  smul c w hc := by
    have e : unflatCone (fun p : Coord n ↦ c p.1 * w p) = fun k i ↦ c k * unflatCone w k i := rfl
    by_cases hw : BlockNonzero (unflatCone w)
    · have hcw : BlockNonzero (unflatCone (fun p : Coord n ↦ c p.1 * w p)) := by
        intro k hk
        apply hw k
        funext i
        have := congrFun hk i
        rw [e] at this
        exact (mul_eq_zero.mp this).resolve_left (hc k)
      rw [if_pos hw, if_pos hcw, e, A.metric_smul c _ hc hw]
    · have hcw : ¬ BlockNonzero (unflatCone (fun p : Coord n ↦ c p.1 * w p)) := by
        intro h
        apply hw
        intro k hk
        apply h k
        funext i
        rw [e]
        simp [congrFun hk i]
      rw [if_neg hw, if_neg hcw, mul_zero]
theorem toGeo_h_of_blockNonzero (A : HermLine n) {w : Coord n → ℂ}
    (hw : BlockNonzero (unflatCone w)) : A.toGeo.h w = A.metric (unflatCone w) := by
  simp only [toGeo, if_pos hw]
theorem isSmoothHerm_toGeo (A : HermLine n) : Geo.IsSmoothHerm A.toGeo := by
  have hu : ContDiff ℝ ∞ (fun w : Coord n → ℂ ↦ unflatCone w) :=
    contDiff_pi.2 fun k ↦ contDiff_pi.2 fun i ↦ contDiff_apply ℝ ℂ (⟨k, i⟩ : Coord n)
  have hm : ContDiffOn ℝ ∞ (fun w : Coord n → ℂ ↦ A.metric (unflatCone w))
      {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} :=
    A.metric_smooth.comp hu.contDiffOn fun w hw ↦ (blockNonzero_unflatCone_iff w).mpr hw
  refine hm.congr fun w hw ↦ ?_
  exact A.toGeo_h_of_blockNonzero ((blockNonzero_unflatCone_iff w).mpr hw)
end HermLine
namespace IntegralSection
variable {P : ArithVariety n} {a : ι → ℤ}
end IntegralSection
def orbitIdeal (x : Cone n (AlgebraicClosure ℚ)) : Ideal (MvPolynomial (Coord n) ℤ) :=
  Geo.mCoordIdeal (ι := blockIdx n) (flatCone x)
theorem chartMonomial_notMem_orbitIdeal (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ) :
    chartMonomial c d ∉ orbitIdeal x := by
  intro h
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at h
  rw [chartMonomial, map_prod] at h
  refine (Finset.prod_ne_zero_iff.mpr fun k _ ↦ ?_) h
  rw [map_pow, Geo.mConeMap, aeval_X]
  exact pow_ne_zero _ (mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _))
theorem isSectionOn_chartMonomial (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ)
    (hd : ∀ k, A.deg k = d k) :
    Geo.IsSectionOn (orbitIdeal x) A.toGeo (chartMonomial c d) :=
  ⟨d, hd, (geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d),
    chartMonomial_notMem_orbitIdeal x c hc d⟩
def samplePoint : Cone (fun _ : Unit ↦ 1) (AlgebraicClosure ℚ) := fun _ ↦ ![1, 2]
example : Geo.IsSectionOn (orbitIdeal samplePoint) (HermLine.standard _).toGeo
    (chartMonomial (fun _ ↦ 0) 1) :=
  isSectionOn_chartMonomial _ _ _ (fun _ ↦ by simp [samplePoint]) 1 (fun _ ↦ rfl)
example : Geo.IsMultiProjPrime (ι := blockIdx (fun _ : Unit ↦ 1)) (ArithVariety.whole _).ideal ∧
    Geo.IsSmoothHerm (HermLine.standard (fun _ : Unit ↦ 1)).toGeo :=
  ⟨ArithVariety.isMultiProjPrime _, HermLine.isSmoothHerm_toGeo _⟩
end
end GroundTheory.Heights₂.Heights


