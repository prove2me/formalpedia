-- Prove2me | Definitions.Def_OAIQ368Chrom006
-- name    : OAIQ368Chrom006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:10:25.356431+00:00
-- url     : https://prove2.me/theorems/a2524194-a2a0-4179-ba1f-d83883df1a12
-- title:
--   Definitions bundle OAIQ368Chrom006 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 121 declarations of OpenAI's Lean: 58 definitions and 63 theorems. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.halfspacePolynomialCoefficientsRing`, `OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit`, `OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidTorus_4`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorus`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRat`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_1`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_10`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_11`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_12`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_13`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_14`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_2`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_3`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_4`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_5`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_6`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_7`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_9`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorus_3`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorus_4`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorus_6`, `OAI.ElementaryPositivity.QuantumTorus.laurentCompletionFaithfulNonUnitalNonAssocSemiring`, `OAI.ElementaryPositivity.QuantumTorus.laurentCompletionFaithfulRing`, `OAI.ElementaryPositivity.QuantumTorus.laurentRay`, `OAI.ElementaryPositivity.QuantumTorus.laurentRayHom`, `OAI.ElementaryPositivity.QuantumTorus.laurentRayNonUnitalNonAssocSemiring`, `OAI.ElementaryPositivity.QuantumTorus.laurentRayRing`, `OAI.ElementaryPositivity.QuantumTorus.laurentRegrade`, `OAI.ElementaryPositivity.QuantumTorus.laurentRegradeFamily`, `OAI.ElementaryPositivity.QuantumTorus.laurentRegradeHom`, `OAI.ElementaryPositivity.QuantumTorus.lineRayData`, `OAI.ElementaryPositivity.QuantumTorus.mutatedLaurent`, `OAI.ElementaryPositivity.QuantumTorus.mutatedPathIndependentPureRing`, `OAI.ElementaryPositivity.QuantumTorus.mutatedPathIndependentRing`, `OAI.ElementaryPositivity.QuantumTorus.mutatedPureLineRing`, `OAI.ElementaryPositivity.QuantumTorus.mutationCompletion`, `OAI.ElementaryPositivity.QuantumTorus.mutationIncomingProbesRing`, `OAI.ElementaryPositivity.QuantumTorus.mutationLaurentCompletionRing`, `OAI.ElementaryPositivity.QuantumTorus.mutationTorusPush` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_HalfspacePolynomialCoefficients`, `Chromatic_GradedAlgebra_KernelTraceLog`, `Chromatic_GradedAlgebra_LaurentDeshear`, `Chromatic_GradedAlgebra_LaurentRegrade`, `Chromatic_GradedAlgebra_MutatedPureFace`, `Chromatic_GradedAlgebra_MutationCoordinates`, `Chromatic_GradedAlgebra_MutationOrientedCompatibility`, `Chromatic_GradedAlgebra_NonpHomogenize`, `Chromatic_GradedAlgebra_NonpRegrade`, `Chromatic_GradedAlgebra_NonpRegradeFaithful`, `Chromatic_GradedAlgebra_RationalLaurentScalars`, `Chromatic_GradedAlgebra_RationalPureCoefficients`, `Chromatic_GradedAlgebra_RationalRegrade`, `Chromatic_GradedAlgebra_RegradeLog`, `Chromatic_QuantumTorus_MutatedNegativeCharts`, `Chromatic_QuantumTorus_MutatedSystemIdentification`, `Chromatic_Walls_AllOrderSectionLine`, `Chromatic_Walls_ComparisonLine`, `Chromatic_Walls_CompletedInfinityCut`, `Chromatic_Walls_CompletedPureComparison`, `Chromatic_Walls_FiniteRayGeometry`, `Chromatic_Walls_FiniteRefinementImportAll`, `Chromatic_Walls_InfinityCutCharts`, `Chromatic_Walls_InfinityFiniteLoop`, `Chromatic_Walls_InfinityPath`, `Chromatic_Walls_LaurentCompletionFaithful`, `Chromatic_Walls_LaurentRayEmbedding`, `Chromatic_Walls_MutatedIncomingNonpure`, `Chromatic_Walls_MutatedIncomingNonpureRoot`, `Chromatic_Walls_MutatedLineCompletion`, `Chromatic_Walls_MutatedPathCompletion`, `Chromatic_Walls_MutatedPathIndependent`, `Chromatic_Walls_MutatedPureLine`, `Chromatic_Walls_MutatedWallKernel`, `Chromatic_Walls_MutationIncomingProbes`, `Chromatic_Walls_MutationInfinityAlgebra`, `Chromatic_Walls_MutationLaurentCompletion`, `Chromatic_Walls_MutationLogCompletion`, `Chromatic_Walls_MutationMonomialAction`, `Chromatic_Walls_MutationSimpleIncoming`, `Chromatic_Walls_NonpJoint`, `Chromatic_Walls_PlanarRefinement`, `Chromatic_Walls_SectionRayTransition`, `Chromatic_Walls_SimpleAdjointFiber`, `Chromatic_Walls_SimpleIncomingData`, `Chromatic_Walls_WallLineInitial`, `Chromatic_Walls_WallRegrade`.
--
--   **Imports.** It imports the bundles `OAIQ368Chrom003` and `OAIQ368Chrom005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom007`, `OAIQ368Chrom011` and `OAIQ368Chrom014`; the proof of `OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom003
import Definitions.Def_OAIQ368Chrom005

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationCoordinates
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (p : I)
include hcoord in
lemma nonp_positive_off_cut {n : ℕ} (hn : 0<n) {m : M} (hm : HasRootDegree C n m)
    (h : M →+ ℝ) (hp : h (simpleRoot C p)≠0) (hm0 : h m=0) :
    0<nonpDegree coord p m := by
  have hnon:=nonpDegree_root_nonneg C coord hcoord p hm
  by_contra hh
  have hz : nonpDegree coord p m=0:=by omega
  rw [nonp_zero_root C coord hcoord p hm hz,map_nsmul] at hm0
  have hnR : (n:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn)
  exact hp ((mul_eq_zero.mp (show (n:ℝ)*h (simpleRoot C p)=0 by simpa only [nsmul_eq_mul] using hm0)).resolve_left hnR)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NonpHomogenize
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogenizeRing
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogenizeAddCommMonoid
local instance homogenizeAddGroup_r8bafe5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma homogenize_monomial_mul (m n : M) (a b : R) (hm : 0≤δ m) (hn : 0≤δ n) :
    homogenize v Ω δ (Torus.monomial v Ω m a*Torus.monomial v Ω n b)=
      homogenize v Ω δ (Torus.monomial v Ω m a)*homogenize v Ω δ (Torus.monomial v Ω n b) := by
  rw [Torus.monomial_mul_monomial,homogenize_monomial,homogenize_monomial,
    homogenize_monomial,PowerSeries.monomial_mul_monomial,Torus.monomial_mul_monomial,_root_.map_add,
    Int.toNat_add hm hn]
lemma homogenize_mul (f g : Torus v Ω)
    (hf : ∀m,f m≠0 → 0≤δ m) (hg : ∀m,g m≠0 → 0≤δ m) :
    homogenize v Ω δ (f*g)=homogenize v Ω δ f*homogenize v Ω δ g := by
  classical
  calc
    _ = ∑m∈f.support,∑n∈g.support,
        homogenize v Ω δ (Torus.monomial v Ω m (f m)*Torus.monomial v Ω n (g n)) := by
      have H (s : Finset M) (a : M → Torus v Ω) :
          homogenize v Ω δ (∑m∈s,a m)=∑m∈s,homogenize v Ω δ (a m) :=
        _root_.map_sum (homogenize v Ω δ) a s
      simp_rw [←H]
      congr 1
      simp_rw [←homo_mul_sum]
      rw [torus_sum_monomial,←homo_sum_mul,torus_sum_monomial]
    _ = ∑m∈f.support,∑n∈g.support,
        homogenize v Ω δ (Torus.monomial v Ω m (f m))*
        homogenize v Ω δ (Torus.monomial v Ω n (g n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact homogenize_monomial_mul v Ω δ m n _ _ (hf m (Finsupp.mem_support_iff.mp hm))
        (hg n (Finsupp.mem_support_iff.mp hn))
    _ = _ := by
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul]
      congr 1
      · rw [←_root_.map_sum,torus_sum_monomial]
      · rw [←_root_.map_sum,torus_sum_monomial]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NonpRegrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)

section Topology
open scoped PowerSeries.WithPiTopology

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeRing
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeTopology
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeDiscreteTopology
lemma regrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hg : RegradeBound v Ω δ B g) :
    regrade v Ω δ B (f*g)=regrade v Ω δ B f*regrade v Ω δ B g := by
  rw [←(regrade_hasSum v Ω δ B hf).tsum_eq,←(regrade_hasSum v Ω δ B hg).tsum_eq,
    (regrade_hasSum v Ω δ B hf).summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (regrade_hasSum v Ω δ B hg).summable (regrade_product_summable v Ω δ B hf hg),
    ←(regrade_hasSum v Ω δ B (hf.mul v Ω δ B hg)).tsum_eq]
  apply tsum_congr
  intro n
  rw [coeff_mul,_root_.map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  exact homogenize_mul v Ω δ _ _ (fun m hm=>(hf ab.1 m hm).1) (fun m hm=>(hg ab.2 m hm).1)

end Topology
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NonpRegradeFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeNegationRing
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeNegationAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeNegationAddGroup
lemma homogenize_one : homogenize v Ω δ 1=1 := by
  change homogenize v Ω δ (Torus.monomial v Ω 0 1)=_
  rw [homogenize_monomial]
  simp only [_root_.map_zero,Int.toNat_zero,monomial_zero_eq_C]
  rfl
lemma regrade_one : regrade v Ω δ B 1=1 := by
  classical
  apply PowerSeries.ext
  intro d
  rw [regrade_coeff,Finset.sum_eq_single 0]
  · rw [coeff_zero_eq_constantCoeff_apply,constantCoeff_one,homogenize_one]
  · intro n hn hn0
    rw [coeff_one,ite_eq_right hn0,_root_.map_zero,_root_.map_zero]
  · intro h
    simp at h

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RegradeLog
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)
local instance regradeLogRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeLogNonUnitalSemiring_r8bafe5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance regradeLogNonUnitalNonAssocSemiring_r8bafe5_1 : NonUnitalNonAssocSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogAddCommGroup
local instance regradeLogSub_r8bafe5_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma homogenize_smul (q : ℚ) (f : Torus v Ω) :
    homogenize v Ω δ (q • f)=q • homogenize v Ω δ f := by
  ext n m
  simp only [homogenize_coeff,coeff_smul,Finsupp.smul_apply]
  split_ifs <;> simp

def regradeLinear : PowerSeries (Torus v Ω) →ₗ[ℚ] PowerSeries (Torus v Ω) where
  toFun:=regrade v Ω δ B
  map_add' f g:=by
    apply PowerSeries.ext
    intro n
    ext m
    simp only [regrade_coeff,nonp_torus_eval_sum,homogenize_coeff,_root_.map_add,Finsupp.add_apply]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  map_smul' q f:=by
    apply PowerSeries.ext
    intro n
    simp only [regrade_coeff,coeff_smul,homogenize_smul,Finset.smul_sum,RingHom.id_apply]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_KernelTraceLog
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.kernelTraceLogAddCommGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.kernelTraceLogAddGroup
local instance kernelTraceLogSub_r8bafe5_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma log_positive_zero (h : M→+ℝ) (F : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1)
    (hf : ∀n m,coeff (n+1) F m≠0→0<h m) (r : M) (hr : h r=0) (n : ℕ) :
    coeff n (FormalLog.log F) r=0 := by
  apply strict_log_support v Ω (V:=fun m=>0<h m) (fun a b ha hb=>by rw [map_add]; linarith)
    F hF (fun n m hm=>not_not.mp (fun hn=>hm (hf n m hn))) n r
  simpa only [hr] using (lt_irrefl (0:ℝ))

lemma log_negative_zero (h : M→+ℝ) (F : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1)
    (hf : ∀n m,coeff (n+1) F m≠0→h m<0) (r : M) (hr : h r=0) (n : ℕ) :
    coeff n (FormalLog.log F) r=0 := by
  apply strict_log_support v Ω (V:=fun m=>h m<0) (fun a b ha hb=>by rw [map_add]; linarith)
    F hF (fun n m hm=>not_not.mp (fun hn=>hm (hf n m hn))) n r
  simpa only [hr] using (lt_irrefl (0:ℝ))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRayGeometry
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (e : M →+ E) (he : Function.Injective e) (C : (I → ℤ) →+ M)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hdeg in
lemma positive_ray_of_mem_span (r p : M) (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (hr : HasRootDegree C d r) (hp : HasRootDegree C n p)
    (H : e p∈Submodule.span ℝ {e r}) : OnPositiveRay r p := by
  obtain ⟨a,ha⟩:=Submodule.mem_span_singleton.mp H
  have HLa:=congrArg L ha
  simp only [map_smul,smul_eq_mul,hdeg d r hr,hdeg n p hp] at HLa
  refine ⟨d,n,hd,hn,he ?_⟩
  simp only [map_nsmul,←Nat.cast_smul_eq_nsmul ℝ]
  rw [←ha,smul_smul]
  congr 1
  nlinarith only [HLa]

omit [Module ℝ E] in
lemma realRoot_mem (N n : ℕ) (hn : n ≤ N) (m : M) (hm : HasRootDegree C n m) :
    e m∈realRootsThrough e C N := by
  classical
  exact Finset.mem_image.mpr ⟨m,mem_rootsThrough C N n hn m hm,rfl⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PlanarRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
lemma joint_roots_plane (N : ℕ) (r : M) (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) (B.flip (e r)) k)
    (a : ℝ) (s : E) (hs : s∈realRootsThrough e C N) (hv : B s (e r)≠0)
    (hsa : (k+a • B.flip (e r)) s=0) :
    ∀n,n ≤ N → ∀m,HasRootDegree C n m → (k+a • B.flip (e r)) (e m)=0 →
      e m∈Submodule.span ℝ {e r,s} := by
  intro n hn m hm hm0
  exact H.joint_plane hs (realRoot_mem e C N n hn m hm) hv a hsa hm0
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallLineInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hdeg in
lemma offset_ray_generic (N d : ℕ) (r : M) (hd : 0 < d) (hr : HasRootDegree C d r)
    (v h : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) v h) :
    RayGeneric C N r (h.toAddMonoidHom.comp e) := by
  refine ⟨H.on_ray,?_⟩
  intro n hn hnN m hm hm0
  apply positive_ray_of_mem_span e he C L hdeg r m d n hd hn hr hm
  by_contra hP
  exact H.avoid _ (realRoot_mem e C N n hnN m hm) hP hm0
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_NonpJoint
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

lemma planar_joint_support (e : M →+ E) (he : Function.Injective e)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
    (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
    (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
    (r s : E) (hr : 0<L r) (hrs : B r s≠0)
    (F : CompletedPositive v Ω C)
    (hF : ∀j,coeff j F.val∈supportedSubring v Ω (planeRoots e r s))
    (N : ℕ) (P : AddSubmonoid M)
    (HI : ∀p d,0<d → d≤N → HasRootDegree C d p → p∈planeRoots e r s →
      ∀j≤N,coeff j (chartZero v Ω C (incomingCovector Ω p) F).val∈supportedSubring v Ω P)
    (h : M →+ ℝ) :
    ∀j≤N,coeff j (chartZero v Ω C h F).val∈supportedSubring v Ω P := by
  classical
  obtain ⟨l,hl,hpair,hRay,hfact⟩:=planar_joint_factorization v Ω C e he B hB hcomp L hdeg r s hr hrs F hF N
  let J (p : M):=chartZero v Ω C (incomingCovector Ω p) F
  let K (p : M):=completedCut v Ω C N (J p)
  let G:=completedListProduct v Ω C l K
  have hK : ∀p∈l,∀j,coeff j (K p).val∈supportedSubring v Ω P:=by
    intro p hp
    obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
    exact completedCut_supported v Ω C N (J p) P (HI p d hd hdN hdp hpP)
  have hG : ∀j,coeff j G.val∈supportedSubring v Ω P:=completed_list_supported v Ω C l K P hK
  have hFG : ∀j≤N,coeff j F.val=coeff j G.val:=by
    intro j hj
    refine (hfact j hj).trans ?_
    apply completedListProduct_congr_through v Ω C l J K N ?_ j hj
    intro p hp i hi
    exact (coeff_cut_of_le (J p).val hi).symm
  have hchart:=chartZero_congr_through v Ω C h F G N hFG
  intro j hj
  rw [hchart j hj]
  exact (chartThree_supported v Ω C h P G hG).2.1 j
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleIncomingData
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d)

include hcoord in
lemma simple_off_fiber (pc i : I) (hi : i≠pc) (α : I → ℤ) (σ : ℤ) :
    simpleRoot C i∈fiberCone coord pc α σ := by
  have hc : coord (simpleRoot C i) pc=0:=by rw [simpleRoot_coordinates C coord hcoord]; simp [hi.symm]
  constructor
  · rw [hc]
  · rw [hc]
    change 0≤∑j∈Finset.univ.erase pc,max 0 (-σ*α j)*coord (simpleRoot C i) j
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (le_max_left _ _)
    rw [simpleRoot_coordinates C coord hcoord]
    by_cases hji : j=i
    · subst j; simp
    · simp [hji]
include hcoord in
lemma positive_nonp_not_simple_ray (pc : I) (r : M) (hr : 0<nonpDegree coord pc r) :
    ¬OnPositiveRay r (simpleRoot C pc) := by
  rintro ⟨a,b,ha,hb,he⟩
  have HH:=congrArg (nonpDegree coord pc) he
  simp only [map_nsmul,nonpDegree_simple_self C coord hcoord pc,nsmul_zero] at HH
  have hb' : 0<(b:ℤ):=by exact_mod_cast hb
  have Hpos : 0<(b:ℤ)*nonpDegree coord pc r:=mul_pos hb' hr
  rw [nsmul_eq_mul] at HH
  omega
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalPureCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
local instance instRingTorus : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentRayEmbedding
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open HahnSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (p : M)
local instance laurentRayRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentRayAddCommMonoid_r8bafe5_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRayAddGroup_r8bafe5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentRayNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def laurentRay (f : HahnSeries ℤ R) : HahnSeries ℤ (Torus v Ω) where
  coeff n:=Torus.monomial v Ω (n • p) (f.coeff n)
  isPWO_support':=f.isPWO_support.mono (by
    intro n hn
    change Torus.monomial v Ω (n • p) (f.coeff n)≠0 at hn
    change f.coeff n≠0
    intro he
    exact hn (by rw [he]; exact Finsupp.single_zero _))
lemma laurentRay_coeff (f : HahnSeries ℤ R) (n : ℤ) :
    (laurentRay v Ω p f).coeff n=Torus.monomial v Ω (n • p) (f.coeff n) := rfl
lemma laurentRay_support (f : HahnSeries ℤ R) : (laurentRay v Ω p f).support=f.support := by
  ext n
  simp only [HahnSeries.mem_support,laurentRay_coeff]
  constructor
  · intro hn hz
    apply hn
    rw [hz]
    exact Finsupp.single_zero _
  · intro hn hz
    have H:=congrArg (fun a : Torus v Ω=>a (n • p)) hz
    exact hn (by simpa [Torus.monomial] using H)
lemma laurentRay_zero : laurentRay v Ω p 0=0 := by
  apply HahnSeries.ext
  funext n
  simp [laurentRay_coeff]
lemma laurentRay_add (f g : HahnSeries ℤ R) :
    laurentRay v Ω p (f+g)=laurentRay v Ω p f+laurentRay v Ω p g := by
  apply HahnSeries.ext
  funext n
  simp [laurentRay_coeff,Torus.monomial]
lemma laurentRay_single (n : ℤ) (a : R) :
    laurentRay v Ω p (HahnSeries.single n a)=HahnSeries.single n (Torus.monomial v Ω (n • p) a) := by
  apply HahnSeries.ext
  funext j
  simp only [laurentRay_coeff,HahnSeries.coeff_single]
  by_cases hj : j=n
  · subst j; simp
  · simp [hj,Torus.monomial]
lemma laurentRay_one : laurentRay v Ω p 1=1 := by
  change laurentRay v Ω p (HahnSeries.single 0 1)=HahnSeries.single 0 1
  rw [laurentRay_single,zero_smul]
  rfl
lemma laurentRay_mul (hp : Ω p p=0) (f g : HahnSeries ℤ R) :
    laurentRay v Ω p (f*g)=laurentRay v Ω p f*laurentRay v Ω p g := by
  classical
  apply HahnSeries.ext
  funext n
  rw [laurentRay_coeff,HahnSeries.coeff_mul,HahnSeries.coeff_mul]
  have HS : Finset.antidiagonal (laurentRay v Ω p f).isPWO_support
      (laurentRay v Ω p g).isPWO_support n=
      Finset.antidiagonal f.isPWO_support g.isPWO_support n := by
    ext ij
    simp only [Finset.mem_antidiagonal,laurentRay_support]
  rw [HS]
  change (Finsupp.singleAddHom (n • p)) _=_
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have H:=(Finset.mem_antidiagonal.mp hij).2.2
  simp only [laurentRay_coeff,Torus.monomial_mul_monomial,map_zsmul,
    AddMonoidHom.zsmul_apply,hp,smul_zero,zpow_zero,Units.val_one,mul_one]
  rw [←add_zsmul,H]
  rfl

def laurentRayHom (hp : Ω p p=0) : HahnSeries ℤ R →+* HahnSeries ℤ (Torus v Ω) where
  toFun:=laurentRay v Ω p
  map_zero':=laurentRay_zero v Ω p
  map_one':=laurentRay_one v Ω p
  map_add':=laurentRay_add v Ω p
  map_mul':=laurentRay_mul v Ω p hp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalLaurentScalars
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gaugeAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gauge_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.RationalFiber.pureAction_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0) (p : M)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalSemiringTorus
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorus
def expandScalar : RatFunc K →+* HahnSeries ℤ (Torus v Ω) :=
  (laurentRayHom v Ω p (hΩ p)).comp expandZero
lemma expandScalar_C (a : K) :
    expandScalar v Ω hΩ p (RatFunc.C a)=HahnSeries.single 0 (Torus.monomial v Ω 0 a) := by
  simp only [expandScalar,RingHom.comp_apply,expandZero_constant]
  change laurentRay v Ω p (HahnSeries.single 0 a)=_
  rw [laurentRay_single,zero_smul]
lemma expandScalar_X : expandScalar v Ω hΩ p RatFunc.X=HahnSeries.single 1 (Torus.X v Ω p) := by
  change laurentRay v Ω p (expandZero RatFunc.X)=_
  have H:=expandZero_X_zpow (K:=K) (1:ℤ)
  simp only [zpow_one] at H
  rw [H,laurentRay_single,one_smul]
  rfl
lemma constUnit_conj_C (m : M) (a : K) :
    innerHom (constUnit v Ω hΩ m) (expandScalar v Ω hΩ p (RatFunc.C a))=
      expandScalar v Ω hΩ p (RatFunc.C a) := by
  rw [expandScalar_C]
  dsimp only [innerHom, constUnit, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk, Units.inv_mk]
  rw [HahnSeries.single_mul_single,HahnSeries.single_mul_single]
  simp [Torus.X,Torus.monomial_mul_monomial,hΩ]
lemma constUnit_conj_X (m : M) :
    innerHom (constUnit v Ω hΩ m) (expandScalar v Ω hΩ p RatFunc.X)=
      expandScalar v Ω hΩ p (RatFunc.C (↑(v^(-2*Ω p m)):K)*RatFunc.X) := by
  rw [map_mul,expandScalar_C,expandScalar_X]
  dsimp only [innerHom, constUnit, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk, Units.inv_mk]
  simp only [HahnSeries.single_mul_single,zero_add,add_zero,Torus.X,Torus.monomial_mul_monomial,
    map_add,AddMonoidHom.add_apply,map_neg,hΩ,map_zero,AddMonoidHom.zero_apply,
    zpow_zero,Units.val_one,mul_one,one_mul,zero_add]
  have he : m+p+-m=p:=by abel
  rw [he,←Units.val_mul,←zpow_add,pairing_swap Ω hΩ m p]
  congr 3
  ring_nf
lemma scalar_commutation (m : M) (a : RatFunc K) :
    HahnSeries.single 0 (Torus.X v Ω m)*expandScalar v Ω hΩ p a=
      expandScalar v Ω hΩ p (scale (v^(-2*Ω p m)) a)*HahnSeries.single 0 (Torus.X v Ω m) := by
  have HE : (innerHom (constUnit v Ω hΩ m)).comp (expandScalar v Ω hΩ p)=
      (expandScalar v Ω hΩ p).comp (scale (v^(-2*Ω p m))) := by
    apply ratFunc_hom_ext_ring
    have HP : ((innerHom (constUnit v Ω hΩ m)).comp (expandScalar v Ω hΩ p)).comp
        (algebraMap (Polynomial K) (RatFunc K))=
        ((expandScalar v Ω hΩ p).comp (scale (v^(-2*Ω p m)))).comp
        (algebraMap (Polynomial K) (RatFunc K)) := by
      apply Polynomial.ringHom_ext
      · intro a
        change innerHom _ (expandScalar v Ω hΩ p (RatFunc.C a))=
          expandScalar v Ω hΩ p (scale _ (RatFunc.C a))
        rw [scale_constant,constUnit_conj_C]
      · change innerHom _ (expandScalar v Ω hΩ p RatFunc.X)=
          expandScalar v Ω hΩ p (scale _ RatFunc.X)
        rw [scale_X,constUnit_conj_X]
    exact fun q=>congrArg (fun f : Polynomial K →+* HahnSeries ℤ (Torus v Ω)=>f q) HP
  have H:=congrArg (fun f : RatFunc K →+* HahnSeries ℤ (Torus v Ω)=>f a) HE
  change ↑(constUnit v Ω hΩ m)*expandScalar v Ω hΩ p a*↑((constUnit v Ω hΩ m)⁻¹)=
    expandScalar v Ω hΩ p (scale _ a) at H
  have HH:=congrArg (fun x : HahnSeries ℤ (Torus v Ω)=>x*(↑(constUnit v Ω hΩ m):HahnSeries ℤ (Torus v Ω))) H
  have hu : (↑((constUnit v Ω hΩ m)⁻¹):HahnSeries ℤ (Torus v Ω))*↑(constUnit v Ω hΩ m)=1 := (constUnit v Ω hΩ m).inv_val
  rw [mul_assoc, mul_assoc, hu, mul_one] at HH
  exact HH
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_1
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalSemiringTorus_1
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorus_1
def expandFiberTerm (l : k.ker) : RatFunc K →+ HahnSeries ℤ (Torus v Ω) where
  toFun a:=expandScalar v Ω hΩ p a*HahnSeries.single 0 (Torus.X v Ω l)
  map_zero':=by simp
  map_add' a b:=by simp [add_mul]
def expandFiberAdd : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+
    HahnSeries ℤ (Torus v Ω) := Finsupp.liftAddHom (expandFiberTerm v Ω hΩ k p)
lemma expandFiberAdd_monomial (l : k.ker) (a : RatFunc K) :
    expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)=
      expandScalar v Ω hΩ p a*HahnSeries.single 0 (Torus.X v Ω l) :=
  Finsupp.liftAddHom_apply_single _ _ _
lemma const_torus_product (m n : M) :
    HahnSeries.single (0:ℤ) (Torus.X v Ω m)*HahnSeries.single 0 (Torus.X v Ω n)=
      expandScalar v Ω hΩ p (RatFunc.C (↑(v^(Ω m n)):K))*
        HahnSeries.single 0 (Torus.X v Ω (m+n)) := by
  rw [expandScalar_C]
  simp [HahnSeries.single_mul_single,Torus.X,Torus.monomial_mul_monomial]
lemma expandFiberAdd_monomial_mul (l j : k.ker) (a b : RatFunc K) :
    expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a*FiberTorus.monomial v _ _ j b)=
      expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)*
        expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ j b) := by
  rw [FiberTorus.monomial_mul,expandFiberAdd_monomial,expandFiberAdd_monomial,expandFiberAdd_monomial]
  simp only [_root_.map_mul,FiberTorus.twist]
  change (expandScalar v Ω hΩ p a*expandScalar v Ω hΩ p (scale (v^(-2*Ω p l)) b)*
      expandScalar v Ω hΩ p (RatFunc.C (↑(v^(Ω l j)):K)))*
      HahnSeries.single 0 (Torus.X v Ω ((l:M)+(j:M)))=_
  simp only [mul_assoc]
  rw [←const_torus_product]
  rw [←mul_assoc (expandScalar v Ω hΩ p (scale _ b)),←scalar_commutation]
  simp only [mul_assoc]

lemma expandFiberAdd_mul (f g : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiberAdd v Ω hΩ k p (f*g)=expandFiberAdd v Ω hΩ k p f*expandFiberAdd v Ω hΩ k p g := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [_root_.add_mul,map_add,hf,hf']
  | single l a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [_root_.mul_add,map_add,hg,hg']
    | single j b=>exact expandFiberAdd_monomial_mul v Ω hΩ k p l j a b
lemma expandFiberAdd_one : expandFiberAdd v Ω hΩ k p 1=1 := by
  change expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ 0 1)=_
  rw [expandFiberAdd_monomial,map_one,one_mul]
  rfl
def expandFiber : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+*
    HahnSeries ℤ (Torus v Ω) where
  __:=expandFiberAdd v Ω hΩ k p
  map_one':=expandFiberAdd_one v Ω hΩ k p
  map_mul':=expandFiberAdd_mul v Ω hΩ k p
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalRegrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
variable (δ : M →+ ℤ) (B : ℕ)
lemma rationalRegrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hg : RegradeBound v Ω δ B g) :
    rationalRegrade v Ω hΩ k p hp δ B (f*g)=
      rationalRegrade v Ω hΩ k p hp δ B f*rationalRegrade v Ω hΩ k p hp δ B g := by
  unfold rationalRegrade
  rw [regrade_mul v Ω δ B hf hg,_root_.map_mul]
lemma rationalRegrade_one : rationalRegrade v Ω hΩ k p hp δ B 1=1 := by
  unfold rationalRegrade
  rw [regrade_one,_root_.map_one]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPureComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_5
local instance instAddCommMonoidTorus_2_r8bafe5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_2_r8bafe5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_5_r8bafe5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_5_r8bafe5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
def boundedRationalUnit (B : ℕ) (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hg : RegradeBound v Ω δ B u.inv.val) :
    (PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))ˣ where
  val:=rationalRegrade v Ω hΩ k p hp δ B u.val.val
  inv:=rationalRegrade v Ω hΩ k p hp δ B u.inv.val
  val_inv:=by
    rw [←rationalRegrade_mul v Ω hΩ k p hp δ B hf hg]
    have H:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) u.val_inv
    change u.val.val*u.inv.val=1 at H
    rw [H,rationalRegrade_one]
  inv_val:=by
    rw [←rationalRegrade_mul v Ω hΩ k p hp δ B hg hf]
    have H:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) u.inv_val
    change u.inv.val*u.val.val=1 at H
    rw [H,rationalRegrade_one]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionRayTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry PowerSeriesSplit PowerSeriesAdjoint
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hdeg in
lemma realRoot_ne_zero (d : ℕ) (hd : 0<d) (p : M) (hp : HasRootDegree C d p) : e p≠0 := by
  intro hh
  have H:=hdeg d p hp
  rw [hh,map_zero] at H
  have hdR : (0:ℝ)<d:=by exact_mod_cast hd
  linarith
omit [Module ℝ E] in
lemma realRoot_exists (N : ℕ) (s : E) (hs : s∈realRootsThrough e C N) :
    ∃p d,d≤N ∧ HasRootDegree C d p ∧ e p=s := by
  classical
  obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hs
  obtain ⟨d,hd,hp⟩:=Finset.mem_biUnion.mp hp
  refine ⟨p,d,by have H:=Finset.mem_range.mp hd; omega,?_,rfl⟩
  simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hp
include he hdeg in
lemma section_event_ray (N : ℕ) (v k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C N) v k) :
    ∃p d,0<d ∧ d≤N ∧ HasRootDegree C d p ∧ v (e p)≠0 ∧
      RayGeneric C N p ((k+a • v).toAddMonoidHom.comp e) := by
  obtain ⟨s,hs,hv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp ha
  obtain ⟨p,d,hd,hp,rfl⟩:=realRoot_exists C e N s hs
  have hd0 : 0<d:=by
    by_contra hh
    have hd0 : d=0:=by omega
    subst d
    have hp0 : p=0:=by
      obtain ⟨c,hc,hcp⟩:=hp
      have hc0 : c=0:=funext (fun i=>Finset.sum_eq_zero_iff.mp hc i (Finset.mem_univ i))
      subst c
      change C (0 : I → ℤ)=p at hcp
      rw [map_zero] at hcp
      exact hcp.symm
    exact hv (by rw [hp0,map_zero,map_zero])
  refine ⟨p,d,hd0,hd,hp,hv,hsa,?_⟩
  intro n hn hnN m hm hm0
  have HH:=H.joint_plane hs (realRoot_mem e C N n hnN m hm) hv a hsa hm0
  apply positive_ray_of_mem_span e he C L hdeg p m d n hd0 hn hp hm
  obtain ⟨x,y,hxy⟩:=Submodule.mem_span_pair.mp HH
  apply Submodule.mem_span_singleton.mpr
  exact ⟨y,by simpa only [smul_zero,zero_add] using hxy⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_AllOrderSectionLine
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

include he hdeg in
lemma section_event_ray_all_orders (N : ℕ) (v k : Module.Dual ℝ E)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C N) v k) :
    ∃p d,0<d ∧ d≤N ∧ HasRootDegree C d p ∧ v (e p)≠0 ∧
      ∀K,RayGeneric C K p ((k+a • v).toAddMonoidHom.comp e) := by
  obtain ⟨p,d,hd0,hd,hp,hv,hgen⟩:=section_event_ray C e he L hdeg N v k (H N) a ha
  refine ⟨p,d,hd0,hd,hp,hv,fun K=>⟨hgen.1,?_⟩⟩
  intro n hn hnK m hm hm0
  have hpS:=realRoot_mem e C (max N K) d (hd.trans (le_max_left _ _)) p hp
  have hmS:=realRoot_mem e C (max N K) n (hnK.trans (le_max_right _ _)) m hm
  have HH:=(H (max N K)).joint_plane hpS hmS hv a hgen.1 hm0
  apply positive_ray_of_mem_span e he C L hdeg p m d n hd0 hn hp hm
  obtain ⟨x,y,hxy⟩:=Submodule.mem_span_pair.mp HH
  exact Submodule.mem_span_singleton.mpr ⟨y,by simpa only [smul_zero,zero_add] using hxy⟩
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

include hdeg in
lemma line_chamber_of_not_event (N : ℕ) (v k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : a∉lineEvents (realRootsThrough e C N) v k) :
    ChamberGeneric C N ((k+a • v).toAddMonoidHom.comp e) := by
  intro n hn hnN m hm hm0
  have hs:=realRoot_mem e C N n hnN m hm
  by_cases hv : v (e m)=0
  · have hk : k (e m)=0:=by
      change k (e m)+a*v (e m)=0 at hm0
      simpa only [hv,mul_zero,add_zero] using hm0
    apply H.avoid (e m) hs _ hk
    simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using
      realRoot_ne_zero C e L hdeg n hn m hm
  · exact ha ((mem_lineEvents_iff _ _ _ _).mpr ⟨e m,hs,hv,hm0⟩)

variable (u : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)

include hdeg in
lemma line_chart_trivial (F : CompletedPositive u Ω C) (N : ℕ)
    (v k : Module.Dual ℝ E) (H : GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : a∉lineEvents (realRootsThrough e C N) v k) :
    ∀n≤N,coeff n (chartZero u Ω C ((k+a • v).toAddMonoidHom.comp e) F).val=coeff n 1 :=
  chamber_chart_trivial C u Ω F N _ (line_chamber_of_not_event C e L hdeg N v k H a ha)

omit [Module ℝ E] in
lemma realRootsThrough_mono {N K : ℕ} (h : N≤K) : realRootsThrough e C N⊆realRootsThrough e C K := by
  intro s hs
  obtain ⟨p,d,hd,hp,rfl⟩:=realRoot_exists C e N s hs
  exact realRoot_mem e C K d (hd.trans h) p hp

lemma lineEvents_mono {S T : Finset E} (h : S⊆T) (v k : Module.Dual ℝ E) :
    lineEvents S v k⊆lineEvents T v k := by
  intro a ha
  obtain ⟨s,hs,hv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp ha
  exact (mem_lineEvents_iff _ _ _ _).mpr ⟨s,h hs,hv,hsa⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleAdjointFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
lemma sideSign_neg (pos : Bool) : sideSign (!pos)= -sideSign pos := by cases pos <;> rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallRegrade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)

variable [Fintype I]

variable {R : Type*} [CommRing R] (v : Rˣ)
local instance wallRegradeRing : Ring (Torus v Ω) := Torus.instRing v Ω

local instance wallRegradeAddCommMonoid_r8bafe5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance wallRegradeAddGroup_r8bafe5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def mutationTorusPush : Torus v Ω →+* Torus v Ω :=
  Torus.push v Ω Ω (mutationLinearPiece Ω C pc pos) (mutationLinearPiece_pairing Ω hΩ C pc pos)
omit [Fintype I] in
lemma mutationTorusPush_read (f : Torus v Ω) (m : M) :
    mutationTorusPush Ω hΩ C pc pos v f (mutationLinearPiece Ω C pc pos m)=f m :=
  Finsupp.mapDomain_apply (mutationLinearPiece_injective Ω hΩ C pc pos) f m

def mutationCompletion (f : PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω) :=
  PowerSeries.map (mutationTorusPush Ω hΩ C pc pos v)
    (regrade v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f)

lemma mutationCompletion_coeff_read (f : PowerSeries (Torus v Ω)) (d : ℕ) (m : M) :
    coeff d (mutationCompletion Ω hΩ C coord pc pos v f) (mutationLinearPiece Ω C pc pos m)=
      if d=(mutationNewOrder Ω C coord pc pos m).toNat then
        ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1),coeff n f m else 0 := by
  rw [mutationCompletion,coeff_map,mutationTorusPush_read,regrade_coeff_eval]

lemma mutationCompletion_constant (f : PowerSeries (Torus v Ω)) (hf : constantCoeff f=1) :
    constantCoeff (mutationCompletion Ω hΩ C coord pc pos v f)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  rw [mutationCompletion,coeff_map,regrade_coeff]
  simp only [mul_zero,zero_add,Finset.sum_range_one,coeff_zero_eq_constantCoeff,hf,
    homogenize_one,map_one]

lemma mutationCompletion_mul {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f)
    (hg : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) g) :
    mutationCompletion Ω hΩ C coord pc pos v (f*g)=
      mutationCompletion Ω hΩ C coord pc pos v f*mutationCompletion Ω hΩ C coord pc pos v g := by
  unfold mutationCompletion
  rw [regrade_mul v Ω _ _ hf hg,map_mul]
lemma mutationCompletion_one : mutationCompletion Ω hΩ C coord pc pos v 1=1 := by
  rw [mutationCompletion,regrade_one,map_one]
lemma mutationCompletion_inverse_mul {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f)
    (hc : constantCoeff f=1) :
    mutationCompletion Ω hΩ C coord pc pos v (PowerSeries.invOfUnit f 1)*
      mutationCompletion Ω hΩ C coord pc pos v f=1 := by
  rw [←mutationCompletion_mul Ω hΩ C coord pc pos v (hf.invOfUnit v Ω _ _) hf,
    PowerSeries.invOfUnit_mul f 1 hc,mutationCompletion_one]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ComparisonLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

variable (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
omit [DecidableEq I] in
include he hdeg in
lemma lineRayData_nonempty (v k : Module.Dual ℝ E)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k) :
    Nonempty (LineRayData C e v k a) := by
  obtain ⟨N,ha⟩:=ha
  obtain ⟨r,d,hd,_,hr,hv,hg⟩:=section_event_ray_all_orders C e he L hdeg N v k H a ha
  exact ⟨⟨r,d,hd,hr,hv,hg⟩⟩

def lineRayData (v k : Module.Dual ℝ E)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k) :
    LineRayData C e v k a :=
  Classical.choice (lineRayData_nonempty C e he L hdeg v k H a ha)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationSimpleIncoming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)

variable {R : Type*} [CommRing R] (v : Rˣ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutationSimpleSideRing
local instance mutationSimpleSideAddCommMonoid_r8bafe5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance mutationSimpleSideAddGroup_r8bafe5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma mutationCompletion_congr_through (f g : PowerSeries (Torus v Ω)) (d N : ℕ)
    (hd : (mutationSize Ω C pc+1)*d≤N) (hfg : ∀n≤N,coeff n f=coeff n g) :
    coeff d (mutationCompletion Ω hΩ C coord pc pos v f)=
      coeff d (mutationCompletion Ω hΩ C coord pc pos v g) := by
  rw [mutationCompletion,mutationCompletion,coeff_map,coeff_map,regrade_coeff,regrade_coeff]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [hfg n (by have HH:=Finset.mem_range.mp hn; omega)]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRefinementImportAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {A : Type*} [Ring A]

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance instRingTorusLaurentSeriesRatVUnit : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedLineCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance instRingTorusLaurentSeriesRatVUnit_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {A : Type*} [Ring A]
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance instRingTorusLaurentSeriesRatVUnit_2 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_5_r8bafe5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_5_r8bafe5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
omit [DecidableEq I] in
lemma orientPowerSeries_graded (b : Bool) (f : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf : SeriesGraded LaurentRay.vUnit Ω C f) :
    SeriesGraded LaurentRay.vUnit Ω C (orientPowerSeries b f) := by
  cases b
  · exact hf.inverse LaurentRay.vUnit Ω C
  · exact hf

lemma mutationCompletion_inverse (pos : Bool) (f : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf : RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos)
      (mutationSize Ω C pc+1) f) (hc : constantCoeff f=1) :
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (invOfUnit f 1)=
      invOfUnit (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f) 1 := by
  let g:=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f
  let gi:=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (invOfUnit f 1)
  have hleft : gi*g=1:=mutationCompletion_inverse_mul Ω hΩ C coord pc pos LaurentRay.vUnit hf hc
  have hright : g*invOfUnit g 1=1:=PowerSeries.mul_invOfUnit g 1
    (mutationCompletion_constant Ω hΩ C coord pc pos LaurentRay.vUnit f hc)
  change gi=invOfUnit g 1
  calc gi=gi*1:=(mul_one gi).symm
       _=gi*(g*invOfUnit g 1):=by rw [hright]
       _=(gi*g)*invOfUnit g 1:=(mul_assoc _ _ _).symm
       _=invOfUnit g 1:=by rw [hleft,one_mul]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationMonomialAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I) (pos:Bool)
local instance instRingTorusLaurentSeriesRatVUnit_3 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPathCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance instRingTorusLaurentSeriesRatVUnit_4 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance instRingTorusLaurentSeriesRatVUnit_5 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationOrientedCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] (v : Rˣ) (Ω : M →+ M →+ ℤ)
local instance instRingTorus_3 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorus_4 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedWallKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (u : Rˣ) (Ω : M →+ M →+ ℤ)
local instance instRingTorus_4 : Ring (Torus u Ω) := Torus.instRing u Ω
end

noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance instRingTorusLaurentSeriesRatVUnit_6 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutatedPureFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
local instance instRingTorusLaurentSeriesRatVUnit_7 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentRegrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentRegradeRing
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentRegradeAddCommMonoid
local instance laurentRegradeAddGroup_r8bafe5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def laurentRegradeFamily (f : PowerSeries (Torus v Ω))
    (hf : LaurentBounded v Ω δ κ B f) (d : ℕ) :
    HahnSeries.SummableFamily ℤ (Torus v Ω) ℕ where
  toFun n := coeff d (laurentHomogenize v Ω δ κ (coeff n f))
  isPWO_iUnion_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-(B : ℤ)*(d : ℤ), ?_⟩
    intro z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    by_contra h
    exact hn (hf.laurent_vanish v Ω δ κ B d n z (Or.inl (lt_of_not_ge h)))
  finite_co_support' z := by
    apply (Finset.finite_toSet (Finset.range ((z+(B+1 : ℤ)*(d : ℤ)).toNat+1))).subset
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hn
    apply hf.laurent_vanish v Ω δ κ B d n z
    right
    omega

def laurentRegrade (f : PowerSeries (Torus v Ω))
    (hf : LaurentBounded v Ω δ κ B f) : PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  PowerSeries.mk fun d => (laurentRegradeFamily v Ω δ κ B f hf d).hsum

lemma laurentRegrade_coeff (f : PowerSeries (Torus v Ω))
    (hf : LaurentBounded v Ω δ κ B f) (d : ℕ) (z : ℤ) :
    (coeff d (laurentRegrade v Ω δ κ B f hf)).coeff z =
      ∑ n ∈ Finset.range ((z+(B+1 : ℤ)*(d : ℤ)).toNat+1),
        (coeff d (laurentHomogenize v Ω δ κ (coeff n f))).coeff z := by
  rw [laurentRegrade, coeff_mk]
  apply HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hn (hf.laurent_vanish v Ω δ κ B d n z (Or.inr (by omega)))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInfinityCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_10
local instance instNonUnitalSemiringTorus_10_r8bafe5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_10_r8bafe5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
def expandFiberInfinity : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+*
    HahnSeries ℤ (Torus v Ω) :=
  (expandFiber v Ω hΩ k (-p)).comp (reciprocalFiber v Ω k p)

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentDeshear
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentDeshearRing
local instance laurentDeshearAddCommMonoid_r8bafe5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentDeshearAddGroup_r8bafe5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentDeshearNonUnitalSemiring_r8bafe5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentDeshearNonUnitalNonAssocSemiring_r8bafe5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma laurentHomogenize_shear_coeff (f : Torus v Ω)
    (hf : ∀m,f m≠0 → 0≤δ m ∧ 0≤κ m+(B:ℤ)*δ m)
    (d : ℕ) (z : ℤ) (hz : 0≤z+(B:ℤ)*(d:ℤ)) :
    (coeff d (laurentHomogenize v Ω δ κ f)).coeff z =
      coeff (z+(B:ℤ)*(d:ℤ)).toNat (coeff d (biHomogenize v Ω δ (κ+B • δ) f)) := by
  ext m
  rw [laurentHomogenize_coeff,biHomogenize_coeff]
  by_cases hm : f m=0
  · simp [hm]
  obtain ⟨hd,hk⟩:=hf m hm
  change (if d=(δ m).toNat ∧ z=κ m then f m else 0)=
    if d=(δ m).toNat ∧ (z+(B:ℤ)*(d:ℤ)).toNat=(κ m+(B:ℤ)*δ m).toNat then f m else 0
  by_cases he : d=(δ m).toNat
  · have hD : δ m=(d:ℤ) := by rw [he,Int.toNat_of_nonneg hd]
    rw [hD] at hk ⊢
    have H : (z+(B:ℤ)*(d:ℤ)).toNat=(κ m+(B:ℤ)*(d:ℤ)).toNat ↔ z=κ m := by omega
    simp only [Int.toNat_natCast, true_and, H, eq_self]
  · simp only [he,false_and,ite_false, if_false]

lemma laurentRegrade_eq_deshear (f : PowerSeries (Torus v Ω))
    (hf : LaurentBounded v Ω δ κ B f) :
    laurentRegrade v Ω δ κ B f hf = Deshear.deshear B (boundedBiRegrade v Ω δ (κ+B • δ) f) := by
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext z
  rw [laurentRegrade_coeff,Deshear.deshear_read]
  by_cases hz : 0≤z+(B:ℤ)*(d:ℤ)
  · have hcast : ((z+(B:ℤ)*(d:ℤ)).toNat:ℤ)=z+(B:ℤ)*(d:ℤ) := Int.toNat_of_nonneg hz
    rw [←hcast,HahnSeries.ofPowerSeries_apply_coeff,boundedBiRegrade_coeff]
    have hN : (z+(B+1:ℤ)*(d:ℤ)).toNat=d+(z+(B:ℤ)*(d:ℤ)).toNat := by
      rw [show z+(B+1:ℤ)*(d:ℤ)=(d:ℤ)+(z+(B:ℤ)*(d:ℤ)) by ring,
        Int.toNat_add (Int.natCast_nonneg d) hz,Int.toNat_natCast]
    rw [hN]
    apply Finset.sum_congr rfl
    intro n hn
    exact laurentHomogenize_shear_coeff v Ω δ κ B (coeff n f)
      (fun m hm=>⟨(hf n m hm).1,by have H:=(hf n m hm).2.1; nlinarith⟩) d z hz
  · have hneg : z+(B:ℤ)*(d:ℤ)<0 := lt_of_not_ge hz
    rw [HahnSeries.ofPowerSeries_apply,HahnSeries.embDomain_of_notMem_range]
    · apply Finset.sum_eq_zero
      intro n hn
      apply hf.laurent_vanish v Ω δ κ B d n z
      left
      nlinarith
    · rintro ⟨n,hn⟩
      simp only [Nat.castOrderEmbedding_apply] at hn
      omega

lemma laurentRegrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g) :
    laurentRegrade v Ω δ κ B (f*g) (hf.mul v Ω δ κ B hg)=
      laurentRegrade v Ω δ κ B f hf*laurentRegrade v Ω δ κ B g hg := by
  rw [laurentRegrade_eq_deshear,laurentRegrade_eq_deshear,laurentRegrade_eq_deshear,
    boundedBiRegrade_mul v Ω δ (κ+B • δ) (hf.bi_shear v Ω δ κ B) (hg.bi_shear v Ω δ κ B),
    Deshear.deshear_mul]
lemma laurentRegrade_add {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g) :
    laurentRegrade v Ω δ κ B (f+g) (hf.add v Ω δ κ B hg)=
      laurentRegrade v Ω δ κ B f hf+laurentRegrade v Ω δ κ B g hg := by
  rw [laurentRegrade_eq_deshear,laurentRegrade_eq_deshear,laurentRegrade_eq_deshear,
    boundedBiRegrade_add,Deshear.deshear_add]
lemma laurentRegrade_zero : laurentRegrade v Ω δ κ B 0 (LaurentBounded.zero v Ω δ κ B)=0 := by
  rw [laurentRegrade_eq_deshear,boundedBiRegrade_zero,Deshear.deshear_zero]
lemma laurentRegrade_one : laurentRegrade v Ω δ κ B 1 (LaurentBounded.one v Ω δ κ B)=1 := by
  rw [laurentRegrade_eq_deshear,boundedBiRegrade_one,Deshear.deshear_one]

def laurentRegradeHom : laurentBoundedSubring v Ω δ κ B →+* PowerSeries (HahnSeries ℤ (Torus v Ω)) where
  toFun f := laurentRegrade v Ω δ κ B f.val f.property
  map_zero' := laurentRegrade_zero v Ω δ κ B
  map_one' := laurentRegrade_one v Ω δ κ B
  map_add' f g := laurentRegrade_add v Ω δ κ B f.property g.property
  map_mul' f g := laurentRegrade_mul v Ω δ κ B f.property g.property
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationLaurentCompletion
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

variable (v : (LaurentSeries ℚ)ˣ)
local instance mutationLaurentCompletionRing : Ring (Torus v Ω) := Torus.instRing v Ω

local instance mutationLaurentCompletionAddCommMonoid_r8bafe5_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance mutationLaurentCompletionAddGroup_r8bafe5_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
def mutatedLaurent (f : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  laurentRegrade v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
    (-pureDegree coord pc) (mutationSize Ω C pc) f.val
    (mutated_series_laurentBounded Ω C coord hcoord pc v f.property.2)

def infinityCompletedUnit (F : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    (PowerSeries (HahnSeries ℤ (Torus v Ω)))ˣ :=
  Units.map (laurentRegradeHom v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
    (-pureDegree coord pc) (mutationSize Ω C pc))
    (completedInfinityUnit Ω C coord hcoord pc v F)

@[simp] lemma infinityCompletedUnit_val (F : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    (infinityCompletedUnit Ω C coord hcoord pc v F).val =
      mutatedLaurent Ω C coord hcoord pc v F := rfl

@[simp] lemma infinityCompletedUnit_inv (F : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    (infinityCompletedUnit Ω C coord hcoord pc v F).inv =
      mutatedLaurent Ω C coord hcoord pc v (completedInverse v Ω (mutatedRoots Ω C pc) F) := rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationInfinityAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RationalFiber WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (v : (LaurentSeries ℚ)ˣ)
local instance instRingTorusLaurentSeriesRat : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityCutCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
local instance instRingTorus_13 : Ring (Torus v Ω) := Torus.instRing v Ω

local instance instNonUnitalSemiringTorus_13_r8bafe5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_13_r8bafe5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
def infinitySideHom (pos : Bool) :
    PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) →+*
    PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  (PowerSeries.map (expandFiberInfinity v Ω hΩ k p)).comp
    (mutationSideAction v (complementOmega k Ω) (complementAlpha k p Ω) pos).toRingHom

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPureLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k:Module.Dual ℝ E) (H:∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance mutatedPureLineRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance instRingTorusLaurentSeriesRatVUnit_6 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance instRingTorus_14 : Ring (Torus v Ω) := Torus.instRing v Ω

local instance instAddCommMonoidTorus_7_r8bafe5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_7_r8bafe5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def infinityTestInput (pos : Bool) (m : M) :
    PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :=
  (mutationSideAction v (complementOmega k Ω) (complementAlpha k p Ω) pos).symm
    (PowerSeries.C (embed v Ω hΩ k p hp (Torus.X v Ω m)))

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityFiniteLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance instRingTorusLaurentSeriesRatVUnit_7 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_r8bafe5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_r8bafe5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_1_r8bafe5_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorusLaurentSeriesRatVUnit_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentCompletionFaithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M I : Type*} [Field K] [AddCommGroup M] [Fintype I]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (δ κ η : M →+ ℤ) (B : ℕ)
local instance laurentCompletionFaithfulRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentCompletionFaithfulAddCommMonoid_r8bafe5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentCompletionFaithfulAddGroup_r8bafe5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentCompletionFaithfulNonUnitalSemiring_r8bafe5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentCompletionFaithfulNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance instRingTorusLaurentSeriesRatVUnit_8 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_8_r8bafe5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_8_r8bafe5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_2_r8bafe5_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorusLaurentSeriesRatVUnit_2 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPathIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)
local instance mutatedPathIndependentRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
local instance mutatedPathIndependentPureRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutatedNegativeCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)
local instance instRingTorusLaurentSeriesRatVUnit_9 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationLogCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I) (pos : Bool) (v : Rˣ)
local instance instRingTorus_6 : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)
local instance instRingTorusLaurentSeriesRatVUnit_10 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationIncomingProbes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance mutationIncomingProbesRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedIncomingNonpure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)
local instance instRingTorusLaurentSeriesRatVUnit_11 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedIncomingNonpureRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)
local instance instRingTorusLaurentSeriesRatVUnit_12 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
local instance instRingTorusLaurentSeriesRatVUnit_13 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutatedSystemIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
local instance instRingTorusLaurentSeriesRatVUnit_14 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HalfspacePolynomialCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
local instance halfspacePolynomialCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


