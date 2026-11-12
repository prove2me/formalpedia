-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_CorrespondenceTests
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T08:59:48.907556+00:00
-- url     : https://prove2.me/theorems/8fdeb614-ee18-4a68-a4f7-1df8f43e69d6
-- title:
--   Correspondence Tests
-- statement:
--   Definitions and structural lemmas for Correspondence Tests, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondenceTests.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_InverseCorrespondence
import Theorems.Thm_OAI_CubicEisenstein_continuous_hyperbolic_action
import Theorems.Thm_OAI_CubicEisenstein_continuous_integralOrbitProjection
import Theorems.Thm_OAI_CubicEisenstein_cubeCuspTriangular_norm_sq
import Theorems.Thm_OAI_CubicEisenstein_integralConjugateMap_projection
import Theorems.Thm_OAI_CubicEisenstein_integralCoverFiberPoint_mk
import Theorems.Thm_OAI_CubicEisenstein_integralCoverFiberPoint_rep
import Theorems.Thm_OAI_CubicEisenstein_integralCoverMap_continuous
import Theorems.Thm_OAI_CubicEisenstein_integralCoverMap_fiberPoint
import Theorems.Thm_OAI_CubicEisenstein_integralCoverMap_projection
import Theorems.Thm_OAI_CubicEisenstein_kernelProjection_contMDiff

set_option autoImplicit false
namespace OAI
noncomputable section
namespace CubicEisenstein
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
section
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O
end
section
open MeasureTheory
open scoped Classical MatrixGroups BigOperators
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O
end
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O
end
section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
lemma integralCoverFiberPoint_continuous (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) : Continuous (integralCoverFiberPoint H K q) := by
  have he : integralCoverFiberPoint H K q=fun w=>
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) :=
    funext (integralCoverFiberPoint_rep H K q)
  rw [he]
  exact (continuous_integralOrbitProjection H).comp
    (continuous_hyperbolic_action (integralComplexMatrix ((integralCoverRep H K q)⁻¹:SL(2,ActualEisensteinCubic.O))))
lemma integralCoverMap_fiber {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (w : HyperbolicSpace) :
    (integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w}=
      Set.range (fun q : IntegralCoverCosets H K=>integralCoverFiberPoint H K q w) := by
  ext u
  constructor
  · intro hu
    induction u using Quotient.inductionOn with
    | _ z =>
      have he : integralOrbitProjection K z=integralOrbitProjection K w := hu
      obtain ⟨k,hk⟩ := Quotient.exact he
      refine ⟨(k : IntegralCoverCosets H K),?_⟩
      change integralCoverFiberPoint H K (k : IntegralCoverCosets H K) w=integralOrbitProjection H z
      rw [integralCoverFiberPoint_mk]
      congr 1
      rw [←hk]
      exact inv_smul_smul k z
  · rintro ⟨q,rfl⟩
    exact integralCoverMap_fiberPoint hHK q w
lemma integralCoverMap_preimage_image {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (S : Set (IntegralOrbitQuotient H)) :
    (integralOrbitProjection K) ⁻¹' (integralCoverMap hHK '' S)=
      ⋃q : IntegralCoverCosets H K,(integralCoverFiberPoint H K q) ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨u,hu,huw⟩
    have hh : u∈(integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w} := huw
    rw [integralCoverMap_fiber hHK w] at hh
    obtain ⟨q,rfl⟩ := hh
    exact Set.mem_iUnion.mpr ⟨q,hu⟩
  · intro hw
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hw
    exact ⟨integralCoverFiberPoint H K q w,hq,integralCoverMap_fiberPoint hHK q w⟩
theorem integralCoverMap_isClosedMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] : IsClosedMap (integralCoverMap hHK) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  intro S hS
  have hq : Topology.IsQuotientMap (integralOrbitProjection K) := isQuotientMap_quotient_mk'
  apply hq.isCoinducing.isClosed_preimage.mp
  rw [integralCoverMap_preimage_image]
  exact isClosed_iUnion_of_finite (fun q=>hS.preimage (integralCoverFiberPoint_continuous H K q))
theorem integralCoverMap_isProperMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] : IsProperMap (integralCoverMap hHK) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨integralCoverMap_continuous hHK,integralCoverMap_isClosedMap hHK,?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change IsCompact ((integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w})
    rw [integralCoverMap_fiber hHK w]
    exact (Set.finite_range _).isCompact
theorem integralCoverMap_compact_preimage {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K]
    (S : Set (IntegralOrbitQuotient K)) (hS : IsCompact S) :
    IsCompact ((integralCoverMap hHK) ⁻¹' S) :=
  (integralCoverMap_isProperMap hHK).isCompact_preimage hS
end
section
open MeasureTheory
open scoped Classical MatrixGroups BigOperators
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O
lemma cubeCuspTriangular_norm_sq_pos {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) : 0<‖cubeCuspTriangular d hp 1 1‖^2 := by
  rw [cubeCuspTriangular_norm_sq]
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) _
def cubeReducedRemainder {M:SL(2,Eis)} {p q:Eis} (d:CubeCuspData M p q) (hp:p≠0)
    (z:ℂ) (v:ℝ) (hv:0<v) : ℂ :=
  sourceCuspRemainder d.matrix
    ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/‖cubeCuspTriangular d hp 1 1‖^2) (div_pos hv (cubeCuspTriangular_norm_sq_pos d hp))
end
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O
end
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
lemma integralCoverMap_hasCompactSupport {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient K→ℂ)
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun q=>f (integralCoverMap hHK q)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (integralCoverMap_compact_preimage hHK (tsupport f) hf.isCompact)
  intro q hq
  exact subset_tsupport f hq
lemma integralCoverTraceFunction_hasCompactSupport {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H→ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (integralCoverTraceFunction H K f) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply HasCompactSupport.of_support_subset_isCompact
    (hf.isCompact.image (integralCoverMap_continuous hHK))
  intro q hq
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑r : IntegralCoverCosets H K,f (integralCoverFiberPoint H K r w))≠0 at hq
    obtain ⟨r,_,hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    exact ⟨integralCoverFiberPoint H K r w,subset_tsupport f hr,
      integralCoverMap_fiberPoint hHK r w⟩
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
def kernelCorrespondenceFunction (f : KernelQuotient→ℂ) : KernelQuotient→ℂ :=
  integralCoverTraceFunction H globalKubotaKernel
    (fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q)))
omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_lift (f : KernelQuotient→ℂ) (w : HyperbolicSpace) :
    kernelCorrespondenceFunction hJK e g he f (integralOrbitProjection globalKubotaKernel w)=
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑q : IntegralCoverCosets H globalKubotaKernel,
        f (integralOrbitProjection globalKubotaKernel
          ((g*integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹:
              globalKubotaKernel):SL(2,ActualEisensteinCubic.O)))•w)) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change (∑q : IntegralCoverCosets H globalKubotaKernel,
    f (integralCoverMap hJK (integralConjugateMap e g he
      (integralCoverFiberPoint H globalKubotaKernel q w))))=_
  apply Finset.sum_congr rfl
  intro q _
  rw [integralCoverFiberPoint_rep,integralSubgroup_smul,
    integralConjugateMap_projection,integralCoverMap_projection,mul_smul]
include hHK in
lemma kernelCorrespondenceFunction_hasCompactSupport (f : KernelQuotient→ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (kernelCorrespondenceFunction hJK e g he f) := by
  apply integralCoverTraceFunction_hasCompactSupport hHK
  exact (integralCoverMap_hasCompactSupport hJK f hf).comp_homeomorph
    (integralConjugateHomeomorph e g he)
omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_contMDiff (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelCorrespondenceFunction hJK e g he f) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  apply kernel_contMDiff_of_lift
  simp_rw [kernelCorrespondenceFunction_lift]
  apply ContMDiff.sum
  intro q _
  exact (hf.comp kernelProjection_contMDiff).comp
    (hyperbolicAction_contMDiff (g*integralComplexMatrix
      (((integralCoverRep H globalKubotaKernel q)⁻¹:globalKubotaKernel):SL(2,ActualEisensteinCubic.O))))
def kernelCorrespondenceTest (f : kernelSmoothTests) : kernelSmoothTests :=
  ⟨kernelCorrespondenceFunction hJK e g he f.1,
    kernelCorrespondenceFunction_contMDiff hJK e g he f.1 f.2.1,
    kernelCorrespondenceFunction_hasCompactSupport hHK hJK e g he f.1 f.2.2⟩
end CubicEisenstein
end
end OAI


