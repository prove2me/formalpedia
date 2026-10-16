-- Prove2me | Definitions.Def_OAIErdos3B1342
-- name    : OAIErdos3B1342
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T23:38:51.930985+00:00
-- url     : https://prove2.me/theorems/0b9a137a-6586-4af2-b1a5-657495768045
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1343 of 1378
-- statement:
--   Definitions bundle 1343 of 1378 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1341`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1343 available.
--
--   Modules: `OAI.Erdos3.PolynomialPatch.ExternalObservableRegularity.mono`, `OAI.Erdos3.PolynomialPatch.ExternalObservableRegularity.recOn`, `OAI.Erdos3.PolynomialPatch.externalObservableRegularity_of_niltest_complexity`, `OAI.Erdos3.PolynomialPatch.shearObservable_memberNets`, `OAI.Erdos3.SubquadraticPatchSource`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_certified_top_range`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_certified_frozen_top_range`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_top_range`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_long_coeff`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.AxisFreezing.withKeep_slice_dense`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_shearDegreeGlobalization`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.exists_normalizedShearDegreeConclusion`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.normalizedShearDegreeConclusion`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.DegreeGlobalizationAt`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.DegreeGlobalizationAt.mono_input`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.DegreeGlobalizationAt.mono_output`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.degreeGlobalizationAt_zero`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.axisPolynomial_freeze`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.restrictAxes_integerSampledRealChart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.restrictAxes_polynomialOrbitRealChart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.withKeep_dense_of_dense`, `OAI.Erdos3.VectorPolynomial.allocatedNormalizedShearObservableExponent`, `OAI.Erdos3.VectorPolynomial.allocatedRecoveredIntegerFullChart_tag_degree`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientSample_floor_coeff_separate`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientSample_floor_coeff_sum`, `OAI.Erdos3.aeval_frozen_integer_chart`, `OAI.Erdos3.exists_polynomialPatch_external_observable_budget`, `OAI.Erdos3.monomialScale_mapDomain_embedding`, `OAI.Erdos3.normalizedMass_aeval_frozen_integer_chart_le`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1340

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformRelativePatchSource
namespace OAI

section

open Filter
open scoped Topology

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open Filter

end Erdos3

end

section

namespace Erdos3

open Filter
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def SubquadraticPatchSource (k s : ℕ) (κ H₀ K q A₀ B D pmin Csrc : ℝ) : Prop :=
  let μ := levelCoefficient K * Real.log q
  let β := 1 - (gainExponent K - μ) / 2
  ∀ S : APFreeInterval k, pmin ≤ S.parameter →
    A₀ * S.parameter ^ β + Csrc ≤ Real.log (Real.log S.length) →
    ∃ (d M a q₀ : ℕ) (U : ℝ) (A : PolynomialPatch Unit s d),
      0 < q₀ ∧ (∀ n < M, a + q₀ * n < S.length) ∧ 1 ≤ U ∧
      Real.log S.length - U ≤ Real.log M ∧ (A.kernel.lip : ℝ) + 1 ≤ Real.exp U ∧
      Real.log ((d : ℝ) + 1) ≤ B * S.parameter ^ μ * Real.log (2 + S.parameter) ∧
      Real.log U ≤ D * S.parameter ^ (1 / 4 : ℝ) * Real.log (2 + S.parameter) ∧
      let G := κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log S.parameter⌋₊ / 2
      Real.exp (-U) ≤ (𝔼 n : Fin M,
        (intervalIndicator S.points (a + q₀ * n.val) - G * S.density) *
          A.value (fun _ => (n.val : ℝ)))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open Filter

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateAxisChartOrbit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

attribute [local irreducible] polynomialOrbitRealChart realChartSubstitute

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

include hkeep in

theorem axisPolynomial_freeze (p : MvPolynomial (LayerSamplerVariables G I n B) ℝ) :
    freezePolynomial keep (fun i => (C.axisFixed keep fixed i : ℝ)) p =
      MvPolynomial.aeval (C.axisPolynomial keep fixed)
        (freezePolynomial C.keep (fun i => (C.fixed i : ℝ)) p) := by
  unfold freezePolynomial
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => MvPolynomial.aeval f p)
  funext i
  by_cases hk : keep i
  · have hc := hkeep i hk
    simp [frozenCoordinate, axisPolynomial, hk, hc]
  · by_cases hc : C.keep i
    · simp [frozenCoordinate, axisPolynomial, axisFixed, hk, hc]
    · simp [frozenCoordinate, axisFixed, hk, hc]

theorem restrictAxes_integerSampledRealChart :
    integerSampledRealChart (C.restrictAxes keep hkeep fixed hfixed).integerChart =
      fun i => MvPolynomial.aeval (C.axisPolynomial keep fixed)
        (integerSampledRealChart C.integerChart i) := by
  funext i
  change integerSampledRealChart
      (fun z => freezePolynomial keep (C.axisFixed keep fixed)
        (allocatedRecoveredIntegerFullChart B U b o poly hm C.centerLift
          C.path.1.val C.path.2.val C.sample z)) i =
    MvPolynomial.aeval (C.axisPolynomial keep fixed)
      (integerSampledRealChart
        (fun z => freezePolynomial C.keep C.fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm C.centerLift
            C.path.1.val C.path.2.val C.sample z)) i)
  rw [integerSampledRealChart_freeze, integerSampledRealChart_freeze]
  exact C.axisPolynomial_freeze keep hkeep fixed _

theorem restrictAxes_polynomialOrbitRealChart
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (g : F.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)) :
    F.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
      (integerSampledRealChart (C.restrictAxes keep hkeep fixed hfixed).integerChart)
      (C.restrictAxes keep hkeep fixed hfixed).integerChart_support g =
    F.polynomialOrbitRealChart (fun _ : C.Variables => 1) (fun _ => 1)
      (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed)
      (F.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
        (integerSampledRealChart C.integerChart) C.integerChart_support g) := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (F.polynomialOrbitRealChart _ _ _ _ g).log =
    (F.polynomialOrbitRealChart _ _ _ _ (F.polynomialOrbitRealChart _ _ _ _ g)).log
  simp only [polynomialOrbitRealChart_log]
  rw [C.restrictAxes_integerSampledRealChart keep hkeep fixed hfixed]
  exact (realChartSubstitute_comp (integerSampledRealChart C.integerChart)
    (C.axisPolynomial keep fixed) g.log).symm

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartRecoveredTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientSample_floor_coeff_sum
    (sample : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o sample = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) :
    (fun i => mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) (sample j) d i) +
      (fun i => (((coefficientIntegerFloorPolynomial U b o sample c j i).coeff d.val : ℤ) : ℝ)) =
      (c ⟨j, d⟩).val := by
  funext i
  have h := congrArg (fun polynomial : MvPolynomial K ℝ => polynomial.coeff d.val)
    (canonicalCoefficientSample_floor_polynomial_remainder U b hb o sample c hc j i).1
  simp only [coefficientRowPolynomial, monomialArrayPolynomial_coeff _ Subtype.val_injective,
    MvPolynomial.coeff_add,
    mixedLiftPolynomial_coeff _ _ _ _ Subtype.val_injective, coeff_map,
    Int.coe_castRingHom] at h
  exact h.symm

theorem canonicalCoefficientSample_floor_coeff_separate
    (sample : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o sample = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1))
    {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ))
    (hQU : U j ≤ LinearMap.ker Q) {D : ℝ} (hD : 0 < D)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hsmall : ∀ t, |Q (fun i => mixedLiftCoefficient (euclideanSubspace (U j))
      (b j) (o j) (sample j) d i) t| < 1 / D) :
    Q (fun i => (((coefficientIntegerFloorPolynomial U b o sample c j i).coeff d.val : ℤ) : ℝ)) = 0 := by
  apply (separate_kernel Q _ _ hD ?_ (hgrid _) hsmall).2
  rw [canonicalCoefficientSample_floor_coeff_sum U b hb o sample c hc j d]
  exact hQU (c ⟨j, d⟩).property

end Erdos3.VectorPolynomial

namespace Erdos3

theorem monomialScale_mapDomain_embedding {A B : Type*}
    (f : A ↪ B) (T : B → ℝ) (α : A →₀ ℕ) :
    monomialScale T (α.mapDomain f) = monomialScale (fun i => T (f i)) α := by
  exact Finsupp.prod_mapDomain_index_inj f.injective

end Erdos3

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_long_coeff
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T Long : Type*}
    (keep : Long ↪ LayerSamplerVariables G I n B)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D) (hH : 1 ≤ H)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, H ≤ layerSamplerBox B U b S (keep i))
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (α : Long →₀ ℕ) (hα : α ≠ 0) (hdegree : α.degree ≤ j.val + 1) :
    Q (fun i => (((allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)).coeff (α.mapDomain keep) : ℤ) : ℝ)) = 0 := by
  let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
    fun k z => (jointIntegerFrame (a, v) k z : ℝ)
  let d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) :=
    ⟨α.mapDomain keep, by simpa only [Finsupp.degree_mapDomain] using hdegree⟩
  have hc : canonicalCoefficientSample U b hb o sample =
      QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (centeredAffineCoefficientArray U poly hm c frame) :=
    h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
  change Q (fun i => (((coefficientIntegerFloorPolynomial U b o sample
    (centeredAffineCoefficientArray U poly hm c frame) j i).coeff d.val : ℤ) : ℝ)) = 0
  apply canonicalCoefficientSample_floor_coeff_separate U b hb o sample _ hc j d Q hQU hD hgrid
  let M : ℝ := C * (((Fintype.card (I j) : ℝ) + 1) * R j)
  let scale : ℝ := monomialScale (layerSamplerBox B U b S) d.val
  have hscale : 0 < scale := monomialScale_pos _
    (fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S i)) d.val
  have hM : 0 ≤ M := mul_nonneg hC (mul_nonneg (by positivity) (hR j).le)
  have hnorm : ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
      (b j) (o j) (sample j) d i‖ ≤ M / scale := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hM hscale.le)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using
      allocatedLayerLiftCoefficient_radius_bound B U b hR hσ S hσ1 o j hC hchart
        (sample j) (h.2.2.1 j).2 d i
  have hscaleH : H ≤ scale := by
    change H ≤ monomialScale (layerSamplerBox B U b S) (α.mapDomain keep)
    rw [monomialScale_mapDomain_embedding]
    exact le_monomialScale_of_ne_zero _ hH hlong hα
  intro t
  calc
    _ ≤ CQ * ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
        (b j) (o j) (sample j) d i‖ := hQ _ t
    _ ≤ CQ * (M / scale) := mul_le_mul_of_nonneg_left hnorm hCQ
    _ = (CQ * M) / scale := (mul_div_assoc CQ M scale).symm
    _ < 1 / D := (div_lt_div_iff₀ hscale hD).mpr (by
      simpa only [one_mul] using hthreshold.trans_le hscaleH)

theorem allocatedRecoveredIntegerFullChart_tag_degree
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (j : Fin m) (i : J j) :
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)).totalDegree ≤ j.val + 1 :=
  coefficientIntegerFloorPolynomial_degree U b o sample _ j i

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_top_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*}
    (keep : LayerSamplerVariables G I n B → Prop)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    (Ktarget : Submodule ℝ (J j → ℝ)) (hker : LinearMap.ker Q ≤ Ktarget)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D) (hH : 1 ≤ H)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x (homogeneousComponent (j.val + 1)
      (MvPolynomial.map (Int.castRingHom ℝ) (freezePolynomial keep fixed
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
          (Sum.inr ⟨j, i⟩)))))) ∈ Ktarget := by
  apply longChart_frozen_top_eval_mem
    (fun i => allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)) keep fixed (j.val + 1)
    (allocatedRecoveredIntegerFullChart_tag_degree B U b o poly hm c a v sample j)
  intro α hdegree
  apply hker
  apply h.integerFullChart_long_coeff B U b hb o S hR hσ poly hm hσ1 c a v sample read j
    ⟨Subtype.val, Subtype.val_injective⟩ Q hQU hC hCQ hD hH hchart hQ hgrid
    (fun i => hlong i.val i.property) hthreshold α _ hdegree.le
  intro hz
  simp [hz] at hdegree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_certified_frozen_top_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {Bstage p M H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K Bstage blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hBp : Bstage ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop) (hH : 1 ≤ H)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x (homogeneousComponent (fullTaggedVariableWeight J i)
      (integerSampledRealChart
        (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i))) ∈ K := by
  obtain ⟨cs, _, hbudget, hK⟩ := hcertificate
  rw [hK]
  refine ⟨Set.mem_univ _, ?_⟩
  intro constraint hc
  have hspan : U constraint.tag ≤
      span ℝ (Set.range (fun q i => (constraint.generators q i : ℝ))) := by
    apply constraint.retained_le_span U hretained
    intro point hpoint
    rw [hK] at hpoint
    exact hpoint.2 constraint hc
  obtain ⟨d, _, Q, hker, hQ, D, hD, hDbound, hgrid⟩ :=
    exists_rationalTaggedSpanProjection constraint.generators hp (hJ constraint.tag)
      ((hbudget constraint hc).1.trans hBp)
      (fun q i => ((hbudget constraint hc).2 q i).trans hBp)
  have hQU : U constraint.tag ≤ LinearMap.ker Q := by
    rw [hker]
    exact hspan
  have hgrid' : ∀ z : J constraint.tag → ℤ, ∀ t,
      ∃ a : ℤ, (D : ℝ) * Q (fun i => (z i : ℝ)) t = a := by
    intro z t
    obtain ⟨w, hw⟩ := hgrid z
    exact ⟨w t, (hw t).symm⟩
  have hnumeric : Real.exp ((p + 2) ^ 9) *
      (C constraint.tag * (((Fintype.card (I constraint.tag) : ℝ) + 1) * R constraint.tag)) *
        (D : ℝ) < H := by
    have hE := Real.exp_nonneg ((p + 2) ^ 9)
    calc
      _ ≤ Real.exp ((p + 2) ^ 9) * M * (D : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcap constraint.tag) hE)
          (Nat.cast_nonneg D)
      _ ≤ Real.exp ((p + 2) ^ 9) * M * Real.exp ((p + 2) ^ 9) :=
        mul_le_mul_of_nonneg_left hDbound (mul_nonneg hE hM)
      _ = Real.exp ((p + 2) ^ 9) ^ 2 * M := by ring
      _ < H := hthreshold
  exact h.integerFullChart_frozen_top_range B U b hb o S hR hσ poly hm hσ1 c a v sample read
    constraint.tag keep Q hQU _ (le_of_eq hker) (hC constraint.tag)
    (Real.exp_nonneg _) (by exact_mod_cast hD) hH (hchart constraint.tag) hQ hgrid'
    hlong hnumeric fixed x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_certified_top_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {Bstage p M H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K Bstage blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hBp : Bstage ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop) (hH : 1 ≤ H)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x (homogeneousComponent (fullTaggedVariableWeight J i)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) i))) ∈ K := by
  exact h.integerFullChart_certified_frozen_top_range B U b hb o S hR hσ poly hm
    hσ1 c a v sample read K hcertificate hretained hp hBp hJ C hC hchart hM hcap
    keep hH hlong hthreshold fixed x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {G X ι η L : Type} [Fintype G] [Fintype η]
  [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
  (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) =
    projectedIntegerLattice (euclideanSubspace (Utag j)))
  (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
  {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B Utag btag R σ)
  (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {N : X → ℕ} {Bphase Bcertificate p M H : ℝ}

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedZeroLayerDegreeScalarConclusion
namespace OAI

section

namespace Erdos3

open scoped NNReal TensorProduct Classical

namespace PolynomialPatch

variable {V : Type*} {s d : ℕ} (P : PolynomialPatch V s d)
  [Fintype (PolynomialShearIndex P.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]

structure ExternalObservableRegularity (M : ℝ≥0) (p : ℝ) : Prop where
  geometry : (polynomialShearNilmanifold P.weight s P.weight_le).GeometryComplexityLE p
  lip_bound : (P.shearObservableLipBound M : ℝ) ≤ Real.exp p
  lipschitz :
    letI : MetricSpace
      ((polynomialShearFiltration P.weight s P.weight_le).realification.Group ⧸
        polynomialShearRealLattice s P.weight_le) :=
      (polynomialShearNilmanifold P.weight s P.weight_le).metricSpace
    LipschitzWith (P.shearObservableLipBound M) (fun y => (P.shearObservable y : ℂ))
  positive : ∀ y, (P.shearObservable y : ℂ).im = 0 ∧
    0 ≤ (P.shearObservable y : ℂ).re ∧ (P.shearObservable y : ℂ).re ≤ 1

theorem externalObservableRegularity_of_niltest_complexity
    (M : ℝ≥0) (hP : ∀ i, realPolynomialMass (P.form.center i) ≤ M)
    {p : ℝ} (h : (P.shearNiltest M hP).ComplexityLE p) :
    P.ExternalObservableRegularity M p := by
  refine ⟨h.1, ?_, (P.shearNiltest M hP).lipschitz, ?_⟩
  · have hbound := RationalFilteredNilmanifold.Niltest.observable_budget h
    change 2 + 1 + (P.shearObservableLipBound M : ℝ) ≤ Real.exp p at hbound
    linarith
  · exact P.shearNiltest_unitInterval M hP

theorem ExternalObservableRegularity.mono {M : ℝ≥0} {p q : ℝ}
    (h : P.ExternalObservableRegularity M p) (hpq : p ≤ q) :
    P.ExternalObservableRegularity M q where
  geometry := RationalFilteredNilmanifold.GeometryComplexityLE.mono _ h.geometry hpq
  lip_bound := h.lip_bound.trans (Real.exp_le_exp.mpr hpq)
  lipschitz := h.lipschitz
  positive := h.positive

omit [Fintype (PolynomialShearIndex P.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)] in

theorem shearObservable_memberNets {X : Type*} [Fintype X]
    (N : X → ℕ) (hN : ∀ x, 0 < N x) {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖(fun (_ : X → ℤ) y => (P.shearObservable y : ℂ)) x y -
            (fun (_ : X → ℤ) y => (P.shearObservable y : ℂ)) (oc i).val y‖ ≤ η :=
  constantObservable_integerBox_memberNets N hN
    (fun y => (P.shearObservable y : ℂ)) hp e

end PolynomialPatch

theorem exists_polynomialPatch_external_observable_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {V : Type*} {d : ℕ} (P : PolynomialPatch V s d)
      [Fintype (PolynomialShearIndex P.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
      (p : ℝ) (hp : 0 ≤ p), (d : ℝ) ≤ p →
      (∀ i, realPolynomialMass (P.form.center i) ≤ p) →
      (P.kernel.lip : ℝ) ≤ Real.exp p →
      P.ExternalObservableRegularity ⟨p, hp⟩ ((p + 2) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_mass_bounded_patch_niltest_budget s
  refine ⟨C, hC, ?_⟩
  intro V d P _ _ _ _ _ p hp hd hcenters hLip
  let M : ℝ≥0 := ⟨p, hp⟩
  have hM : ∀ i, realPolynomialMass (P.form.center i) ≤ M := hcenters
  exact P.externalObservableRegularity_of_niltest_complexity M hM
    (hbudget P M hM p hp hd le_rfl hLip)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

def DegreeGlobalizationAt (weight : (X → ℤ) → ℂ)
    (degree netExponent : ℕ) (p outputCost : ℝ) : Prop :=
  ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d f : ℕ} (D : RationalFilteredNilmanifold L degree d)
    (Fmark : RationalFilteredNilmanifold M degree f) (φ : L →ₗ⁅ℚ⁆ M),
    (∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j) →
    (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
    (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
    ∀ (marked : Fmark.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
      (observable : (X → ℤ) → D.Space → ℂ) (ℓ : ℝ≥0),
    (ℓ : ℝ) ≤ Real.exp p →
    (∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x)) →
    (∀ x y, (observable x y).im = 0 ∧ 0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1) →
    (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + netExponent) ^ netExponent) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η) →
    (∀ x, ‖weight x‖ ≤ Real.exp p) →
    ∀ P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight p (Real.exp (-p)) (Real.exp (-p)),
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)))

theorem degreeGlobalizationAt_zero (weight : (X → ℤ) → ℂ)
    (netExponent : ℕ) (p : ℝ) : A.DegreeGlobalizationAt (E := E) weight 0 netExponent p p := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  exact P.conclusion_stepZero A D Fmark.filtration φ marked observable weight

theorem DegreeGlobalizationAt.mono_output
    {weight : (X → ℤ) → ℂ} {degree netExponent : ℕ} {p outputCost largerCost : ℝ}
    (rule : A.DegreeGlobalizationAt (E := E) weight degree netExponent p outputCost)
    (hcost : outputCost ≤ largerCost) :
    A.DegreeGlobalizationAt (E := E) weight degree netExponent p largerCost := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  obtain ⟨out⟩ := rule D Fmark φ hφ hsurj hD hF hmap marked observable ℓ
    hℓ hLip hpositive hnet hweight P
  exact ⟨out.mono hcost (Real.exp_le_exp.mpr (neg_le_neg hcost))
    (Real.exp_le_exp.mpr (neg_le_neg hcost))⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

theorem DegreeGlobalizationAt.mono_input
    {weight : (X → ℤ) → ℂ} {degree netExponent : ℕ} {p q outputCost : ℝ}
    (rule : A.DegreeGlobalizationAt (E := E) weight degree netExponent q outputCost)
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    A.DegreeGlobalizationAt (E := E) weight degree netExponent p outputCost := by
  intro L M _ _ _ _ _ _ _ _ d f D Fmark φ hφ hsurj hD hF hmap
    marked observable ℓ hℓ hLip hpositive hnet hweight P
  have hexp : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have hneg : Real.exp (-q) ≤ Real.exp (-p) := Real.exp_le_exp.mpr (neg_le_neg hpq)
  let ref := P.budgetRefinement hpq hneg hneg
  have hnet' : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((q + Real.log (1 / η) + netExponent) ^ netExponent) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η := by
    intro η hη hηone
    obtain ⟨n, hn, oc, hoc⟩ := hnet η hη hηone
    have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hη).mpr hηone)
    refine ⟨n, hn.trans (Real.exp_le_exp.mpr ?_), oc, hoc⟩
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hpq]) netExponent
  obtain ⟨out⟩ := rule D Fmark φ hφ hsurj
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hD hpq)
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono Fmark hF hpq)
    (fun i j => (hmap i j).trans hpq) marked observable ℓ (hℓ.trans hexp)
    hLip hpositive hnet' (fun x => (hweight x).trans hexp) ref.problem
  exact ⟨ref.conclusion out⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {V : Type*} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    {f : (X → ℤ) → ℝ} {lam cost mass score : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost mass score)

theorem conclusion_of_shearDegreeGlobalization
    {M : ℝ≥0} {p outputCost : ℝ} {netExponent : ℕ}
    (hregularity : patch.ExternalObservableRegularity M p)
    (hp : 0 ≤ p) (hcost : cost ≤ p)
    (hmass : Real.exp (-p) ≤ mass) (hscore : Real.exp (-p) ≤ score)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - lam : ℝ) : ℂ)) s netExponent p outputCost) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  let refinement := P.budgetRefinement hcost hmass hscore
  have hweight (x : X → ℤ) : ‖((f x - lam : ℝ) : ℂ)‖ ≤ Real.exp p := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [(hf x).1, hlam.2],
      by linarith [(hf x).2, hlam.1]⟩).trans (Real.one_le_exp hp)
  obtain ⟨out⟩ := rule
    (polynomialShearNilmanifold patch.weight s patch.weight_le)
    (RationalTorus.trivialNilmanifold s) 0
    (fun _ _ _ => Submodule.zero_mem _)
    (fun j y _ => ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩)
    hregularity.geometry (RationalTorus.trivialNilmanifold_geometry s hp)
    (fun _ j => Fin.elim0 j) 1 (fun _ y => (patch.shearObservable y : ℂ))
    (patch.shearObservableLipBound M) hregularity.lip_bound
    (fun _ => hregularity.lipschitz) (fun _ => hregularity.positive)
    (patch.shearObservable_memberNets N A.size_pos hp netExponent)
    hweight refinement.problem
  exact ⟨refinement.conclusion out⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

noncomputable def allocatedNormalizedShearObservableExponent (s : ℕ) : ℕ :=
  (exists_polynomialPatch_external_observable_budget.{0} s).choose

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {V : Type} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    {f : (X → ℤ) → ℝ} {target cost childCost normBudget : ℝ}
    {rankBound : ℕ} {productive : Finset A.Path}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - target : ℝ) : ℂ)) cost
      ((A.law.mass productive /
        ((min rankBound ⌊childCost⌋₊ + 1) * (s + 1) ^ min rankBound ⌊childCost⌋₊ : ℕ)) *
        Real.exp (-normBudget)) (Real.exp (-normBudget)))

theorem exists_normalizedShearDegreeConclusion
    {gainLog gain pGlobal outputCost : ℝ} {netExponent : ℕ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min rankBound ⌊childCost⌋₊)
    (hchildBudget : childCost ≤ normBudget)
    (hcenters : ∀ i, realPolynomialMass (patch.form.center i) ≤ normBudget)
    (hLip : (patch.kernel.lip : ℝ) ≤ Real.exp normBudget)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hReady : gain / 16 < A.law.mass productive)
    (hregularityBudget : (normBudget + 2) ^ allocatedNormalizedShearObservableExponent s ≤ pGlobal)
    (hpGlobal : 0 ≤ pGlobal) (hcost : cost ≤ pGlobal)
    (hscoreBudget : normBudget ≤ pGlobal)
    (hmassBudget : gainLog + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ pGlobal)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - target : ℝ) : ℂ)) s netExponent pGlobal outputCost) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2
    (polynomialShearNilmanifold patch.weight s patch.weight_le).basis
  have hnorm : 0 ≤ normBudget := hchild.trans hchildBudget
  have hdBudget : (d : ℝ) ≤ normBudget :=
    (Nat.cast_le.mpr (hd.trans (min_le_right _ _))).trans
      ((Nat.floor_le hchild).trans hchildBudget)
  have regularity := PolynomialPatch.ExternalObservableRegularity.mono patch
    ((exists_polynomialPatch_external_observable_budget s).choose_spec.2
      patch normBudget hnorm hdBudget hcenters hLip) hregularityBudget
  have hmass := (Real.exp_le_exp.mpr (neg_le_neg hmassBudget)).trans
    (preparedReady_capped_normalized_mass_lower rankBound s hchild hgain hReady
      (normBudget := normBudget))
  exact P.conclusion_of_shearDegreeGlobalization patch regularity hpGlobal hcost hmass
    (Real.exp_le_exp.mpr (neg_le_neg hscoreBudget)) hf htarget rule

noncomputable def normalizedShearDegreeConclusion
    {gainLog gain pGlobal outputCost : ℝ} {netExponent : ℕ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min rankBound ⌊childCost⌋₊)
    (hchildBudget : childCost ≤ normBudget)
    (hcenters : ∀ i, realPolynomialMass (patch.form.center i) ≤ normBudget)
    (hLip : (patch.kernel.lip : ℝ) ≤ Real.exp normBudget)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hReady : gain / 16 < A.law.mass productive)
    (hregularityBudget : (normBudget + 2) ^ allocatedNormalizedShearObservableExponent s ≤ pGlobal)
    (hpGlobal : 0 ≤ pGlobal) (hcost : cost ≤ pGlobal)
    (hscoreBudget : normBudget ≤ pGlobal)
    (hmassBudget : gainLog + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ pGlobal)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (rule : A.DegreeGlobalizationAt (E := E)
      (fun x => ((f x - target : ℝ) : ℂ)) s netExponent pGlobal outputCost) :
    P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)) :=
  Classical.choice (P.exists_normalizedShearDegreeConclusion patch
    hchild hd hchildBudget hcenters hLip hgain hReady hregularityBudget
    hpGlobal hcost hscoreBudget hmassBudget hf htarget rule)

end AllocatedExternalCandidateProblem

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateFrozenStageDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)

theorem withKeep_dense_of_dense {densityCost : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      densityCost C.slice.integerPoints) :
    IsDenseCommonStrideBox (fun i : {i // keep i} => A.sides i.val)
      densityCost (C.withKeep keep hkeep).slice.integerPoints := by
  cases hkeep
  exact hdense

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.AxisFreezing

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)
    (commonKeep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : freezing.problem.productive, (freezing.problem.chart z).keep = commonKeep)

theorem withKeep_slice_dense (z : P.productive) :
    IsDenseCommonStrideBox (fun i : {i // commonKeep i} => A.sides i.val) cost
      (((freezing.problem.withKeep commonKeep hkeep).chart z).slice.integerPoints) :=
  (freezing.problem.chart z).withKeep_dense_of_dense commonKeep (hkeep z)
    (freezing.problem_slice_dense z)

end AllocatedExternalCandidateProblem.AxisFreezing
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FullFrozenChartMass
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial VectorPolynomial

theorem aeval_frozen_integer_chart {σ K : Type*}
    (β : σ → MvPolynomial K ℤ)
    (keep : K → Prop) (fixed : {i // ¬keep i} → ℤ)
    (p : MvPolynomial σ ℝ) :
    aeval (integerSampledRealChart (fun z => freezePolynomial keep fixed (β z))) p =
      freezePolynomial keep (fun i => (fixed i : ℝ))
        (aeval (integerSampledRealChart β) p) := by
  have hchart : integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) =
      fun z => freezePolynomial keep (fun i => (fixed i : ℝ)) (integerSampledRealChart β z) := by
    funext z
    exact integerSampledRealChart_freeze β keep fixed z
  rw [hchart]
  exact (comp_aeval_apply (integerSampledRealChart β)
    (freezePolynomial keep (fun i => (fixed i : ℝ))) p).symm

theorem normalizedMass_aeval_frozen_integer_chart_le {σ K : Type*}
    (β : σ → MvPolynomial K ℤ)
    (keep : K → Prop) (T : K → ℝ) (hT : ∀ i, 0 < T i)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, |(fixed i : ℝ)| ≤ T i.val)
    (p : MvPolynomial σ ℝ) :
    realPolynomialMass
      (scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val)
        (aeval (integerSampledRealChart (fun z => freezePolynomial keep fixed (β z))) p)) ≤
      realPolynomialMass
        (scaleMvPolynomialAxes T (aeval (integerSampledRealChart β) p)) := by
  rw [aeval_frozen_integer_chart]
  exact normalizedMass_freezePolynomial_le keep T hT
    (fun i => (fixed i : ℝ)) hfixed _

end Erdos3

end

end OAI

end


