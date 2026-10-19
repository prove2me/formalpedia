-- Prove2me | Definitions.Def_OAIE3v2B237
-- name    : OAIE3v2B237
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:49:12.124714+00:00
-- url     : https://prove2.me/theorems/35f7c58c-ebaa-4cfc-9845-cad2468c1a2c
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 242 of 311
-- statement:
--   Definitions bundle 242 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B203`, `OAIE3v2B301`, `OAIE3v2B220` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateRefinementLabels.lean`, `Estimates/AllocatedExternalCandidateTaggedPairFamily.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Geometry/ActualFixedSpatialDenseSliceCenter.lean`, `Geometry/AllocatedExternalLocalChartKeepBounds.lean`, `Geometry/CertifiedFullChartFrozenTerminal.lean`, `Lattices/AllocatedRecoveredIntegerFullChart.lean`, `Probability/AllocatedExternalLocalSliceLaw.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B203
import Definitions.Def_OAIE3v2B301
import Definitions.Def_OAIE3v2B220

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3.NativeReducedIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
  {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K)

noncomputable def globalExpansion :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s K
      (D.globalError (fun _ => B.coordinate) R.code) :=
  (D.globalErrorExpansion (fun _ => B.coordinate) R.code).mono R.global_budget

end Erdos3.NativeReducedIntervalFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedRecoveredIntegerFullChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
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

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_low_residual
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (k : ℕ) (x : LayerSamplerVariables G I n B → ℤ)
    (hx : ∀ z, |(x z : ℝ)| ≤ layerSamplerBox B U b S z)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval
      (fun z => (integerSampledSpatial (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) x z : ℝ))
      (lowTaggedPolynomial J k poly i) - (c (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) x i : ℝ)| ≤ 1 / 8 := by
  rw [allocatedRecoveredIntegerFullChart_spatial, lowTaggedPolynomial_eval]
  exact (h.integerFullChart_residual B U b hb o S hR hσ poly hm hσ1 C hC hchart hp
    c a v sample read x hx (lowTaggedIndex J k i).1 (lowTaggedIndex J k i).2).trans
      (hsmall (lowTaggedIndex J k i).1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators Classical

theorem integerSampledLowTags_freeze {m : ℕ} {X V : Type*}
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial V ℤ) (keep : V → Prop)
    (fixed : {i // ¬keep i} → ℤ) (u : {i // keep i} → ℤ) :
    integerSampledLowTags J k (fun z => freezePolynomial keep fixed (β z)) u =
      integerSampledLowTags J k β (finiteSplitPoint keep u fixed) := by
  funext i
  exact freezePolynomial_eval keep fixed (β (Sum.inr (lowTaggedIndex J k i))) u

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

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_low_residual
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val)
    (k : ℕ) (u : {i // keep i} → ℤ)
    (hu : u ∈ integerBox (fun i : {i // keep i} =>
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val))
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval
      (fun z => (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u z : ℝ))
      (lowTaggedPolynomial J k poly i) - (c (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u i : ℝ)| ≤ 1 / 8 := by
  have hs := integerSampledSpatial_freeze
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) keep fixed u
  have ht := integerSampledLowTags_freeze J k
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) keep fixed u
  change integerSampledSpatial
    (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u = _ at hs
  change integerSampledLowTags J k
    (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u = _ at ht
  rw [hs, ht]
  exact h.integerFullChart_low_residual B U b hb o S hR hσ poly hm hσ1 C hC hchart hsmall hp
    c a v sample read k (finiteSplitPoint keep u fixed)
    (allocatedFrozenParameterBox_bound B U b S keep fixed hfixed u hu) i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRefinementLabels
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

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalLocalCandidate

variable {cost newCost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (step : ℕ) (step_pos : 0 < step)
    (slice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) step)
    (dense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      newCost slice.integerPoints)
    (inside : slice.integerPoints ⊆ C.slice.integerPoints)

noncomputable def refineSlice :
    AllocatedExternalLocalCandidate (C.refineSlice step step_pos slice dense)
      D Fmark φ marked where
  orbit := candidate.orbit
  mark_on_slice u hu := candidate.mark_on_slice u (inside hu)

@[simp] theorem refineSlice_orbit :
    (candidate.refineSlice step step_pos slice dense inside).orbit = candidate.orbit := rfl

@[simp] theorem refineSlice_value (u : C.Variables → ℤ) :
    (candidate.refineSlice step step_pos slice dense inside).value u = candidate.value u := rfl

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

structure Refinement (newCost newMass newScore : ℝ) where
  retained : Finset A.Path
  subset : retained ⊆ P.productive
  mass : newMass ≤ A.law.mass retained
  cost_le : cost ≤ newCost
  step : retained → ℕ
  step_pos : ∀ z, 0 < step z
  slice : ∀ z : retained, ResidueBoxSlice
    (fun i : (P.chart ⟨z.val, subset z.property⟩).Variables => A.sides i.val) (step z)
  dense : ∀ z, IsDenseCommonStrideBox
    (fun i : (P.chart ⟨z.val, subset z.property⟩).Variables => A.sides i.val)
      newCost (slice z).integerPoints
  inside : ∀ z, (slice z).integerPoints ⊆
    (P.chart ⟨z.val, subset z.property⟩).slice.integerPoints
  scoreLower : ∀ z, newScore ≤
    (𝔼 u ∈ (slice z).integerPoints,
      weight ((P.chart ⟨z.val, subset z.property⟩).physical u) *
      observable ((P.chart ⟨z.val, subset z.property⟩).physical u)
        ((P.candidate ⟨z.val, subset z.property⟩).value u)).re

namespace Refinement

variable {P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

noncomputable def problem :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      newCost newMass newScore where
  productive := refinement.retained
  mass := refinement.mass
  chart z := (P.chart ⟨z.val, refinement.subset z.property⟩).refineSlice
    (refinement.step z) (refinement.step_pos z) (refinement.slice z) (refinement.dense z)
  chart_path z := P.chart_path ⟨z.val, refinement.subset z.property⟩
  centerLift := P.centerLift
  chart_centerLift z := P.chart_centerLift ⟨z.val, refinement.subset z.property⟩
  frozen_side z i := (P.frozen_side ⟨z.val, refinement.subset z.property⟩ i).trans
    (Real.exp_le_exp.mpr refinement.cost_le)
  candidate z := (P.candidate ⟨z.val, refinement.subset z.property⟩).refineSlice
    (refinement.step z) (refinement.step_pos z) (refinement.slice z) (refinement.dense z)
    (refinement.inside z)
  score := refinement.scoreLower

@[simp] theorem problem_productive : refinement.problem.productive = refinement.retained := rfl

@[simp] theorem problem_chart_path (z : refinement.retained) :
    (refinement.problem.chart z).path = (P.chart ⟨z.val, refinement.subset z.property⟩).path := rfl

@[simp] theorem problem_chartValues (z : refinement.retained)
    (u : (P.chart ⟨z.val, refinement.subset z.property⟩).Variables → ℤ) :
    (refinement.problem.chart z).chartValues u =
      (P.chart ⟨z.val, refinement.subset z.property⟩).chartValues u := rfl

@[simp] theorem problem_physical (z : refinement.retained)
    (u : (P.chart ⟨z.val, refinement.subset z.property⟩).Variables → ℤ) :
    (refinement.problem.chart z).physical u =
      (P.chart ⟨z.val, refinement.subset z.property⟩).physical u := rfl

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalLocalChartKeepBounds
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

noncomputable def withKeep : AllocatedExternalLocalChart (E := E) A cost where
  path := C.path
  path_supported := C.path_supported
  centerLift := C.centerLift
  center_eq := C.center_eq
  sample := C.sample
  read := C.read
  recovered := C.recovered
  keep := keep
  fixed := hkeep ▸ C.fixed
  fixed_in_box := by cases hkeep; exact C.fixed_in_box
  step := C.step
  step_pos := C.step_pos
  slice := hkeep ▸ C.slice
  dense := by cases hkeep; exact C.dense

@[simp] theorem withKeep_self : C.withKeep C.keep rfl = C := rfl

theorem withKeep_slice_transport {q : ℕ} {outputCost outputScore : ℝ}
    (slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q)
    (hdense : IsDenseCommonStrideBox (fun i : {i // keep i} => A.sides i.val)
      outputCost slice.integerPoints)
    (hinside : slice.integerPoints ⊆ (C.withKeep keep hkeep).slice.integerPoints)
    (f : (X → ℤ) → (X ⊕ (Σ j, J j) → ℤ) → ℂ)
    (hscore : outputScore ≤ (𝔼 u ∈ slice.integerPoints,
      f ((C.withKeep keep hkeep).physical u) ((C.withKeep keep hkeep).chartValues u)).re) :
    ∃ oldSlice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) q,
      IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
        outputCost oldSlice.integerPoints ∧
      oldSlice.integerPoints ⊆ C.slice.integerPoints ∧
      outputScore ≤ (𝔼 u ∈ oldSlice.integerPoints, f (C.physical u) (C.chartValues u)).re := by
  cases hkeep
  exact ⟨slice, hdense, hinside, hscore⟩

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)

noncomputable def withKeep :
    AllocatedExternalLocalCandidate (C.withKeep keep hkeep) D Fmark φ marked := by
  cases hkeep
  exact candidate

@[simp] theorem withKeep_score :
    (candidate.withKeep keep hkeep).score observable weight = candidate.score observable weight := by
  cases hkeep
  rfl

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)

noncomputable def withKeep :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart z := (P.chart z).withKeep keep (hkeep z)
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side z := by
    change ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost
    rw [← hkeep z]
    exact P.frozen_side z
  candidate z := (P.candidate z).withKeep keep (hkeep z)
  score z := by rw [AllocatedExternalLocalCandidate.withKeep_score]; exact P.score z

@[simp] theorem withKeep_chart_keep (z : P.productive) :
    ((P.withKeep keep hkeep).chart z).keep = keep := rfl

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)

theorem slice_transport_of_eq_withKeep
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)
    (C' : AllocatedExternalLocalChart (E := Deck) A cost)
    (hchart : C' = C.withKeep keep hkeep)
    {q : ℕ} {outputCost outputScore : ℝ}
    (slice : ResidueBoxSlice (fun i : C'.Variables => A.sides i.val) q)
    (hdense : IsDenseCommonStrideBox (fun i : C'.Variables => A.sides i.val)
      outputCost slice.integerPoints)
    (hinside : slice.integerPoints ⊆ C'.slice.integerPoints)
    (f : (X → ℤ) → (X ⊕ (Σ j, J j) → ℤ) → ℂ)
    (hscore : outputScore ≤ (𝔼 u ∈ slice.integerPoints,
      f (C'.physical u) (C'.chartValues u)).re) :
    ∃ oldSlice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) q,
      IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
        outputCost oldSlice.integerPoints ∧
      oldSlice.integerPoints ⊆ C.slice.integerPoints ∧
      outputScore ≤ (𝔼 u ∈ oldSlice.integerPoints, f (C.physical u) (C.chartValues u)).re := by
  subst C'
  exact C.withKeep_slice_transport keep hkeep slice hdense hinside f hscore

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold massThreshold' scoreThreshold' : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked
      observable weight cost massThreshold scoreThreshold)
    (Q : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked
      observable weight cost massThreshold' scoreThreshold')

def conclusion_of_chartwise_withKeep
    (hsub : Q.productive ⊆ P.productive)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : Q.productive, (P.chart ⟨z.val, hsub z.property⟩).keep = keep)
    (hchart : ∀ z : Q.productive,
      Q.chart z = (P.chart ⟨z.val, hsub z.property⟩).withKeep keep (hkeep z))
    {outputCost outputMass outputScore : ℝ}
    (result : Q.Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore := by
  have hex (z : result.retained) :
      ∃ slice : ResidueBoxSlice
          (fun i : (P.chart ⟨z.val, hsub (result.subset z.property)⟩).Variables => A.sides i.val)
          (result.step z),
        IsDenseCommonStrideBox
          (fun i : (P.chart ⟨z.val, hsub (result.subset z.property)⟩).Variables => A.sides i.val)
          outputCost slice.integerPoints ∧
        slice.integerPoints ⊆ (P.chart ⟨z.val, hsub (result.subset z.property)⟩).slice.integerPoints ∧
        outputScore ≤ P.ambientScore result.ambient
          ⟨z.val, hsub (result.subset z.property)⟩ slice.integerPoints := by
    exact (P.chart ⟨z.val, hsub (result.subset z.property)⟩).slice_transport_of_eq_withKeep
      keep (hkeep ⟨z.val, result.subset z.property⟩)
      (Q.chart ⟨z.val, result.subset z.property⟩) (hchart ⟨z.val, result.subset z.property⟩)
      (result.slice z) (result.dense z) (result.inside z)
      (fun x y => weight x * observable x (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          y result.ambient))) (result.score z)
  choose slice hdense hinside hscore using hex
  exact {
    ambient := result.ambient
    marked := result.marked
    retained := result.retained
    subset := fun _ hz => hsub (result.subset hz)
    mass := result.mass
    step := result.step
    step_pos := result.step_pos
    slice := slice
    dense := hdense
    inside := hinside
    score := hscore
  }

@[simp] theorem conclusion_of_chartwise_withKeep_retained
    (hsub : Q.productive ⊆ P.productive)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : Q.productive, (P.chart ⟨z.val, hsub z.property⟩).keep = keep)
    (hchart : ∀ z : Q.productive,
      Q.chart z = (P.chart ⟨z.val, hsub z.property⟩).withKeep keep (hkeep z))
    {outputCost outputMass outputScore : ℝ}
    (result : Q.Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_chartwise_withKeep Q hsub keep hkeep hchart result).retained =
      result.retained := rfl

@[simp] theorem conclusion_of_chartwise_withKeep_ambient
    (hsub : Q.productive ⊆ P.productive)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : Q.productive, (P.chart ⟨z.val, hsub z.property⟩).keep = keep)
    (hchart : ∀ z : Q.productive,
      Q.chart z = (P.chart ⟨z.val, hsub z.property⟩).withKeep keep (hkeep z))
    {outputCost outputMass outputScore : ℝ}
    (result : Q.Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_chartwise_withKeep Q hsub keep hkeep hchart result).ambient =
      result.ambient := rfl

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalLocalSliceLaw
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

@[simp] theorem retainedParameter_parameter (u : C.Variables → ℤ) :
    C.retainedParameter (C.parameter u) = u := by
  funext i
  exact finiteSplitPoint_fixed C.keep u C.fixed i

noncomputable abbrev SlicePoint := ↥C.slice.integerPoints

noncomputable def sliceSite (u : C.SlicePoint) : A.Site :=
  C.site u.val (C.slice.integerPoints_subset_integerBox u.property)

@[simp] theorem sliceSite_val (u : C.SlicePoint) :
    (C.sliceSite u).val = C.parameter u.val := rfl

@[simp] theorem physical_sliceSite (u : C.SlicePoint) :
    A.physical C.path (C.sliceSite u) = C.physical u.val := rfl

noncomputable def localLaw : FiniteProbabilityWeights A.Site :=
  (FiniteProbabilityWeights.uniformFinset C.slice.integerPoints C.dense.nonempty).finitePushforward
    C.sliceSite

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

noncomputable def siteValue (site : A.Site) : D.Space :=
  candidate.value (C.retainedParameter site.val)

@[simp] theorem siteValue_sliceSite (u : C.SlicePoint) :
    candidate.siteValue (C.sliceSite u) = candidate.value u.val := by
  unfold siteValue
  rw [C.sliceSite_val, C.retainedParameter_parameter]

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
namespace OAI

universe u

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

noncomputable def fullSlicePoints (S : ResidueBoxSlice N q) : Finset (integerBox N) :=
  Finset.univ.image S.fullSlicePointInIntegerBox

theorem fullSlicePointInIntegerBox_injective (S : ResidueBoxSlice N q) (hq : 0 < q) :
    Function.Injective S.fullSlicePointInIntegerBox := by
  intro u v h
  exact S.integerPoint_injective hq (congrArg Subtype.val h)

theorem fullSlicePoints_image_val (S : ResidueBoxSlice N q) :
    S.fullSlicePoints.image Subtype.val = S.integerPoints := by
  simp only [fullSlicePoints, integerPoints, Finset.image_image]
  rfl

theorem expect_fullSlicePoints (S : ResidueBoxSlice N q) (hq : 0 < q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : integerBox N → V) :
    (𝔼 x ∈ S.fullSlicePoints, f x) = 𝔼 u, f (S.fullSlicePointInIntegerBox u) :=
  Finset.expect_image (S.fullSlicePointInIntegerBox_injective hq).injOn

theorem fullSliceLaw_complexMean_eq_expect_points (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (hq : 0 < q) (f : integerBox N → ℂ) :
    (S.fullSliceLaw hlen).complexMean f = 𝔼 x ∈ S.fullSlicePoints, f x := by
  rw [S.fullSliceLaw_complexMean hlen]
  exact (S.expect_fullSlicePoints hq f).symm

end Erdos3.ResidueBoxSlice

end

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem low_residual
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (k : ℕ) (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val))
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval (fun x => (C.physical u x : ℝ)) (lowTaggedPolynomial J k poly i) -
      (C.centerLift (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k C.integerChart u i : ℝ)| ≤ 1 / 8 := by
  rw [← C.integerChart_spatial]
  exact C.recovered.integerFrozenFullChart_low_residual B U b hb o S hR hσ poly hm
    hσ1 H hH hchart hsmall hp C.centerLift C.path.1.val C.path.2.val C.sample C.read
    C.keep C.fixed C.fixed_in_box k u hu i

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable def fullTaggedPhysicalIntegerPoint {m : ℕ} {X : Type*}
    (J : Fin m → Type*) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (x : X → ℤ) : X ⊕ (Σ j, J j) → ℤ :=
  Sum.elim x (fun a => round (eval (fun i => (x i : ℝ)) (poly a.1) a.2 - c a.1 a.2))

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

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem chartValues_tag_eq_round (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val))
    (j : Fin m) (i : J j) :
    C.chartValues u (Sum.inr ⟨j, i⟩) =
      round (eval (fun x => (C.physical u x : ℝ)) (poly j) i - (C.centerLift j).val i) := by
  have hj : j.val + 1 ≤ m + 1 := by omega
  have hr := C.low_residual hσ1 H hH hchart hsmall hp (m + 1) u hu
    (lowTaggedSlot J (m + 1) j hj i)
  rw [lowTaggedPolynomial_eval] at hr
  simp only [integerSampledLowTags] at hr
  rw [lowTaggedIndex_slot] at hr
  change |eval (fun x => (C.physical u x : ℝ)) (poly j) i - (C.centerLift j).val i -
    (C.chartValues u (Sum.inr ⟨j, i⟩) : ℝ)| ≤ 1 / 8 at hr
  symm
  apply round_eq_iff.mpr
  have hb := abs_le.mp hr
  constructor <;> linarith

theorem chartValues_eq_physicalIntegerPoint (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    C.chartValues u = fullTaggedPhysicalIntegerPoint J poly
      (fun j => (C.centerLift j).val) (C.physical u) := by
  funext a
  rcases a with x | ⟨j, i⟩
  · exact C.chartValues_spatial u x
  · exact C.chartValues_tag_eq_round hσ1 H hH hchart hsmall hp u hu j i

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct NNReal

variable {X : Type*} {J : Fin 0 → Type*}

theorem zeroLayerSpatialChart_support (v : X ⊕ Sigma J) :
    zeroLayerSpatialChart v ∈ weightedSupportLE (fun _ : X => 1)
      (fullTaggedVariableWeight J v) := by
  rcases v with x | a
  · exact weightedSupportLE_X (fun _ : X => 1) x
  · exact Fin.elim0 a.1

namespace PolynomialPatch

variable {V : Type*} {s d : ℕ} (A : PolynomialPatch V s d)

noncomputable def ofZeroLayerShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) : PolynomialPatch X s d :=
  A.ofWeightedChartShearOrbit (fullTaggedVariableWeight J)
    zeroLayerSpatialChart zeroLayerSpatialChart_support g

@[simp] theorem ofZeroLayerShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    (A.ofZeroLayerShearOrbit g).kernel = A.kernel := rfl

@[simp] theorem ofZeroLayerShearOrbit_complexity
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    relativePatchComplexity (A.ofZeroLayerShearOrbit g) = relativePatchComplexity A := rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators NNReal Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
  {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]

structure AllocatedFrozenTaggedContext where
  U : ∀ j, Submodule ℝ (J j → ℝ)
  btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ
  hbtag : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))
  o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))
  R : Fin m → ℝ
  σ : Fin m → ℝ
  S : LayerSamplerScale (G := G) B U btag R σ
  hR : ∀ j, 0 < R j
  hσ : ∀ j, 0 < σ j
  poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)
  hm : ∀ j d, coefficients (poly j) d ∈ U j
  hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  N : X → ℕ
  hN : ∀ x, 0 < N x
  τ : ℝ
  ξ : ℝ
  hτ : 0 < τ
  hτ1 : τ ≤ 1
  hξ : ξ ≤ 1
  hσ1 : ∀ j, σ j ≤ 1
  Cgeo : Fin m → ℝ
  hCgeo : ∀ j, 0 ≤ Cgeo j
  hchart : ∀ j x,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖
  hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8
  periodCap : ℝ
  coverCap : ℝ
  L : ℝ≥0

variable {B}

def AllocatedFrozenTaggedContext.sides
    (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B)
    (keep : LayerSamplerVariables G I n B → Prop) : {i // keep i} → ℕ :=
  fun i => Sum.elim (fun _ : G => Γ.S.value)
    (allocatedPrincipalSides B Γ.U Γ.btag Γ.S) i.val

variable {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG]
  [LieRing MG] [LieAlgebra ℚ MG] {s d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
  [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]

structure AllocatedFrozenTaggedPairInput
    (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B)
    (Deck : Fin m → Type*) (keep : LayerSamplerVariables G I n B → Prop)
    (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
    (p : ℝ) where
  twist : NormalizedPolynomialTwist X (Σ j, J j) Γ.periodCap Γ.coverCap Γ.L
  c : ∀ j, Γ.U j
  a : X → ℤ
  v : Option (LayerSamplerVariables G I n B) × X → ℤ
  hv : v ∈ rectangularWeightIndices 0
    (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B Γ.U Γ.btag Γ.S (fun _ => 0))
      Γ.τ Γ.ξ Γ.N) 1
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ
  hread : AllocatedCenteredFramedRecoveredSampleAt B Γ.U Γ.btag Γ.hbtag Γ.o Γ.S
    Γ.hR Γ.hσ Γ.poly Γ.hm c a v sample read
  fixed : {i // ¬keep i} → ℤ
  hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
    Sum.elim (fun _ : G => Γ.S.value) (allocatedPrincipalSides B Γ.U Γ.btag Γ.S) i.val
  q : ℕ
  Q : ResidueBoxSlice (Γ.sides keep) q
  hq : 0 < q
  hlen : ∀ i, 0 < Q.length i
  hQ : ∀ i, Real.exp (-p) * (Γ.sides keep i : ℝ) ≤ Q.length i
  V : D.Niltest (fun _ : {i // keep i} => 1)
  W : E.Niltest (fun _ : {i // keep i} => 1)
  hp : 0 ≤ p
  hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p
  hvariationBound : (Γ.L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p
  hV : V.ComplexityLE p
  hW : W.ComplexityLE p
  hWnorm : W.normBound ≤ 1
  η : LG →ₗ[ℚ] ℚ
  θ : MG →ₗ[ℚ] ℚ
  hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p
  hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p
  hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
    V.observable (z • x) = CircleFourier.character
      ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x
  hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
    W.observable (z • x) = CircleFourier.character
      ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x
  hK : (Fintype.card {i // keep i} : ℝ) ≤ p
  hbias : Real.exp (-p) ≤ ‖(Q.fullSliceLaw hlen).complexMean (fun t =>
    star (twist.eval Γ.N Γ.poly (integerSampledSpatial
      (allocatedFrozenIntegerFullChart B Γ.U Γ.btag Γ.o Γ.poly Γ.hm c a v sample keep fixed)
      t.val)) * (V.eval t.val * W.eval t.val))‖

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

def frozenTaggedContext
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (periodCap coverCap : ℝ) (Lip : ℝ≥0) :
    AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B where
  U := U
  btag := b
  hbtag := hb
  o := o
  R := R
  σ := σ
  S := S
  hR := hR
  hσ := hσ
  poly := poly
  hm := hm
  hpoly := hpoly
  N := N
  hN := A.size_pos
  τ := τ
  ξ := ξ
  hτ := A.trim_pos
  hτ1 := hτ1
  hξ := hξ
  hσ1 := hσ1
  Cgeo := Cgeo
  hCgeo := hCgeo
  hchart := hchart
  hsmall := hsmall
  periodCap := periodCap
  coverCap := coverCap
  L := Lip

end AllocatedExternalCandidateSampler

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "Γ" => A.frozenTaggedContext hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  periodCap coverCap Lip

namespace AllocatedFrozenTaggedPairInput

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)
    {LG MG LM : Type u} [LieRing LG] [LieAlgebra ℚ LG]
    [LieRing MG] [LieAlgebra ℚ MG] [LieRing LM] [LieAlgebra ℚ LM]
    {s d e t : ℕ} {D : RationalFilteredNilmanifold LG s d}
    {E : RationalFilteredNilmanifold MG s e} {Fmark : NilpotentLieFiltration LM t}
    {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (reference : D.Niltest (fullTaggedVariableWeight (X := X) J))
    (partner : E.Niltest (fullTaggedVariableWeight (X := X) J))
    (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    {p : ℝ} (hp : 0 ≤ p) (hcost : cost ≤ p)
    (hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hV : reference.ComplexityLE p) (hW : partner.ComplexityLE p)
    (hWnorm : partner.normBound ≤ 1)
    (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      reference.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * reference.observable x)
    (hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
      partner.observable (z • x) = CircleFourier.character
        ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * partner.observable x)
    (hK : (Fintype.card C.Variables : ℝ) ≤ p)

def ofCandidate
    (hcorr : Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (C.physical t.val)) *
          (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p where
  twist := twist
  c := C.centerLift
  a := C.path.1.val
  v := C.path.2.val
  hv := by
    change C.path.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using C.path.2.property
  sample := C.sample
  read := C.read
  hread := C.recovered
  fixed := C.fixed
  hfixed := C.fixed_in_box
  q := C.step
  Q := C.slice
  hq := C.step_pos
  hlen := C.slice.length_pos_of_dense C.dense
  hQ := fun i =>
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg (A.sides i.val))).trans
        (C.slice.length_lower_of_dense C.step_pos C.dense i)
  V := reference.withOrbit candidate.orbit
  W := partner.integerChartPullback (fun _ : C.Variables => 1) C.integerChart C.integerChart_support
  hp := hp
  hperiod := hperiod
  hvariationBound := hvariation
  hV := hV
  hW := hW
  hWnorm := hWnorm
  η := η
  θ := θ
  hηheight := hηheight
  hθheight := hθheight
  hη := hη
  hθ := hθ
  hK := hK
  hbias := by
    change Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (integerSampledSpatial C.integerChart t.val)) *
          ((reference.withOrbit candidate.orbit).eval t.val *
            (partner.integerChartPullback (fun _ : C.Variables => 1)
              C.integerChart C.integerChart_support).eval t.val))‖
    simp only [C.integerChart_spatial, Niltest.integerChartPullback_eval,
      Niltest.withOrbit_eval]
    exact hcorr

variable (hcorr : Real.exp (-p) ≤
  ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
    star (twist.eval N poly (C.physical t.val)) *
      (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖)

local notation "candidateInput" => ofCandidate A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  C candidate reference partner twist hp hcost hperiod hvariation hV hW hWnorm
  η θ hηheight hθheight hη hθ hK hcorr

@[simp] theorem ofCandidate_V_orbit :
    (candidateInput).V.orbit = candidate.orbit := rfl

@[simp] theorem ofCandidate_W_orbit :
    (candidateInput).W.orbit =
      (partner.integerChartPullback (fun _ : C.Variables => 1)
        C.integerChart C.integerChart_support).orbit := rfl

end AllocatedFrozenTaggedPairInput

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalLocalChart

theorem withKeep_localLaw {cost : ℝ} {Deck : Fin m → Type*}
    (C : AllocatedExternalLocalChart (E := Deck) A cost)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep) :
    (C.withKeep keep hkeep).localLaw = C.localLaw := by
  cases hkeep
  rfl

end AllocatedExternalLocalChart

structure AllocatedExternalCandidateTaggedPairFamily
    (Deck : Fin m → Type*) (Ω Pivot : Type*) [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    (D : RationalFilteredNilmanifold LG s d₀)
    (E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j))
    (Fmark : NilpotentLieFiltration LM t) (φ : LG →ₗ⁅ℚ⁆ LM)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost p periodCap coverCap : ℝ) (Lip : ℝ≥0) where
  hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  hτ1 : τ ≤ 1
  hξ : ξ ≤ 1
  hσ1 : ∀ j, σ j ≤ 1
  Cgeo : Fin m → ℝ
  hCgeo : ∀ j, 0 ≤ Cgeo j
  hchart : ∀ j x,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖
  hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8
  sourceChart : Ω → AllocatedExternalLocalChart (E := Deck) A cost
  keep_eq : ∀ a, (sourceChart a).keep = keep
  sourceCandidate : ∀ a, AllocatedExternalLocalCandidate (sourceChart a) D Fmark φ marked
  reference : Ω → Pivot → D.Niltest (fullTaggedVariableWeight (X := X) J)
  ambient : ∀ j, (E j).Niltest (fullTaggedVariableWeight (X := X) J)
  selected : ∀ j, (E j).Niltest (fullTaggedVariableWeight (X := X) J)
  selected_orbit : ∀ j, (selected j).orbit = (ambient j).orbit
  twist : Ω → Pivot → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip
  hp : 0 ≤ p
  hcost : cost ≤ p
  hperiod : ∀ a j, (((twist a j).modulus * (twist a j).cover : ℕ) : ℝ) ≤ Real.exp p
  hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p
  hV : ∀ a j, (reference a j).ComplexityLE p
  hW : ∀ j, (selected j).ComplexityLE p
  hWnorm : ∀ j, (selected j).normBound ≤ 1
  η : Pivot → LG →ₗ[ℚ] ℚ
  θ : ∀ j, MG j →ₗ[ℚ] ℚ
  hηheight : ∀ j i, rationalLogHeight (η j (D.basis i)) ≤ p
  hθheight : ∀ j i, rationalLogHeight (θ j ((E j).basis i)) ≤ p
  hη : ∀ a j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
    (reference a j).observable (z • x) = CircleFourier.character
      ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * (reference a j).observable x
  hθ : ∀ j z, z ∈ (E j).filtration.realification.subgroup s → ∀ x,
    (selected j).observable (z • x) = CircleFourier.character
      ((realifyFunctional (θ j) z.coord : ℝ) : CircleFourier.Circle) * (selected j).observable x
  hK : (Fintype.card {i // keep i} : ℝ) ≤ p
  hcorr : ∀ a j,
    let C := (sourceChart a).withKeep keep (keep_eq a)
    let candidate := (sourceCandidate a).withKeep keep (keep_eq a)
    Real.exp (-p) ≤ ‖(sourceChart a).localLaw.complexMean (fun site =>
      star ((twist a j).eval N poly (A.physical (sourceChart a).path site)) *
        ((reference a j).observable (candidate.value (C.retainedParameter site.val)) *
          (selected j).eval (fullTaggedPhysicalIntegerPoint J poly
            (fun k => ((sourceChart a).centerLift k).val)
            (A.physical (sourceChart a).path site))))‖

namespace AllocatedExternalCandidateTaggedPairFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Ω Pivot D E Fmark φ marked
      keep cost p periodCap coverCap Lip)

def context : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B :=
  A.frozenTaggedContext F.hpoly F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    periodCap coverCap Lip

@[simp] theorem context_sides : F.context.sides keep = fun i => A.sides i.val := rfl

def chart (a : Ω) : AllocatedExternalLocalChart (E := Deck) A cost :=
  (F.sourceChart a).withKeep keep (F.keep_eq a)

def candidate (a : Ω) : AllocatedExternalLocalCandidate (F.chart a) D Fmark φ marked :=
  (F.sourceCandidate a).withKeep keep (F.keep_eq a)

@[simp] theorem chart_keep (a : Ω) : (F.chart a).keep = keep := rfl

@[simp] theorem chart_localLaw (a : Ω) : (F.chart a).localLaw = (F.sourceChart a).localLaw := by
  exact (F.sourceChart a).withKeep_localLaw A keep (F.keep_eq a)

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialDenseSliceCenter
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

attribute [instance] ActualFixedSpatialDenseSliceInput.keepDecidable

namespace ActualFixedSpatialDenseSliceInput
variable {s q} (input : ActualFixedSpatialDenseSliceInput s q)

omit [DecidableEq X] in
theorem kernel_kept (g : G) : input.keep (Sum.inl g) :=
  (input.keep_iff _).mpr input.cutoff_le

omit [DecidableEq X] in
theorem active_kept (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) : input.keep (Sum.inr ⟨a.val,p⟩) := by
  apply (input.keep_iff _).mpr
  change q.Hchild ≤ allocatedPrincipalSides B U b S ⟨a.val,p⟩
  rw [allocatedPrincipalSides_not_short B U b S a p]
  exact input.cutoff_le

end ActualFixedSpatialDenseSliceInput

end Erdos3.VectorPolynomial

end

end OAI
end


