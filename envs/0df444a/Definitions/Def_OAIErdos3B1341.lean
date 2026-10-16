-- Prove2me | Definitions.Def_OAIErdos3B1341
-- name    : OAIErdos3B1341
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T23:43:21.271684+00:00
-- url     : https://prove2.me/theorems/d7af6a39-8afc-4ed7-9746-7d86688119ab
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1342 of 1378
-- statement:
--   Definitions bundle 1342 of 1378 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1340`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1342 available.
--
--   Modules: `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedModelData.model_commonFactors_iff`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.AxisFreezing.problem_nativeFactors`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedRebase`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedRebase_ambientScore`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedRebase_candidate_orbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedRebase_candidate_score`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedRebase_candidate_value`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedRebase_centerLift`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedRebase_chart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedRebase_localLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedRebase_productive`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_adaptedRebase`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_adaptedRebase_ambient`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_adaptedRebase_retained`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.exists_withKeep_marked_frozen_symbol_factors`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.withKeep_chart_integerChart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.withKeep_chart_recovered`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.adaptedRebase`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.adaptedRebase_orbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.adaptedRebase_score`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.adaptedRebase_siteValue`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.adaptedRebase_value`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.formal_mark`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.formal_mark_group`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.hasCommonRefilteredOrbitFactors_freezeAxes`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.hasCommonRefilteredOrbitFactors_withKeep`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.mark_log_on_slice`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.axisVariableEquiv`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.degree_lt_slice_length_of_dense`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.hasCommonRefilteredOrbitFactors_axisPolynomial`, `_private.Estimates.AllocatedExternalCandidateKeptSymbolFactors.0.OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.chart_mark_degreeLE`, `_private.Estimates.AllocatedExternalCandidateKeptSymbolFactors.0.OAI.Erdos3.VectorPolynomial.adaptedChart_eq_of_chart_eq`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1336

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFrozenNativeFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

noncomputable section

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

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (adapted : D.AdaptedModelData)

def adaptedRebase : AllocatedExternalLocalCandidate C adapted.model Fmark φ marked where
  orbit := candidate.orbit
  mark_on_slice := candidate.mark_on_slice

@[simp] theorem adaptedRebase_orbit :
    (candidate.adaptedRebase adapted).orbit = candidate.orbit := rfl

@[simp] theorem adaptedRebase_value (u : C.Variables → ℤ) :
    (candidate.adaptedRebase adapted).value u = candidate.value u := rfl

@[simp] theorem adaptedRebase_siteValue (site : A.Site) :
    (candidate.adaptedRebase adapted).siteValue site = candidate.siteValue site := rfl

@[simp] theorem adaptedRebase_score :
    (candidate.adaptedRebase adapted).score observable weight =
      candidate.score observable weight := rfl

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (adapted : D.AdaptedModelData)

def adaptedRebase :
    AllocatedExternalCandidateProblem (E := E) A adapted.model Fmark φ marked observable weight
      cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (P.candidate z).adaptedRebase adapted
  score := P.score

@[simp] theorem adaptedRebase_productive :
    (P.adaptedRebase adapted).productive = P.productive := rfl

@[simp] theorem adaptedRebase_chart (z : P.productive) :
    (P.adaptedRebase adapted).chart z = P.chart z := rfl

@[simp] theorem adaptedRebase_localLaw (z : P.productive) :
    ((P.adaptedRebase adapted).chart z).localLaw = (P.chart z).localLaw := rfl

@[simp] theorem adaptedRebase_centerLift :
    (P.adaptedRebase adapted).centerLift = P.centerLift := rfl

@[simp] theorem adaptedRebase_candidate_orbit (z : P.productive) :
    ((P.adaptedRebase adapted).candidate z).orbit = (P.candidate z).orbit := rfl

@[simp] theorem adaptedRebase_candidate_value (z : P.productive)
    (u : (P.chart z).Variables → ℤ) :
    ((P.adaptedRebase adapted).candidate z).value u = (P.candidate z).value u := rfl

@[simp] theorem adaptedRebase_candidate_score (z : P.productive) :
    ((P.adaptedRebase adapted).candidate z).score observable weight =
      (P.candidate z).score observable weight := rfl

@[simp] theorem adaptedRebase_ambientScore
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) :
    (P.adaptedRebase adapted).ambientScore ambient z points =
      P.ambientScore ambient z points := rfl

def conclusion_of_adaptedRebase {outputCost outputMass outputScore : ℝ}
    (result : (P.adaptedRebase adapted).Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore where
  ambient := result.ambient
  marked := result.marked
  retained := result.retained
  subset := result.subset
  mass := result.mass
  step := result.step
  step_pos := result.step_pos
  slice := result.slice
  dense := result.dense
  inside := result.inside
  score := result.score

@[simp] theorem conclusion_of_adaptedRebase_ambient {outputCost outputMass outputScore : ℝ}
    (result : (P.adaptedRebase adapted).Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_adaptedRebase adapted result).ambient = result.ambient := rfl

@[simp] theorem conclusion_of_adaptedRebase_retained {outputCost outputMass outputScore : ℝ}
    (result : (P.adaptedRebase adapted).Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_adaptedRebase adapted result).retained = result.retained := rfl

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

namespace Erdos3.RationalFilteredNilmanifold.AdaptedModelData

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    {D : RationalFilteredNilmanifold L s d} (adapted : D.AdaptedModelData)
    {σ : Type*} (side : σ → ℝ) (q : ℝ) (den : ℕ)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)

@[simp] theorem model_commonFactors_iff :
    adapted.model.filtration.HasCommonRefilteredOrbitFactors
        adapted.model.basis adapted.weight adapted.model_layers side q den W g ↔
      D.filtration.HasCommonRefilteredOrbitFactors
        adapted.basis adapted.weight adapted.layers side q den W g := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.AdaptedModelData

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M ι : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)

theorem hasCommonRefilteredOrbitFactors_withKeep
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : C.Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) candidate.orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (candidate.withKeep keep hkeep).orbit) := by
  cases hkeep
  exact h

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
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
    {L M ι : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalCandidateProblem

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

end AllocatedExternalCandidateProblem

end Erdos3.VectorPolynomial

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

def axisVariableEquiv : {i // keep i} ≃ {i : C.Variables // keep i.val} where
  toFun i := ⟨⟨i.val, hkeep i.val i.property⟩, i.property⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hkeep in

theorem hasCommonRefilteredOrbitFactors_axisPolynomial
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
    (F : NilpotentLieFiltration L s) (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : C.Variables => (A.sides i.val : ℝ)) q l W g) :
    F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // keep i} => 1) (C.axisPolynomial keep fixed)
        (C.axisPolynomial_support keep fixed) g) := by
  let localKeep : C.Variables → Prop := fun i => keep i.val
  let β := frozenCoordinate localKeep (fun i => (fixed i : ℝ))
  let e := C.axisVariableEquiv keep hkeep
  let γ : {i : C.Variables // localKeep i} → MvPolynomial {i // keep i} ℝ :=
    fun i => MvPolynomial.X (e.symm i)
  have hβ := frozenCoordinate_support localKeep (fun i => (fixed i : ℝ))
  have hγ : ∀ i, γ i ∈ weightedSupportLE (fun _ : {i // keep i} => 1) 1 :=
    fun i => weightedSupportLE_X (fun _ : {i // keep i} => 1) (e.symm i)
  have hf := HasCommonRefilteredOrbitFactors.freeze F bD ω hF localKeep
    (fun i => (fixed i : ℝ)) (fun i : C.Variables => (A.sides i.val : ℝ)) q l W g h
  have hr := HasCommonRefilteredOrbitFactors.reindex F bD ω hF e
    (fun i : {i : C.Variables // localKeep i} => (A.sides i.val.val : ℝ)) q l W
    (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
      (fun _ : {i : C.Variables // localKeep i} => 1) β hβ g) hf
  have hcomp : (fun i => MvPolynomial.aeval γ (β i)) = C.axisPolynomial keep fixed := by
    funext i
    by_cases hi : keep i.val <;>
      simp [β, γ, e, localKeep, frozenCoordinate, axisVariableEquiv, axisPolynomial, hi]
  have hcompose := F.weightedAdaptedRealChartHom_comp
    (fun _ : C.Variables => 1) (fun _ : {i : C.Variables // localKeep i} => 1)
    (fun _ : {i // keep i} => 1) β γ hβ hγ
    (weightedRealChart_comp_support _ _ _ β γ hβ hγ) g
  rw [← hcompose] at hr
  simpa only [hcomp, e, axisVariableEquiv, Equiv.coe_fn_mk] using hr

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost shortCost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

theorem hasCommonRefilteredOrbitFactors_freezeAxes
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : C.Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) candidate.orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).orbit) := by
  change D.filtration.HasCommonRefilteredOrbitFactors bD ω hD _ q l W
    (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
      (D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) candidate.orbit))
  rw [D.filtration.polynomialOrbitRealChart_polynomialCoordinates]
  exact C.hasCommonRefilteredOrbitFactors_axisPolynomial keep hkeep
    D.filtration bD ω hD fixed q l W _ h

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem.AxisFreezing

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

theorem problem_nativeFactors
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (z : P.productive)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (P.candidate z).orbit)) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (freezing.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (freezing.problem.candidate z).orbit) :=
  (P.candidate z).hasCommonRefilteredOrbitFactors_freezeAxes (shortCost := shortCost)
    (keep z) (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
    bD ω hD q l W h

end AllocatedExternalCandidateProblem.AxisFreezing

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateKeptSymbolFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

attribute [local irreducible] realChartSubstitute

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
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

theorem mark_log_on_slice (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    eval₂ (fun i => (u i : ℝ))
      (map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) candidate.orbit.log) =
    eval₂ (fun i => (u i : ℝ))
      (realChartSubstitute (integerSampledRealChart C.integerChart) marked.log) := by
  have he := candidate.mark_on_slice u hu
  rw [← D.filtration.realification.polynomialOrbitRealEval_integer _ candidate.orbit u,
    ← Fmark.realification.polynomialOrbitRealEval_integer _ marked (C.chartValues u)] at he
  have hc := congrArg NilpotentLieBCHGroup.coord he
  rw [eval₂_map, eval₂_realChartSubstitute]
  refine hc.trans ?_
  apply congrArg (fun z => eval₂ z marked.log)
  funext i
  exact (integerSampledRealChart_eval C.integerChart u i).symm

theorem chart_mark_degreeLE :
    DegreeLE (fun _ : C.Variables => 1) t
      (realChartSubstitute (integerSampledRealChart C.integerChart) marked.log) :=
  Fmark.realification.adapted_degreeLE _
    (Fmark.adapted_realChartSubstitute_weightedSupport
      (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
      (integerSampledRealChart C.integerChart) C.integerChart_support marked.adapted)

theorem formal_mark (hlength : ∀ i, max s t < C.slice.length i) :
    map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) candidate.orbit.log =
      realChartSubstitute (integerSampledRealChart C.integerChart) marked.log := by
  refine eq_of_eval₂_eq_on_residueBoxSlice C.slice C.step_pos ?_ ?_ hlength ?_
  · intro α hα
    exact (candidate.orbit.degreeLE.map _ ) α ((le_max_left s t).trans_lt hα)
  · intro α hα
    exact chart_mark_degreeLE α ((le_max_right s t).trans_lt hα)
  · intro j
    exact candidate.mark_log_on_slice _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem formal_mark_group
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (hlength : ∀ i, max s t < C.slice.length i) :
    D.filtration.realPolynomialGroupMap Fmark φ hφ (fun _ : C.Variables => 1)
      (D.filtration.realification.polynomialOrbitCoordinates _ candidate.orbit) =
    Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart) C.integerChart_support
      (Fmark.realification.polynomialOrbitCoordinates _ marked) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact candidate.formal_mark hlength

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalChart

theorem degree_lt_slice_length_of_dense (r : ℕ) {sliceCost : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      sliceCost C.slice.integerPoints)
    (hlong : ∀ i : C.Variables,
      Real.exp (sliceCost + (r : ℝ) + 1) ≤ (A.sides i.val : ℝ)) :
    ∀ i, r < C.slice.length i := by
  intro i
  have hlength := C.slice.length_lower_of_dense C.step_pos hdense i
  have hlower : Real.exp ((r : ℝ) + 1) ≤ (C.slice.length i : ℝ) := by
    calc
      _ = Real.exp (-sliceCost) * Real.exp (sliceCost + (r : ℝ) + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-sliceCost) * (A.sides i.val : ℝ) :=
        mul_le_mul_of_nonneg_left (hlong i) (Real.exp_nonneg _)
      _ ≤ _ := hlength
  have hstrict : (r : ℝ) < (C.slice.length i : ℝ) := by
    linarith [Real.add_one_le_exp ((r : ℝ) + 1)]
  exact_mod_cast hstrict

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

theorem adaptedChart_eq_of_chart_eq
    {V K L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : V → ℕ) (v : K → ℕ)
    (β γ : V → MvPolynomial K ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
    (heq : β = γ) (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w v β hβ g = F.weightedAdaptedRealChartHom w v γ hγ g := by
  cases heq
  rfl

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)

theorem withKeep_chart_integerChart (z : P.productive) :
    ((P.withKeep keep hkeep).chart z).integerChart =
      allocatedFrozenIntegerFullChart B U b o poly hm P.centerLift
        z.val.1.val z.val.2.val (P.chart z).sample keep
        ((P.withKeep keep hkeep).chart z).fixed := by
  change allocatedFrozenIntegerFullChart B U b o poly hm (P.chart z).centerLift
      (P.chart z).path.1.val (P.chart z).path.2.val (P.chart z).sample keep
      ((P.withKeep keep hkeep).chart z).fixed = _
  rw [P.chart_centerLift z, P.chart_path z]

theorem withKeep_chart_recovered (z : P.productive) :
    AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      P.centerLift z.val.1.val z.val.2.val (P.chart z).sample (P.chart z).read := by
  have h := (P.chart z).recovered
  simpa only [P.chart_centerLift z, P.chart_path z] using h

theorem exists_withKeep_marked_frozen_symbol_factors
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν)]
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ den : ℕ, 0 < den ∧ (den : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ den ∧
      ∀ (z : P.productive) (q : ℝ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded),
      (∀ i, s < ((P.withKeep keep hkeep).chart z).slice.length i) →
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.realification.polynomialOrbitCoordinates _
          ((P.withKeep keep hkeep).candidate z).orbit) →
      ∃ El Pl Rl : Fmark.RealPolynomialSymbolGroup (fun _ : {i // keep i} => 1),
        El * Pl * Rl = Fmark.realPolynomialSymbolHom bF ν hF (fun _ => 1)
          (Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
            (fun _ : {i // keep i} => 1)
            (integerSampledRealChart
              (allocatedFrozenIntegerFullChart B U b o poly hm P.centerLift
                z.val.1.val z.val.2.val (P.chart z).sample keep
                ((P.withKeep keep hkeep).chart z).fixed))
            (allocatedFrozenIntegerFullChart_support B U b o poly hm P.centerLift
              z.val.1.val z.val.2.val (P.chart z).sample keep
              ((P.withKeep keep hkeep).chart z).fixed)
            (Fmark.realification.polynomialOrbitCoordinates _ marked)) ∧
        Pl.coord ∈ realificationLieSubalgebra
          (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ => 1)
            (W.map (D.filtration.associatedGradedMap Fmark φ hφ))) ∧
        Fmark.SymbolSlowBound bF ν hF (fun _ => 1)
          (fun i : {i // keep i} => (A.sides i.val : ℝ))
          (Real.exp ((p + 2) ^ 3 + q)) El ∧
        Fmark.SymbolRationalGrid bF ν hF (fun _ => 1) den Rl := by
  obtain ⟨den, hden, hdenBound, hlden, hmap⟩ :=
    D.filtration.exists_common_refiltered_marked_symbol_factors (σ := {i // keep i})
      Fmark bD ω hD bF ν hF φ hφ hH hl hentries hp hsource htarget hHp hlp
  refine ⟨den, hden, hdenBound, hlden, ?_⟩
  intro z q W hlength hfactor
  have hside (i : {i // keep i}) : (0 : ℝ) < A.sides i.val := by
    apply Nat.cast_pos.mpr
    change 0 < Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val
    cases i.val with
    | inl x => exact S.positive
    | inr x => exact allocatedPrincipalSides_pos B U b S x
  obtain ⟨El, Pl, Rl, hprod, hPl, hEl, hRl⟩ :=
    hmap (fun i : {i // keep i} => (A.sides i.val : ℝ)) hside q W
      (D.filtration.realification.polynomialOrbitCoordinates _
        ((P.withKeep keep hkeep).candidate z).orbit) hfactor
  refine ⟨El, Pl, Rl, ?_, hPl, hEl, hRl⟩
  have hmark := ((P.withKeep keep hkeep).candidate z).formal_mark_group hφ
    (by simpa only [max_self] using hlength)
  have hmarked := hprod.trans (congrArg
    (Fmark.realPolynomialSymbolHom bF ν hF (fun _ : {i // keep i} => 1)) hmark)
  apply hmarked.trans
  apply congrArg (Fmark.realPolynomialSymbolHom bF ν hF (fun _ : {i // keep i} => 1))
  apply adaptedChart_eq_of_chart_eq
  exact congrArg integerSampledRealChart (P.withKeep_chart_integerChart keep hkeep z)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end


