-- Prove2me | Definitions.Def_OAIErdos3B1338
-- name    : OAIErdos3B1338
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T21:24:41.845412+00:00
-- url     : https://prove2.me/theorems/def90b49-79c8-4fa2-a3ae-ac491370221a
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1339 of 1363
-- statement:
--   Definitions bundle 1339 of 1363 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1337`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1339 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.casesOn`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.conclusion`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.exists_common_label`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.problem`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.problem_chartValues`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.problem_chart_path`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.problem_physical`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.problem_productive`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Refinement.restrictPaths`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_chartwise_withKeep`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_chartwise_withKeep_ambient`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_chartwise_withKeep_retained`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_withKeep`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.exists_common_keep_refinement`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.exists_common_keep_refinement_exp`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.withKeep`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.withKeep_chart_keep`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.refineSlice`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.refineSlice_orbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.refineSlice_value`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.withKeep`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.withKeep_score`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.refineSlice`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.refineSlice_centerLift`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.refineSlice_chartValues`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.refineSlice_integerChart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.refineSlice_parameter`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.refineSlice_path`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.refineSlice_physical`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.slice_transport_of_eq_withKeep`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.withKeep`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.withKeep_chart_fixed`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.withKeep_dense`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.withKeep_original_dense`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.withKeep_polynomialSlowBound`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.withKeep_self`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.withKeep_slice_transport`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B075

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

namespace AllocatedExternalLocalChart

variable {cost newCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (step : ℕ) (step_pos : 0 < step)
    (slice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) step)
    (dense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      newCost slice.integerPoints)

noncomputable def refineSlice : AllocatedExternalLocalChart (E := E) A newCost where
  path := C.path
  path_supported := C.path_supported
  centerLift := C.centerLift
  center_eq := C.center_eq
  sample := C.sample
  read := C.read
  recovered := C.recovered
  keep := C.keep
  fixed := C.fixed
  fixed_in_box := C.fixed_in_box
  step := step
  step_pos := step_pos
  slice := slice
  dense := dense

@[simp] theorem refineSlice_path :
    (C.refineSlice step step_pos slice dense).path = C.path := rfl

@[simp] theorem refineSlice_centerLift :
    (C.refineSlice step step_pos slice dense).centerLift = C.centerLift := rfl

@[simp] theorem refineSlice_integerChart :
    (C.refineSlice step step_pos slice dense).integerChart = C.integerChart := rfl

@[simp] theorem refineSlice_chartValues (u : C.Variables → ℤ) :
    (C.refineSlice step step_pos slice dense).chartValues u = C.chartValues u := rfl

@[simp] theorem refineSlice_parameter (u : C.Variables → ℤ) :
    (C.refineSlice step step_pos slice dense).parameter u = C.parameter u := rfl

@[simp] theorem refineSlice_physical (u : C.Variables → ℤ) :
    (C.refineSlice step step_pos slice dense).physical u = C.physical u := rfl

end AllocatedExternalLocalChart

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

noncomputable def conclusion {outputCost outputMass outputScore : ℝ}
    (out : refinement.problem.Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore where
  ambient := out.ambient
  marked := out.marked
  retained := out.retained
  subset := fun _ hz => refinement.subset (out.subset hz)
  mass := out.mass
  step := out.step
  step_pos := out.step_pos
  slice := out.slice
  dense := out.dense
  inside z := (out.inside z).trans
    (refinement.inside ⟨z.val, out.subset z.property⟩)
  score := out.score

end Refinement
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

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    (D : RationalFilteredNilmanifold L r d) (Fmark : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)

namespace AllocatedExternalCandidateProblem

variable {D Fmark φ marked observable weight cost massThreshold scoreThreshold}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_common_keep_refinement :
    ∃ (keep : LayerSamplerVariables G I n B → Prop)
      (refinement : P.Refinement cost
        (massThreshold / (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B)) scoreThreshold),
      ∀ z : refinement.problem.productive, (refinement.problem.chart z).keep = keep := by
  let code (z : A.Path) : Finset (LayerSamplerVariables G I n B) :=
    if hz : z ∈ P.productive then Finset.univ.filter (P.chart ⟨z, hz⟩).keep else ∅
  obtain ⟨chosen, hmass⟩ := A.law.exists_code_fiber_mass P.productive code
  let retained := P.productive.filter (fun z => code z = chosen)
  have hsub : retained ⊆ P.productive := Finset.filter_subset _ _
  have hmass' : massThreshold / (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B)
      ≤ A.law.mass retained := by
    have hcard : (Fintype.card (Finset (LayerSamplerVariables G I n B)) : ℝ) =
        (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B) := by
      simp only [Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat]
    rw [hcard] at hmass
    exact (div_le_div_of_nonneg_right P.mass (by positivity)).trans hmass
  let refinement : P.Refinement cost
      (massThreshold / (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B)) scoreThreshold :=
    { retained := retained
      subset := hsub
      mass := hmass'
      cost_le := le_rfl
      step := fun z => (P.chart ⟨z.val, hsub z.property⟩).step
      step_pos := fun z => (P.chart ⟨z.val, hsub z.property⟩).step_pos
      slice := fun z => (P.chart ⟨z.val, hsub z.property⟩).slice
      dense := fun z => (P.chart ⟨z.val, hsub z.property⟩).dense
      inside := fun _ => Finset.Subset.refl _
      scoreLower := fun z => P.score ⟨z.val, hsub z.property⟩ }
  refine ⟨fun i => i ∈ chosen, refinement, ?_⟩
  intro z
  change (P.chart ⟨z.val, hsub z.property⟩).keep = _
  have hz : code z.val = chosen := (Finset.mem_filter.mp z.property).2
  have hc : Finset.univ.filter (P.chart ⟨z.val, hsub z.property⟩).keep = chosen := by
    simpa only [code, dite_eq_ite, dif_pos (hsub z.property)] using hz
  funext i
  apply propext
  rw [← hc]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem exists_common_keep_refinement_exp {p : ℝ}
    (hmass : 0 ≤ massThreshold)
    (hdim : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p) :
    ∃ (keep : LayerSamplerVariables G I n B → Prop)
      (refinement : P.Refinement cost (massThreshold * Real.exp (-p)) scoreThreshold),
      ∀ z : refinement.problem.productive, (refinement.problem.chart z).keep = keep := by
  obtain ⟨keep, refinement, hkeep⟩ := P.exists_common_keep_refinement
  have hpow : (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B) ≤ Real.exp p := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card (LayerSamplerVariables G I n B) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
      _ = Real.exp (Fintype.card (LayerSamplerVariables G I n B)) := by
        rw [← Real.exp_nat_mul]
        simp only [mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr hdim
  have hsmall : massThreshold * Real.exp (-p) ≤
      massThreshold / (2 : ℝ) ^ Fintype.card (LayerSamplerVariables G I n B) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hmass (by positivity) hpow
  let smaller : P.Refinement cost (massThreshold * Real.exp (-p)) scoreThreshold :=
    { refinement with mass := hsmall.trans refinement.mass }
  exact ⟨keep, smaller, hkeep⟩

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

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace Refinement
variable {P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

noncomputable def restrictPaths (paths : Finset A.Path)
    (hpaths : paths ⊆ refinement.retained) {mass : ℝ} (hmass : mass ≤ A.law.mass paths) :
    P.Refinement newCost mass newScore where
  retained := paths
  subset := fun _ hz => refinement.subset (hpaths hz)
  mass := hmass
  cost_le := refinement.cost_le
  step z := refinement.step ⟨z.val, hpaths z.property⟩
  step_pos z := refinement.step_pos ⟨z.val, hpaths z.property⟩
  slice z := refinement.slice ⟨z.val, hpaths z.property⟩
  dense z := refinement.dense ⟨z.val, hpaths z.property⟩
  inside z := refinement.inside ⟨z.val, hpaths z.property⟩
  scoreLower z := refinement.scoreLower ⟨z.val, hpaths z.property⟩

theorem exists_common_label {Label : Type*} [Fintype Label] [Nonempty Label]
    (label : refinement.retained → Label) :
    ∃ chosen : Label, ∃ paths : Finset A.Path, ∃ hpaths : paths ⊆ refinement.retained,
      ∃ hmass : newMass / (Fintype.card Label : ℝ) ≤ A.law.mass paths,
        ∀ z : (refinement.restrictPaths paths hpaths hmass).retained,
          label ⟨z.val, hpaths z.property⟩ = chosen := by
  classical
  let code (z : A.Path) : Label :=
    if hz : z ∈ refinement.retained then label ⟨z, hz⟩ else Classical.choice inferInstance
  obtain ⟨chosen, hchosen⟩ := A.law.exists_code_fiber_mass refinement.retained code
  let paths := refinement.retained.filter (fun z => code z = chosen)
  have hpaths : paths ⊆ refinement.retained := Finset.filter_subset _ _
  have hmass : newMass / (Fintype.card Label : ℝ) ≤ A.law.mass paths :=
    (div_le_div_of_nonneg_right refinement.mass (Nat.cast_nonneg _)).trans hchosen
  refine ⟨chosen, paths, hpaths, hmass, ?_⟩
  intro z
  have he := (Finset.mem_filter.mp z.property).2
  simpa only [code, dif_pos (hpaths z.property)] using he

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

noncomputable def conclusion_of_withKeep {outputCost outputMass outputScore : ℝ}
    (result : (P.withKeep keep hkeep).Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore := by
  have hex (z : result.retained) :
      ∃ slice : ResidueBoxSlice
          (fun i : (P.chart ⟨z.val, result.subset z.property⟩).Variables => A.sides i.val)
          (result.step z),
        IsDenseCommonStrideBox
          (fun i : (P.chart ⟨z.val, result.subset z.property⟩).Variables => A.sides i.val)
          outputCost slice.integerPoints ∧
        slice.integerPoints ⊆ (P.chart ⟨z.val, result.subset z.property⟩).slice.integerPoints ∧
        outputScore ≤ P.ambientScore result.ambient ⟨z.val, result.subset z.property⟩
          slice.integerPoints := by
    exact (P.chart ⟨z.val, result.subset z.property⟩).withKeep_slice_transport
      keep (hkeep _) (result.slice z) (result.dense z) (result.inside z)
      (fun x y => weight x * observable x (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          y result.ambient))) (result.score z)
  choose slice hdense hinside hscore using hex
  exact
    { ambient := result.ambient
      marked := result.marked
      retained := result.retained
      subset := result.subset
      mass := result.mass
      step := result.step
      step_pos := result.step_pos
      slice := slice
      dense := hdense
      inside := hinside
      score := hscore }

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

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom

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

theorem withKeep_chart_fixed
    (β : X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ)
    (hfixed : ∀ x : C.Variables → ℝ,
      (fun v => MvPolynomial.eval
        (fun i => MvPolynomial.eval x (integerSampledRealChart C.integerChart i)) (β v)) =
      (fun i => MvPolynomial.eval x (integerSampledRealChart C.integerChart i))) :
    ∀ x : (C.withKeep keep hkeep).Variables → ℝ,
      (fun v => MvPolynomial.eval
        (fun i => MvPolynomial.eval x
          (integerSampledRealChart (C.withKeep keep hkeep).integerChart i)) (β v)) =
      (fun i => MvPolynomial.eval x
        (integerSampledRealChart (C.withKeep keep hkeep).integerChart i)) := by
  cases hkeep
  exact hfixed

theorem withKeep_polynomialSlowBound
    {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (basis : Basis κ ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group)
    (M : ℝ)
    (hslow : F.PolynomialSlowBound basis (fun _ : C.Variables => 1)
      (fun i : C.Variables => (A.sides i.val : ℝ)) M
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support g)) :
    F.PolynomialSlowBound basis (fun _ : (C.withKeep keep hkeep).Variables => 1)
      (fun i : (C.withKeep keep hkeep).Variables => (A.sides i.val : ℝ)) M
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : (C.withKeep keep hkeep).Variables => 1)
        (integerSampledRealChart (C.withKeep keep hkeep).integerChart)
        (C.withKeep keep hkeep).integerChart_support g) := by
  cases hkeep
  exact hslow

theorem withKeep_dense (dCost : ℝ)
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      dCost C.slice.integerPoints) :
    IsDenseCommonStrideBox (fun i : (C.withKeep keep hkeep).Variables => A.sides i.val)
      dCost (C.withKeep keep hkeep).slice.integerPoints := by
  cases hkeep
  exact hdense

theorem withKeep_original_dense :
    IsDenseCommonStrideBox (fun i : (C.withKeep keep hkeep).Variables => A.sides i.val)
      cost (C.withKeep keep hkeep).slice.integerPoints :=
  C.withKeep_dense keep hkeep cost C.dense

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI

end


