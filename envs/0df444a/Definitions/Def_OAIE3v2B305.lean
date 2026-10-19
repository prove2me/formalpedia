-- Prove2me | Definitions.Def_OAIE3v2B305
-- name    : OAIE3v2B305
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:38:10.048992+00:00
-- url     : https://prove2.me/theorems/a86bbc57-fc3b-4df2-8c43-15377a3679ab
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 273 of 311
-- statement:
--   Definitions bundle 273 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B264` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateAdaptedOptionQuotientFactors.lean`, `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidateFrozenNativeFactors.lean`, `Estimates/AllocatedExternalCandidateTaggedPairUniformFactors.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B264

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

structure AxisFreezing
    (keep : P.productive → LayerSamplerVariables G I n B → Prop) (shortCost : ℝ) where
  keep_subset : ∀ z i, keep z i → (P.chart z).keep i
  removed_side : ∀ z (i : (P.chart z).Variables),
    ¬keep z i.val → (A.sides i.val : ℝ) ≤ Real.exp shortCost
  fixed : ∀ z, {i : (P.chart z).Variables // ¬keep z i.val} → ℤ
  fixed_mem : ∀ z i, fixed z i ∈ integerProgressionSupport
    ((P.chart z).slice.start i.val : ℤ) (P.chart z).step ((P.chart z).slice.length i.val)
  score_mono : ∀ z, (P.candidate z).score observable weight ≤
    (P.candidate z).freezeAxesScore (shortCost := shortCost) (keep z) (keep_subset z)
      (fixed z) (fixed_mem z) observable weight

namespace AxisFreezing

variable {P} {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

noncomputable abbrev problem :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      (max cost shortCost) massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart z := (P.chart z).freezeAxes (shortCost := shortCost) (keep z)
    (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side z i := by
    by_cases hi : (P.chart z).keep i.val
    · exact (freezing.removed_side z ⟨i.val, hi⟩ i.property).trans
        (Real.exp_le_exp.mpr (le_max_right _ _))
    · exact (P.frozen_side z ⟨i.val, hi⟩).trans
        (Real.exp_le_exp.mpr (le_max_left _ _))
  candidate z := (P.candidate z).freezeAxes (shortCost := shortCost) (keep z)
    (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
  score z := by
    change scoreThreshold ≤ (P.candidate z).freezeAxesScore (shortCost := shortCost)
      (keep z) (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
      observable weight
    exact (P.score z).trans (freezing.score_mono z)

@[simp] theorem problem_productive : freezing.problem.productive = P.productive := rfl

@[simp] theorem problem_centerLift : freezing.problem.centerLift = P.centerLift := rfl

@[simp] theorem problem_chart (z : P.productive) :
    freezing.problem.chart z = (P.chart z).freezeAxes (shortCost := shortCost) (keep z)
      (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z) := rfl

@[simp] theorem problem_chart_keep (z : P.productive) :
    (freezing.problem.chart z).keep = keep z := rfl

@[simp] theorem problem_slice_length (z : P.productive)
    (i : (freezing.problem.chart z).Variables) :
    (freezing.problem.chart z).slice.length i =
      (P.chart z).slice.length
        ((P.chart z).keptInclusion (keep z) (freezing.keep_subset z) i) := rfl

@[simp] theorem problem_candidate (z : P.productive) :
    freezing.problem.candidate z = (P.candidate z).freezeAxes (shortCost := shortCost) (keep z)
      (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z) := rfl

end AxisFreezing

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQ : Q.filtration = D.filtration.quotientLie I hI) {w : σ → ℕ}

noncomputable def quotientOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit I hI g
  polynomialOrbitOfLog q.log (by rw [hQ]; exact q.adapted)

@[simp] theorem quotientOrbit_log (g : D.filtration.realification.PolynomialOrbit w) :
    (D.quotientOrbit I hI Q hQ g).log =
      VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
        g.log := rfl

theorem quotientOrbit_surjective :
    Function.Surjective (D.quotientOrbit I hI Q hQ (w := w)) := by
  intro q
  let q₀ : (D.filtration.quotientLie I hI).realification.PolynomialOrbit w :=
    polynomialOrbitOfLog q.log (by rw [← hQ]; exact q.adapted)
  obtain ⟨g, hg⟩ := D.filtration.realQuotientPolynomialOrbit_surjective I hI q₀
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  exact congrArg (fun p => p.log) hg

theorem quotientOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (D.quotientOrbit I hI Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitEval w x g) := by
  exact D.filtration.realQuotientPolynomialOrbit_eval I hI g x

theorem quotientOrbit_realEval (g : D.filtration.realification.PolynomialOrbit w) (z : σ → ℝ) :
    Q.filtration.realification.polynomialOrbitRealEval w z (D.quotientOrbit I hI Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitRealEval w z g) := by
  exact D.filtration.realQuotientPolynomialOrbit_realEval I hI g z

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t u d n : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (I : LieIdeal ℚ L) (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
    (hQ : Q.filtration = D.filtration.quotientLie I hI)
    (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0) {w : σ → ℕ}

theorem quotientOrbit_mark (g : D.filtration.realification.PolynomialOrbit w) :
    map ((realificationLieHom (quotientInducedMark I π hker)).toLinearMap.restrictScalars ℚ)
      (D.quotientOrbit I hI Q hQ g).log =
      map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log := by
  rw [D.quotientOrbit_log I hI Q hQ]
  apply coefficients.injective
  ext a
  simp only [coefficients_map]
  exact quotientInducedMark_real_mk I π hker (coefficients g.log a)

end Erdos3.RationalFilteredNilmanifold

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t dQ : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

def lieQuotient :
    AllocatedExternalLocalCandidate C Q Fmark (quotientInducedMark ideal φ hker) marked where
  orbit := D.quotientOrbit ideal hI Q hQ candidate.orbit
  mark_on_slice u hu := by
    rw [D.quotientOrbit_eval ideal hI Q hQ]
    have hcompose :
        realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.lowerCentralSeries_eq_bot) (quotientInducedMark ideal φ hker)
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal)
            (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) =
        realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.lowerCentralSeries_eq_bot) φ
          (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit) := by
      apply NilpotentLieBCHGroup.ext
      exact quotientInducedMark_real_mk ideal φ hker _
    exact hcompose.trans (candidate.mark_on_slice u hu)

@[simp] theorem lieQuotient_orbit :
    (candidate.lieQuotient ideal hI Q hQ hker).orbit =
      D.quotientOrbit ideal hI Q hQ candidate.orbit := rfl

theorem lieQuotient_score_eq
    (observable : (X → ℤ) → D.Space → ℂ) (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))
    (weight : (X → ℤ) → ℂ) :
    (candidate.lieQuotient ideal hI Q hQ hker).score descended weight =
      candidate.score observable weight := by
  unfold score
  simp only [value, lieQuotient_orbit, D.quotientOrbit_eval, hrecovery]

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked
      observable weight cost massThreshold scoreThreshold)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))

def lieQuotientProblem :
    AllocatedExternalCandidateProblem (E := Deck) A Q Fmark
      (quotientInducedMark ideal φ hker) marked
      descended weight cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (P.candidate z).lieQuotient ideal hI Q hQ hker
  score z := by
    rw [(P.candidate z).lieQuotient_score_eq ideal hI Q hQ hker
      observable descended hrecovery weight]
    exact P.score z

@[simp] theorem lieQuotientProblem_productive :
    (P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).productive = P.productive := rfl

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

section

universe u v

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

namespace AllocatedExternalCandidateProblem

variable {Pivot : Type v} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    {s d : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold LG s d}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (partners : ∀ j, RationalFilteredNilmanifold (MG j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

variable (ideal : LieIdeal ℚ LG)
    (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    {dQ : ℕ} (Q : RationalFilteredNilmanifold (LG ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))

def optionQuotient :=
  (P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).optionJoint
    partners partnerOrbit

@[simp] theorem optionQuotient_productive :
    (P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).productive =
      P.productive := rfl

@[simp] theorem optionQuotient_chart (z : P.productive) :
    (P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).chart z =
      P.chart z := rfl

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

structure AllocatedExternalCandidateSpatialNativeFamily
    (Deck : Fin m → Type*) (Ω Pivot : Type*) [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ}
    (D : RationalFilteredNilmanifold LG s d₀)
    (Fmark : NilpotentLieFiltration LM t) (φ : LG →ₗ⁅ℚ⁆ LM)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost p pLocal pNative r periodCap coverCap : ℝ) (Lip : ℝ≥0) where
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
  nativeValue : Pivot → integerBox N → ℂ
  native : ∀ j, NativeSampleModel (fun _ : X => 1) s pNative
    (fun x : integerBox N => x.val) (nativeValue j)
  twist : Ω → Pivot → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip
  hp : 0 ≤ p
  hpLocal : 0 ≤ pLocal
  hr : 0 ≤ r
  hcost : cost ≤ p
  hlocal : pLocal ≤ p
  hnative : pNative ≤ p
  hperiod : ∀ a j, (((twist a j).modulus * (twist a j).cover : ℕ) : ℝ) ≤ Real.exp p
  hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p
  hV : ∀ a j, (reference a j).ComplexityLE pLocal
  η : Pivot → LG →ₗ[ℚ] ℚ
  hηheight : ∀ j i, rationalLogHeight (η j (D.basis i)) ≤ p
  hη : ∀ a j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
    (reference a j).observable (z • x) = CircleFourier.character
      ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * (reference a j).observable x
  hK : (Fintype.card {i // keep i} : ℝ) ≤ p

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

def chart (a : Ω) : AllocatedExternalLocalChart (E := Deck) A cost :=
  (F.sourceChart a).withKeep keep (F.keep_eq a)

def candidate (a : Ω) : AllocatedExternalLocalCandidate (F.chart a) D Fmark φ marked :=
  (F.sourceCandidate a).withKeep keep (F.keep_eq a)

def jointOrbit (a : Ω) : ∀ i : Option Pivot,
    (optionFactors D (fun j => (F.native j).model) i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keep i} => 1)
  | none => (F.candidate a).orbit
  | some j => (((F.native j).test.fullTaggedSpatial J).integerChartPullback
      (fun _ : {i // keep i} => 1)
      (F.chart a).integerChart (F.chart a).integerChart_support).orbit

def physicalBox (a : Ω) (u : integerBox (fun i : {i // keep i} => A.sides i.val)) :
    integerBox N :=
  ⟨A.physical (F.chart a).path ((F.chart a).site u.val u.property),
    A.physical_mem_integerBox F.hξ _ _⟩

@[simp] theorem physicalBox_val (a : Ω)
    (u : integerBox (fun i : {i // keep i} => A.sides i.val)) :
    (F.physicalBox a u).val = (F.chart a).physical u.val := rfl

def sitePhysicalBox (a : Ω) (site : A.Site) : integerBox N :=
  ⟨A.physical (F.sourceChart a).path site,
    A.physical_mem_integerBox F.hξ _ _⟩

def correlation (a : Ω) (j : Pivot) : ℂ :=
  (F.sourceChart a).localLaw.complexMean (fun site =>
    star ((F.twist a j).eval N poly (F.sitePhysicalBox a site).val) *
      ((F.reference a j).observable ((F.sourceCandidate a).siteValue site) *
        F.nativeValue j (F.sitePhysicalBox a site)))

@[simp] theorem chart_localLaw (a : Ω) :
    (F.chart a).localLaw = (F.sourceChart a).localLaw :=
  (F.sourceChart a).withKeep_localLaw A keep (F.keep_eq a)

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

def withBudget (q : ℝ) (hpq : p ≤ q) :
    AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost q pLocal pNative r periodCap coverCap Lip where
  hpoly := F.hpoly
  hτ1 := F.hτ1
  hξ := F.hξ
  hσ1 := F.hσ1
  Cgeo := F.Cgeo
  hCgeo := F.hCgeo
  hchart := F.hchart
  hsmall := F.hsmall
  sourceChart := F.sourceChart
  keep_eq := F.keep_eq
  sourceCandidate := F.sourceCandidate
  reference := F.reference
  nativeValue := F.nativeValue
  native := F.native
  twist := F.twist
  hp := F.hp.trans hpq
  hpLocal := F.hpLocal
  hr := F.hr
  hcost := F.hcost.trans hpq
  hlocal := F.hlocal.trans hpq
  hnative := F.hnative.trans hpq
  hperiod := fun a j => (F.hperiod a j).trans (Real.exp_le_exp.mpr hpq)
  hvariation := F.hvariation.trans (Real.exp_le_exp.mpr hpq)
  hV := F.hV
  η := F.η
  hηheight := fun j i => (F.hηheight j i).trans hpq
  hη := F.hη
  hK := F.hK.trans hpq

@[simp] theorem withBudget_sourceChart (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).sourceChart = F.sourceChart := rfl

@[simp] theorem withBudget_sourceCandidate (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).sourceCandidate = F.sourceCandidate := rfl

@[simp] theorem withBudget_reference (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).reference = F.reference := rfl

@[simp] theorem withBudget_nativeValue (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).nativeValue = F.nativeValue := rfl

@[simp] theorem withBudget_native (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).native = F.native := rfl

@[simp] theorem withBudget_twist (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).twist = F.twist := rfl

@[simp] theorem withBudget_eta (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).η = F.η := rfl

@[simp] theorem withBudget_chart (q : ℝ) (hpq : p ≤ q) (a : Ω) :
    (F.withBudget q hpq).chart a = F.chart a := rfl

@[simp] theorem withBudget_candidate (q : ℝ) (hpq : p ≤ q) (a : Ω) :
    (F.withBudget q hpq).candidate a = F.candidate a := rfl

@[simp] theorem withBudget_jointOrbit (q : ℝ) (hpq : p ≤ q) (a : Ω) :
    (F.withBudget q hpq).jointOrbit a = F.jointOrbit a := rfl

@[simp] theorem withBudget_correlation (q : ℝ) (hpq : p ≤ q) (a : Ω) (j : Pivot) :
    (F.withBudget q hpq).correlation a j = F.correlation a j := rfl

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors
namespace OAI

universe u

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateTaggedPairFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
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
    {H : Finset Ω}

def longJointOrbit
    {Λ : Type*}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Λ Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop) (a : Λ) :
    ∀ i : Option Pivot, (optionFactors D E i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keepLong i} => 1) :=
  fun i => (optionFactors D E i).filtration.polynomialOrbitRealChart
    (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
    ((F.chart a).axisPolynomial keepLong (fun _ => 0))
    ((F.chart a).axisPolynomial_support keepLong (fun _ => 0)) (F.jointOrbit a i)

def extendedLongJointOrbit
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop) (a : Ω) :
    ∀ i : Option Pivot, (optionFactors D E i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keepLong i} => 1) :=
  if ha : a ∈ H then F.longJointOrbit keepLong ⟨a, ha⟩ else fun _ => 1

omit [Fintype Ω] in
@[simp] theorem extendedLongJointOrbit_mem
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop) (a : Ω) (ha : a ∈ H) :
    F.extendedLongJointOrbit keepLong a = F.longJointOrbit keepLong ⟨a, ha⟩ := by
  simp only [extendedLongJointOrbit, dif_pos ha]

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end


