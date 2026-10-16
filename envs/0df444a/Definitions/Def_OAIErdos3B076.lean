-- Prove2me | Definitions.Def_OAIErdos3B076
-- name    : OAIErdos3B076
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T00:20:16.061162+00:00
-- url     : https://prove2.me/theorems/d0ce65d8-60fc-4eb2-9229-738444fcbd3c
-- title:
--   OpenAI Erdős-3 split, definitions bundle 77 of 1379
-- statement:
--   Definitions bundle 77 of 1379 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B075`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 77 available.
--
--   Modules: `OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_marked_quotientOrbit_lift`, `OAI.Erdos3.RationalFilteredNilmanifold.optionQuotientMap_mem_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.quotientMap_mem_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.quotientOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.quotientOrbit_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.quotientOrbit_log`, `OAI.Erdos3.RationalFilteredNilmanifold.quotientOrbit_mark`, `OAI.Erdos3.RationalFilteredNilmanifold.quotientOrbit_realEval`, `OAI.Erdos3.RationalFilteredNilmanifold.quotientOrbit_surjective`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.active_kept`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.casesOn`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.kernel_exp_width`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.kernel_geometry`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.kernel_kept`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.length_pos`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.principalLower`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.principalWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.principal_geometry`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.side_pos`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialDenseSliceInput.step_le`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.toDenseSliceMember`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.toDenseSliceMember_center`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.withNumerics`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.withNumerics_slice`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.withNumerics_target`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.withNumerics_targetAt`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.targetAt`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.targetAt_eq_target`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.denseSliceInput`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.denseSliceInput_cost`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.adaptedOptionQuotient`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.ambientPhysicalValue`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.ambientScore_eq_physical`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.chartValues_eq_physicalIntegerPoint`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_adaptedOptionQuotient`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_lieQuotient`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.conclusion_of_optionQuotient`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.lieQuotientProblem`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.lieQuotientProblem_ambientScore`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.lieQuotientProblem_productive`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.optionQuotient`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.optionQuotient_chart`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.optionQuotient_productive`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.physicalIntegerPoint`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.lieQuotient`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.lieQuotient_orbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.lieQuotient_score_eq`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.optionJoint_lieQuotient_log`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.optionJoint_lieQuotient_polynomialCoordinates`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.siteValue_site`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.withKeep_siteValue`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.withOrbit_eval`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.withOrbit_eval_site`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.localLaw_complexMean_eq_fullSliceLaw_site`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1340
import Definitions.Def_OAIErdos3B1341
import Definitions.Def_OAIErdos3B1343

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidatePhysicalScore
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

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    (D : RationalFilteredNilmanifold L r d) (Fmark : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)

namespace AllocatedExternalCandidateProblem
variable {A D Fmark φ marked observable weight cost massThreshold scoreThreshold}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def physicalIntegerPoint (x : X → ℤ) : X ⊕ (Σ j, J j) → ℤ :=
  fullTaggedPhysicalIntegerPoint J poly (fun j => (P.centerLift j).val) x

noncomputable def ambientPhysicalValue
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (x : X → ℤ) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
    (fullTaggedVariableWeight J) (P.physicalIntegerPoint x) ambient)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem chartValues_eq_physicalIntegerPoint (z : P.productive)
    (u : (P.chart z).Variables → ℤ) (hu : u ∈ (P.chart z).slice.integerPoints) :
    (P.chart z).chartValues u = P.physicalIntegerPoint ((P.chart z).physical u) :=
  (P.chart z).chartValues_eq_physicalIntegerPoint_of_center
    hσ1 H hH hchart hsmall hp P.centerLift (P.chart_centerLift z) u hu

theorem ambientScore_eq_physical
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ))
    (hpoints : points ⊆ (P.chart z).slice.integerPoints) :
    P.ambientScore ambient z points =
      (𝔼 u ∈ points, weight ((P.chart z).physical u) *
        observable ((P.chart z).physical u)
          (P.ambientPhysicalValue ambient ((P.chart z).physical u))).re := by
  unfold ambientScore ambientPhysicalValue
  apply congrArg Complex.re
  apply Finset.expect_congr rfl
  intro u hu
  rw [P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u (hpoints hu)]

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t u : ℕ}
    (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0) {w : σ → ℕ}

end Erdos3.NilpotentLieFiltration

end

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

theorem exists_prescribed_marked_quotientOrbit_lift
    (G : NilpotentLieFiltration M u)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hmarked : map
      ((realificationLieHom (quotientInducedMark I π hker)).toLinearMap.restrictScalars ℚ)
      q.log = marked.log) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.quotientOrbit I hI Q hQ g = q ∧
      map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log = marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) π
          (D.filtration.realification.polynomialOrbitRealEval w z g) =
            G.realification.polynomialOrbitRealEval w z marked := by
  obtain ⟨g, hq⟩ := D.quotientOrbit_surjective I hI Q hQ q
  have hformal : map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log =
      marked.log := by
    rw [← D.quotientOrbit_mark I hI Q hQ π hker g, hq]
    exact hmarked
  refine ⟨g, hq, hformal, ?_, ?_⟩
  · intro z
    rw [← hq]
    exact (D.quotientOrbit_realEval I hI Q hQ g z).symm
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom π (eval₂ z g.log) = eval₂ z marked.log
    rw [← hformal]
    exact (eval₂_map (realificationLieHom π).toLinearMap z g.log).symm

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

variable {L M σ X Ω J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [Fintype Ω] [Fintype J]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {s t u d n : ℕ} (D : RationalFilteredNilmanifold L s d)
  (I : LieIdeal ℚ L) (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQ : Q.filtration = D.filtration.quotientLie I hI)

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

theorem lieQuotientProblem_ambientScore
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) :
    (P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).ambientScore
      (D.quotientOrbit ideal hI Q hQ ambient) z points = P.ambientScore ambient z points := by
  unfold ambientScore
  simp only [lieQuotientProblem, D.quotientOrbit_eval, hrecovery]

theorem conclusion_of_lieQuotient
    {outputCost outputMass outputScore : ℝ}
    (lower : (P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).Conclusion
      outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  obtain ⟨ambient, hquotient, hmark, _, _⟩ :=
    D.exists_prescribed_marked_quotientOrbit_lift ideal hI Q hQ φ hker
      Fmark lower.ambient marked lower.marked
  refine ⟨{
    ambient := ambient
    marked := hmark
    retained := lower.retained
    subset := lower.subset
    mass := lower.mass
    step := lower.step
    step_pos := lower.step_pos
    slice := lower.slice
    dense := lower.dense
    inside := lower.inside
    score := ?_
  }⟩
  intro z
  have he := P.lieQuotientProblem_ambientScore ideal hI Q hQ hker descended hrecovery
    ambient ⟨z.val, lower.subset z.property⟩ (lower.slice z).integerPoints
  rw [hquotient] at he
  exact (lower.score z).trans_eq he

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d dQ : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)

include hQ in

theorem quotientMap_mem_layer (j : ℕ) (x : L) (hx : x ∈ D.filtration.layer j) :
    lieQuotientMap ideal x ∈ Q.filtration.layer j := by
  rw [hQ]
  exact D.filtration.quotientLie_mem ideal hI hx

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
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

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration

variable {Pivot : Type v} [Fintype Pivot]
    {L : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))

include hQ in

theorem optionQuotientMap_mem_layer (k : ℕ)
    (x : ∀ i : Option Pivot, optionLieSpace L P i)
    (hx : x ∈ (optionProduct D partners).filtration.layer k) :
    optionMarkedLieMap (lieQuotientMap ideal) x ∈
      (optionProduct Q partners).filtration.layer k := by
  apply (mem_pi_layer (fun i => (optionFactors Q partners i).filtration) k _).mpr
  intro i
  cases i with
  | none =>
    exact D.quotientMap_mem_layer ideal hI Q hQ k (x none)
      ((mem_pi_layer (fun i => (optionFactors D partners i).filtration) k x).mp hx none)
  | some i =>
    exact (mem_pi_layer (fun i => (optionFactors D partners i).filtration) k x).mp hx (some i)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

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
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d dQ : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

theorem optionJoint_lieQuotient_log :
    ((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit.log =
      VectorPolynomial.map
        ((realificationLieHom (optionMarkedLieMap (L := P)
          (lieQuotientMap ideal))).toLinearMap.restrictScalars ℚ)
        (candidate.optionJoint partners partnerOrbit).orbit.log := by
  exact (optionMarkedLieMap_piRealOrbit_log D Q partners (lieQuotientMap ideal)
    (candidate.optionJointLocalOrbits partners partnerOrbit)
    ((candidate.lieQuotient ideal hI Q hQ hker).optionJointLocalOrbits partners partnerOrbit)
    (D.quotientOrbit_log ideal hI Q hQ candidate.orbit).symm (fun _ => rfl)).symm

attribute [local irreducible] NilpotentLieFiltration.realPolynomialGroupMap

theorem optionJoint_lieQuotient_polynomialCoordinates :
    (⟨⟨((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit.log,
        ((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit.property⟩⟩ :
      ((optionProduct Q partners).filtration.realification.adaptedPolynomialFiltration
        (fun _ : C.Variables => 1)).Group) =
      (optionProduct D partners).filtration.realPolynomialGroupMap
        (optionProduct Q partners).filtration
        (optionMarkedLieMap (L := P) (lieQuotientMap ideal))
        (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
        (fun _ : C.Variables => 1)
        ⟨⟨(candidate.optionJoint partners partnerOrbit).orbit.log,
          (candidate.optionJoint partners partnerOrbit).orbit.property⟩⟩ := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [realPolynomialGroupMap_log]
  exact candidate.optionJoint_lieQuotient_log ideal hI Q hQ hker partners partnerOrbit

end AllocatedExternalLocalCandidate
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

theorem conclusion_of_optionQuotient {outputCost outputMass outputScore : ℝ}
    (result : (P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).Conclusion
      outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  exact P.conclusion_of_lieQuotient ideal hI Q hQ hker descended hrecovery
    ((P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).conclusion_of_optionJoint
      partners partnerOrbit result)

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

variable (adapted : (optionProduct Q partners).AdaptedModelData)

def adaptedOptionQuotient :=
  (P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).adaptedRebase adapted

theorem conclusion_of_adaptedOptionQuotient {outputCost outputMass outputScore : ℝ}
    (result : (P.adaptedOptionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery
      adapted).Conclusion outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) :=
  P.conclusion_of_optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery
    ((P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).conclusion_of_adaptedRebase adapted result)

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualSlicedForecastLateData
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact : Type*} [Fintype Vact] [DecidableEq Vact]
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "short" => allocatedShortAxis (I := I) U basis S.value

end Erdos3.VectorPolynomial

end

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3.VectorPolynomial

end

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))

namespace ActualFixedSpatialSlicedForecastPath

noncomputable def targetAt
    {Ppath Pbad Ppres : ℝ}
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice Ppath Pbad Ppres)
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : X → ℤ) : ℂ := by
  let : ∀ p : slice.path.primes, NeZero p.val := slice.path.primeNeZero
  let N := ∏ p : slice.path.primes, p.val ^ slice.path.exponent p.val
  let : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
    (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : slice.path.primes => p.val)
    (fun p : slice.path.primes => slice.path.exponent p.val)
    (fun p : slice.path.primes => slice.path.prescribed p.val)
    (primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective) slice.path.origin
  exact (κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u

@[simp] theorem targetAt_eq_target
    {Ppath Pbad Ppres : ℝ}
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice Ppath Pbad Ppres)
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : integerBox physicalN) :
    slice.targetAt selected hBactive o bW hb originalpoly hmem κ u.val =
      slice.target selected hBactive o bW hb originalpoly hmem κ u := rfl

end ActualFixedSpatialSlicedForecastPath

attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3.VectorPolynomial

end

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

structure ActualFixedSpatialSlicedAdmissiblePath where
  slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
    Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres
  regular : ∀ a, (∃ b0 v0,
    allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < q.Hchild) ∨
    ((∀ i v, q.δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
      (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
     (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩))
  stride : ∀ a i v,
    (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ q.Ptail
  kernelWidth : ∀ g, Real.exp (-q.v) ≤ slice.kernelWidth g

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

end Erdos3.VectorPolynomial

end

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

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

end Erdos3.VectorPolynomial

end

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
variable {s} {qEarly : ActualFixedSpatialSlicedForecastNumerics s}

namespace ActualFixedSpatialSlicedAdmissiblePath

def withNumerics (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qLate where
  slice := path.slice
  regular := by simpa only [hδ, hH] using path.regular
  stride := by simpa only [hTail] using path.stride
  kernelWidth := by simpa only [hv] using path.kernelWidth

omit [Fintype Tsp] in
@[simp] theorem withNumerics_slice (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    (path.withNumerics qLate hδ hH hv hTail).slice = path.slice := rfl

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

@[simp] theorem withNumerics_target (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    (path.withNumerics qLate hδ hH hv hTail).slice.target
      selected s.hBactive o bW hb originalpoly hmem s.κ =
    path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ := rfl

@[simp] theorem withNumerics_targetAt (path : ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
    (qLate : ActualFixedSpatialSlicedForecastNumerics s)
    (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
    (hv : qEarly.v = qLate.v) (hTail : qEarly.Ptail = qLate.Ptail) :
    (path.withNumerics qLate hδ hH hv hTail).slice.targetAt
      selected s.hBactive o bW hb originalpoly hmem s.κ =
    path.slice.targetAt selected s.hBactive o bW hb originalpoly hmem s.κ := rfl

end ActualFixedSpatialSlicedAdmissiblePath

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

end Erdos3.VectorPolynomial

end

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
variable (qEarly qLate : ActualFixedSpatialSlicedForecastNumerics s)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
variable (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
variable (hv : qEarly.v = qLate.v) (hPtail : qEarly.Ptail = qLate.Ptail)

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

structure ActualFixedSpatialDenseSliceInput where
  keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop
  [keepDecidable : DecidablePred keep]
  keep_iff : ∀ k, keep k ↔ q.Hchild ≤
    Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k
  step : ℕ
  step_pos : 0 < step
  box : ResidueBoxSlice
    (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S) k.val) step
  fixed : {k // ¬keep k} → ℤ
  fixed_inside : ∀ k, 0 ≤ fixed k ∧ fixed k <
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℤ)
  commonTuple : G → IntegerScalarCubeBox Empty S.value
  cost : ℝ
  dense : ∀ k, Real.exp (-cost) *
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℝ) ≤ box.length k
  kernel_nonempty : Nonempty G
  cutoff_le : q.Hchild ≤ S.value
  late_floor : 2 ≤ Real.exp (-cost) * (S.value : ℝ)
  density_le : q.δ ≤ Real.exp (-cost)
  active_width : δslice ≤ Real.exp (-cost) / 2
  kernel_log : cost + 1 ≤ q.v
  prescribed_log : cost + 1 ≤ s.Ppres
  stride_cap : 2 * Real.exp cost ≤ q.Ptail

attribute [instance] ActualFixedSpatialDenseSliceInput.keepDecidable

namespace ActualFixedSpatialDenseSliceInput
variable {s q} (input : ActualFixedSpatialDenseSliceInput s q)

theorem side_pos (k : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) :
    0 < Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k := by
  cases k with
  | inl g => exact S.positive
  | inr j => exact allocatedPrincipalSides_pos B U b S j

omit [DecidableEq X] in
theorem length_pos (k : {k // input.keep k}) : 0 < input.box.length k := by
  have hp : (0 : ℝ) < ((Sum.elim (fun _ : G => S.value)
      (allocatedPrincipalSides B U b S) k.val : ℕ) : ℝ) := Nat.cast_pos.mpr (side_pos (S := S) k.val)
  exact Nat.cast_pos.mp ((mul_pos (Real.exp_pos _) hp).trans_le (input.dense k))

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

noncomputable def principalLower
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) : ℝ :=
  (input.box.fiberParameterStart input.fixed (Sum.inr ⟨a.val,p⟩) : ℝ) /
    allocatedPrincipalSides B U b S ⟨a.val,p⟩

noncomputable def principalWidth
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) : ℝ :=
  (ResidueBoxSlice.fiberParameterStride (keep := input.keep) (q := input.step)
    (Sum.inr ⟨a.val,p⟩) : ℝ) *
    (input.box.fiberParameterLength (Sum.inr ⟨a.val,p⟩) - 1 : ℕ) /
      allocatedPrincipalSides B U b S ⟨a.val,p⟩

omit [DecidableEq X] in
theorem kernel_geometry (g : G) :
    2 ≤ input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ ∧
    0 ≤ (input.box.start ⟨Sum.inl g,input.kernel_kept g⟩ : ℝ) / S.value ∧
    Real.exp (-input.cost) / 2 ≤
      (input.step : ℝ) * (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ - 1 : ℕ) / S.value ∧
    (input.box.start ⟨Sum.inl g,input.kernel_kept g⟩ : ℝ) / S.value +
      (input.step : ℝ) * (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ - 1 : ℕ) / S.value < 1 ∧
    (input.step : ℝ) * (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ - 1 : ℕ) / S.value ≤ 1 ∧
    (input.step : ℝ) ≤ 2 * Real.exp input.cost :=
  input.box.denseCoordinate_geometry ⟨Sum.inl g,input.kernel_kept g⟩ input.step_pos
    S.positive (input.dense _) input.late_floor

omit [DecidableEq X] in
theorem principal_geometry
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a})
    (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    0 ≤ input.principalLower a p ∧
      Real.exp (-input.cost) / 2 ≤ input.principalWidth a p ∧
      |input.principalLower a p| + |input.principalWidth a p| ≤ 1 := by
  have heq := allocatedPrincipalSides_not_short B U b S a p
  have hf : 2 ≤ Real.exp (-input.cost) *
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) (Sum.inr ⟨a.val,p⟩) : ℕ) : ℝ) := by
    simpa only [Sum.elim_inr, heq] using input.late_floor
  have hg := input.box.fiberParameter_dense_geometry input.fixed
    (Sum.inr ⟨a.val,p⟩) (input.active_kept a p) input.step_pos
    (side_pos (S := S) _) (input.dense ⟨Sum.inr ⟨a.val,p⟩,input.active_kept a p⟩) hf
  exact ⟨hg.2.1, hg.2.2.1, hg.2.2.2.2⟩

omit [DecidableEq X] in
theorem step_le : (input.step : ℝ) ≤ 2 * Real.exp input.cost := by
  obtain ⟨g⟩ := input.kernel_nonempty
  exact (input.kernel_geometry g).2.2.2.2.2

omit [DecidableEq X] in
theorem kernel_exp_width : Real.exp (-q.v) ≤ Real.exp (-input.cost) / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    Real.exp (-q.v) ≤ Real.exp (-input.cost - 1) := Real.exp_le_exp.mpr (by linarith [input.kernel_log])
    _ = Real.exp (-input.cost) / Real.exp 1 := Real.exp_sub _ _
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) htwo

end ActualFixedSpatialDenseSliceInput

namespace ActualFixedSpatialForecastPath

variable {s q} {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δbase s.P s.Pbad PpresBase)

noncomputable def toDenseSliceMember (input : ActualFixedSpatialDenseSliceInput s q) :
    ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q := by
  classical
  let origin : ∀ p : path.primes, LayerSamplerLongVariables
      (allocatedShortAxis (I := I) U b S.value) G B → ZMod (p.val ^ path.exponent p.val) :=
    fun p v => ((Sum.elim
      (fun g => (input.box.start ⟨Sum.inl g,input.kernel_kept g⟩ : ℤ))
      (fun a => input.box.fiberParameterStart input.fixed (Sum.inr ⟨a.1.val,a.2⟩)) v : ℤ) :
        ZMod (p.val ^ path.exponent p.val))
  have hpres : ((∏ p : path.primes, p.val ^ padicValNat p.val input.step : ℕ) : ℝ) ≤
      Real.exp s.Ppres :=
    (arbitraryStep_prescribed_product_exp_le path.primes path.prime input.step_pos input.step_le).trans
      (Real.exp_le_exp.mpr input.prescribed_log)
  let newpath := path.reparameterize δslice s.Ppres input.commonTuple
    (fun p => padicValNat p input.step) origin hpres
    input.principalLower input.principalWidth
    (fun a p => input.active_width.trans (input.principal_geometry a p).2.1)
    (fun a p => (input.principal_geometry a p).1)
    (fun a p => (input.principal_geometry a p).2.2)
  let slice := newpath.withResidueBoxSlice input.box input.length_pos input.fixed input.fixed_inside
    input.kernel_kept input.active_kept input.step_pos (fun g => (input.kernel_geometry g).1)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨slice, ?_, ?_, ?_⟩
  · intro a
    have hdense (k : {k // input.keep k}) : q.δ *
        ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k.val : ℕ) : ℝ) ≤ input.box.length k :=
      (mul_le_mul_of_nonneg_right input.density_le (Nat.cast_nonneg _)).trans (input.dense k)
    have hregular := input.box.fiberParameter_regular_of_threshold hdense input.step_pos
      (fun k hk => (input.keep_iff k).mpr hk)
      (fun p : B ⟨(selected a).1,Sum.inr (selected a).2⟩ × Fin ((selected a).1.val + 1) =>
        Sum.inr (⟨⟨(selected a).1,Sum.inr (selected a).2⟩,p⟩ : PrincipalTupleIndex B (layerSamplerDegree I n)))
    rcases hregular with ⟨⟨i,v⟩,hsmall⟩ | ⟨hd,hs⟩
    · exact Or.inl ⟨i,v,hsmall⟩
    · exact Or.inr ⟨fun i v => hd (i,v), fun i v => hs (i,v)⟩
  · intro a i v
    exact (Nat.cast_le.mpr (ResidueBoxSlice.fiberParameterStride_le (keep := input.keep)
      (q := input.step) (Sum.inr ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩))).trans
        (input.step_le.trans input.stride_cap)
  · intro g
    exact input.kernel_exp_width.trans (input.kernel_geometry g).2.2.1

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

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

namespace ActualFixedSpatialForecastPath

variable {s q} {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δbase s.P s.Pbad PpresBase)

omit [Fintype Tsp] in

@[simp] theorem toDenseSliceMember_center (input : ActualFixedSpatialDenseSliceInput s q) :
    (path.toDenseSliceMember input).slice.path.center = path.center := rfl

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateDenseSliceInput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {step : ℕ}
    (slice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) step)
    (hstep : 0 < step) (hlen : ∀ i, 0 < slice.length i)
    (hne : slice.integerPoints.Nonempty)

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore)

variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
    {Dmod : ℕ} {Selection : Type} [Fintype Selection]
    {selected : Selection → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
      B U b S Dmod selected τ δslice)
    (qnum : ActualFixedSpatialSlicedForecastNumerics s)
    (z : out.retained)
    (hkeep : ∀ k, (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔
      qnum.Hchild ≤ A.sides k)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (hkernel : Nonempty G)
    (hcutoff : qnum.Hchild ≤ S.value)
    (hlate : 2 ≤ Real.exp (-outputCost) * (S.value : ℝ))
    (hdensity : qnum.δ ≤ Real.exp (-outputCost))
    (hactive : δslice ≤ Real.exp (-outputCost) / 2)
    (hlog : outputCost + 1 ≤ qnum.v)
    (hprescribed : outputCost + 1 ≤ s.Ppres)
    (hstride : 2 * Real.exp outputCost ≤ qnum.Ptail)

noncomputable def denseSliceInput : ActualFixedSpatialDenseSliceInput s qnum := by
  classical
  exact
    { keep := (P.chart ⟨z.val, out.subset z.property⟩).keep
      keep_iff := hkeep
      step := out.step z
      step_pos := out.step_pos z
      box := out.slice z
      fixed := (P.chart ⟨z.val, out.subset z.property⟩).fixed
      fixed_inside := (P.chart ⟨z.val, out.subset z.property⟩).fixed_in_box
      commonTuple := commonTuple
      cost := outputCost
      dense := (out.slice z).length_lower_of_dense (out.step_pos z) (out.dense z)
      kernel_nonempty := hkernel
      cutoff_le := hcutoff
      late_floor := hlate
      density_le := hdensity
      active_width := hactive
      kernel_log := hlog
      prescribed_log := hprescribed
      stride_cap := hstride }

@[simp] theorem denseSliceInput_cost :
    (out.denseSliceInput s qnum z hkeep commonTuple hkernel hcutoff hlate hdensity
      hactive hlog hprescribed hstride).cost = outputCost := rfl

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedSourceEvaluation
namespace OAI

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

theorem localLaw_complexMean_eq_fullSliceLaw_site (f : A.Site → ℂ) :
    C.localLaw.complexMean f =
      (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
        (fun t => f (C.site t.val t.property)) := by
  let f' : (LayerSamplerVariables G I n B → ℤ) → ℂ :=
    fun x => if hx : x ∈ integerBox A.sides then f ⟨x, hx⟩ else 0
  calc
    C.localLaw.complexMean f = C.localLaw.complexMean (fun site => f' site.val) := by
      apply congrArg C.localLaw.complexMean
      funext site
      simp only [f', dif_pos site.property]
    _ = (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
        (fun t => f' (C.parameter t.val)) := C.localLaw_complexMean_eq_fullSliceLaw f'
    _ = _ := by
      apply congrArg (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
      funext t
      simp only [f', dif_pos (C.parameter_mem t.val t.property)]
      rfl

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

@[simp] theorem withKeep_siteValue
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)
    (site : A.Site) :
    (candidate.withKeep keep hkeep).siteValue site = candidate.siteValue site := by
  cases hkeep
  rfl

@[simp] theorem siteValue_site (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    candidate.siteValue (C.site u hu) = candidate.value u := by
  change candidate.value (C.retainedParameter (C.parameter u)) = candidate.value u
  rw [C.retainedParameter_parameter]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {Y : Type*} {w : Y → ℕ} (reference : D.Niltest w)

@[simp] theorem withOrbit_eval (u : C.Variables → ℤ) :
    (reference.withOrbit candidate.orbit).eval u =
      reference.observable (candidate.value u) := rfl

@[simp] theorem withOrbit_eval_site (site : A.Site) :
    (reference.withOrbit candidate.orbit).eval (C.retainedParameter site.val) =
      reference.observable (candidate.siteValue site) := rfl

end AllocatedExternalLocalCandidate

end

end Erdos3.VectorPolynomial

end

end OAI

end


