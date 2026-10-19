-- Prove2me | Definitions.Def_OAIE3v2B276
-- name    : OAIE3v2B276
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:18:41.927428+00:00
-- url     : https://prove2.me/theorems/99da3587-eb8d-43d9-af60-c55075aa18a3
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 288 of 311
-- statement:
--   Definitions bundle 288 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B306`, `OAIE3v2B307`, `OAIE3v2B270`, `OAIE3v2B271`, `OAIE3v2B272` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidatePrecenterPaths.lean`, `Estimates/AllocatedExternalCandidateAdaptedOptionQuotientFactors.lean`, `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidateLocalFixedCenterFront.lean`, `Estimates/AllocatedExternalCandidateThresholdSuccessor.lean`, `Estimates/AllocatedFrozenPrefixStageData.lean`, `Estimates/AllocatedOrdinaryLongPhysicalTerminalConclusion.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeAdaptedConclusion.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry.lean`, `Lattices/CertifiedAffineCutoffCost.lean`, `Linear/AllocatedExternalCandidateCommonKeepPositiveKernelPreparation.lean`, `Nilpotent/AllocatedCandidateHistoryLocalNiltests.lean`, `Polynomial/AllocatedExternalCandidateFixedCenterDegreeModel.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B306
import Definitions.Def_OAIE3v2B307
import Definitions.Def_OAIE3v2B270
import Definitions.Def_OAIE3v2B271
import Definitions.Def_OAIE3v2B272

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrecenterPaths
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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem precenterChart_frozen (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) (i : {i // ¬(P.precenterChart hpos a).keep i}) :
    (A.sides i.val : ℝ) ≤ Real.exp cost := P.frozen_side _ i

theorem precenterCandidate_score (hpos : 0 < A.law.mass P.productive)
    (a : A.Path) : scoreThreshold ≤ (P.precenterCandidate hpos a).score observable weight :=
  P.score _

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

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

theorem freezeAxes_score (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ) :
    (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).score observable weight =
      𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints,
        (weight (C.physical (C.axisPoint keep fixed u)) *
          observable (C.physical (C.axisPoint keep fixed u))
            (candidate.value (C.axisPoint keep fixed u))).re := by
  simp only [score, C.freezeAxes_physical, candidate.freezeAxes_value, Complex.re_expect]

end AllocatedExternalLocalCandidate

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

theorem exists_axisFreezing
    (keep : P.productive → LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z i, keep z i → (P.chart z).keep i) (shortCost : ℝ)
    (hremoved : ∀ z (i : (P.chart z).Variables),
      ¬keep z i.val → (A.sides i.val : ℝ) ≤ Real.exp shortCost) :
    Nonempty (P.AxisFreezing keep shortCost) := by
  have hex (z : P.productive) :=
    (P.candidate z).exists_freezeAxes (keep z) (hkeep z)
      observable weight (a := (P.candidate z).score observable weight) le_rfl
  choose fixed hfixed hscore using hex
  exact ⟨{ keep_subset := hkeep
           removed_side := hremoved
           fixed := fixed
           fixed_mem := hfixed
           score_mono := fun z => by
             rw [AllocatedExternalLocalCandidate.freezeAxesScore,
               AllocatedExternalLocalCandidate.freezeAxes_score]
             exact hscore z }⟩

theorem exists_thresholdAxisFreezing (H : ℕ) :
    Nonempty (P.AxisFreezing (P.thresholdKeep H) (Real.log ((max H 1 : ℕ) : ℝ))) := by
  apply P.exists_axisFreezing (P.thresholdKeep H) (fun _ _ hi => hi.1)
  intro z i hi
  have hlt : A.sides i.val < H := by
    have hnot : ¬ H ≤ A.sides i.val := fun h => hi ⟨i.property, h⟩
    exact Nat.lt_of_not_ge hnot
  have hpos : (0 : ℝ) < ((max H 1 : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right H 1))
  rw [Real.exp_log hpos]
  exact_mod_cast (hlt.le.trans (le_max_left H 1))

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedExternalCandidateCommonKeepPositiveKernelPreparation
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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_precenterKernelSelection
    {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    (early : ExternalFamilyPrecenterProjectionData T p q)
    (top : Submodule ℚ L) (htop : top ≤ D.filtration.layer s)
    (hpos : 0 < A.law.mass P.productive)
    (hξ1 : ξ ≤ 1)
    (hweight : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp p)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hobservable : ∀ x, (T x).observable = observable x) :
    Nonempty (P.PrecenterKernelSelection early top htop hpos) := by
  obtain ⟨code, tests, retained, htests, hidentity, hinvariant, hsub, hmass, hlocal⟩ :=
    early.select top htop A.law P.productive
      (fun a => (P.precenterChart hpos a).localLaw)
      (fun a => A.physical (P.precenterChart hpos a).path)
      (fun a => (P.precenterCandidate hpos a).siteValue)
      (fun a site => weight (A.physical (P.precenterChart hpos a).path site))
      (fun a site => hweight _ (A.physical_mem_integerBox hξ1 _ _)) (by
        intro a ha
        have hs := hscore.trans (P.precenterCandidate_score hpos a)
        rw [← (P.precenterCandidate hpos a).localLaw_score observable weight] at hs
        simpa only [hobservable] using hs)
  refine ⟨{
    code := code
    tests := tests
    test_bounds := htests
    identity := hidentity
    invariant := hinvariant
    retained := retained
    subset := hsub
    mass := hmass
    pivots := fun a ha => (hlocal a ha).1
    scores := ?_ }⟩
  intro a ha
  exact ((hlocal a ha).2).trans_eq
    ((P.precenterCandidate hpos a).localLaw_score (fun x => (tests x).observable) weight)

end AllocatedExternalCandidateProblem
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_positiveKernelPreparation
    (p : ℝ) (e : ℕ) (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hξ1 : ξ ≤ 1)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ η) :
    Nonempty (P.PositiveKernelPreparation p e) := by
  classical
  let := D.metricSpace
  have hcap (x : X → ℤ) (y : D.Space) : ‖observable x y‖ ≤ 1 := by
    simpa only [positiveClip_eq_self _ (hpositive x y)] using
      norm_positiveClip_le_one (observable x y)
  let tests (x : X → ℤ) : D.Niltest (fullTaggedVariableWeight (X := X) J) :=
    D.externalNetNiltest (observable x) ℓ (hcap x) (hLip x) 1
  have hunit (x : X → ℤ) : (tests x).UnitIntervalValued := hpositive x
  have hcomplexity (x : X → ℤ) : (tests x).ComplexityLE (p + 3) :=
    D.externalNetNiltest_complexity (observable x) ℓ (hcap x) (hLip x) 1 hp hD hℓ
  have hp3 : 0 ≤ p + 3 := by linarith
  have hpp3 : p ≤ p + 3 := by linarith
  obtain ⟨early⟩ := (Classical.choose_spec
    (exists_externalFamilyPrecenterProjectionData.{0, 0, 0})).2 tests (p + 3) hp3
      (hD.mono D hpp3) hunit hcomplexity
  have hq : positiveKernelPreparationParameter p =
      (p + 3 + 2) ^ positiveKernelPreparationExponent := by
    simp only [positiveKernelPreparationParameter, show p + 3 + 2 = p + 5 by ring]
  change ExternalFamilyPrecenterProjectionData tests (p + 3)
    ((p + 3 + 2) ^ positiveKernelPreparationExponent) at early
  rw [← hq] at early
  have hpos : 0 < A.law.mass P.productive :=
    (Real.exp_pos _).trans_le (hmass.trans P.mass)
  obtain ⟨selected⟩ := P.exists_precenterKernelSelection early
    (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap) inf_le_left hpos hξ1
    (fun x _ => (hweight x).trans (Real.exp_le_exp.mpr hpp3))
    ((Real.exp_le_exp.mpr (neg_le_neg hpp3)).trans hscore) (fun _ => rfl)
  let η := Real.exp (-((p + 3) + positiveKernelPreparationParameter p + 2))
  have hη : 0 < η := Real.exp_pos _
  have hq0 : 0 ≤ positiveKernelPreparationParameter p := by
    unfold positiveKernelPreparationParameter
    positivity
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨count, hcount, centers, hcenters⟩ := hnet η hη hη1
  have hcountPos : 0 < count := by
    have hzero : (0 : X → ℤ) ∈ integerBox N := by
      apply (mem_integerBox N _).mpr
      intro x
      change (0 : ℤ) ≤ 0 ∧ (0 : ℤ) < (N x : ℤ)
      exact ⟨le_rfl, by exact_mod_cast A.size_pos x⟩
    obtain ⟨i, _⟩ := hcenters 0 hzero
    exact Nat.zero_lt_of_lt i.isLt
  have hlog : Real.log (1 / η) = (p + 3) + positiveKernelPreparationParameter p + 2 := by
    dsimp [η]
    rw [one_div, ← Real.exp_neg, Real.log_exp]
    ring
  have hbin : (count : ℝ) ≤ Real.exp (positiveKernelPreparationBinLog p e) := by
    rw [hlog] at hcount
    convert hcount using 1
    unfold positiveKernelPreparationBinLog
    congr 2
    ring
  exact ⟨{
    positive_mass := hpos
    tests := tests
    tests_observable := fun _ => rfl
    tests_unit := hunit
    tests_complexity := hcomplexity
    early := early
    selected := selected
    binCount := count
    binCount_pos := hcountPos
    representative := centers
    net := fun x => hcenters x.val x.property
    binCard := hbin }⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

noncomputable def positiveKernelResidualPrecisionParameter (p : ℝ) (e : ℕ) : ℝ :=
  positiveKernelPreparationParameter p + positiveKernelPreparationParameter p +
    positiveKernelPreparationBinLog p e + 4

end Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedExternalCandidateFixedCenterDegreeModel
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.fixedCenterDegreeSiteNonempty
theorem exists_fixedCenter_degree_forecast_model (degree : ℕ)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata P C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ P)
    (hdirect : A.NativeDetection degree pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy P)
    {Tests : A.Path → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset A.Site)
    (origin : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hshape : ∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j))
    (hDense : ∀ z j, IsDenseCommonStrideBox A.sides pSlice ((slices z j).image Subtype.val))
    (hcomplex : ∀ z j, (Vdetect z j).ComplexityLE pTest)
    (hcap : ∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let tests : ∀ z, Tests z → A.Site → ℂ := fun z j t =>
      star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val))
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) degree commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ model : CenteredForecastModel (integerBox N),
      (∀ i, model.models i ∈ native) ∧
      input = (∑ i, model.coefficient i • model.models i) + model.residual ∧
      (∑ i, |model.coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      sampledSliceSeminorm A.law (A.physicalBox hξone hmargin) slices tests model.residual ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data f).target‖ ≤ Real.exp (-u)) ∧
      (model.nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) := by
  classical
  intro tests commonBudget Qmodel native
  let : ∀ x, NeZero (N x) := fun x => ⟨(A.size_pos x).ne'⟩
  have hsize := preparedCenteredForecast_slice_family_bounds B U b S slices hDense
  have htests (z) (j) (t : A.Site) : ‖tests z j t‖ ≤ 1 :=
    preparedCenteredForecast_niltest_star_eval_bound (Vdetect z j) (hcap z j)
      (commonStrideIndex (origin z j) (step z j) t.val)
  have hdetect := hdirect Ddetect Vdetect slices origin step length
    hstep hshape hDense hcomplex hcap
  obtain ⟨nterms, hn, models, coefficient, residual, hmodels, heq, hcoeff, hlocal, hforecast, hterms⟩ :=
    exists_fixedLaw_centered_forecast_twist_model degree N poly localBudget Pnative hbudget hNative
      A.law (A.physicalBox hξone hmargin) A.physical (fun _ _ => rfl)
      slices tests (fun f => (data f).target) hu hp (le_max_left 0 massLog)
      (Real.exp_nonneg _) hC (Real.exp_nonneg _) (Real.exp_le_exp.mpr hSliceLog)
      hCp (Real.exp_le_exp.mpr hCap) hPrecision hsize.2 htests (fun f => (data f).cap)
      hdetect (fun f => (data f).Term) (fun f => (data f).coefficient)
      (fun f => (data f).centerConstant) (fun f => (data f).twists)
      (fun f => (data f).mass.trans (Real.exp_le_exp.mpr (le_max_right 0 massLog)))
      (fun f v => ((data f).approximation v).trans (Real.exp_le_exp.mpr (neg_le_neg hAccuracy)))
      hexcess le_rfl input hinput
  exact ⟨⟨nterms, hn, models, coefficient, residual⟩,
    hmodels, heq, hcoeff, hlocal, hforecast, hterms⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateLocalFixedCenterFront
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.fixedCenterUniversalSiteNonempty
theorem exists_fixedCenter_universal_forecast_model (degree : ℕ)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata P C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceNonneg : 0 ≤ pSlice) (hTestBudget : 2 ≤ pTest)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ P)
    (hdirect : A.NativeDetection degree pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy P)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let Packet := UniversalLocalMajorSliceTest A.sides degree pSlice pTest
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) degree commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ model : CenteredForecastModel (integerBox N),
      (∀ i, model.models i ∈ native) ∧
      input = (∑ i, model.coefficient i • model.models i) + model.residual ∧
      (∑ i, |model.coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      sampledSliceSeminorm A.law (A.physicalBox hξone hmargin)
        (fun _ (packet : Packet) => packet.slice.subtypeSites)
        (fun _ (packet : Packet) site => packet.weight site.val) model.residual ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data f).target‖ ≤ Real.exp (-u)) ∧
      (model.nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) := by
  classical
  intro Packet commonBudget Qmodel native
  have hSides (i : LayerSamplerVariables G I n B) : 0 < A.sides i := by
    cases i with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U b S j
  let : Nonempty Packet := UniversalLocalMajorSliceTest.nonempty A.sides hSides
    degree pSlice pTest hSliceNonneg hTestBudget
  have hmodel := A.exists_fixedCenter_degree_forecast_model degree hξone hmargin
    hu hp hbudget hNative hSliceLog hC hCp hCap hAccuracy hPrecision hdirect hexcess
    (Tests := fun _ => Packet) (Ldetect := fun _ packet => packet.nativeModel.L)
    (dims := fun _ packet => packet.nativeModel.dim)
    (fun _ packet => packet.nativeModel.model) (fun _ packet => packet.nativeModel.test)
    (fun _ packet => packet.slice.subtypeSites)
    (fun _ packet i => (packet.slice.start i : ℤ))
    (fun _ packet => packet.stride) (fun _ packet => packet.slice.length)
    (fun _ packet => packet.stride_pos)
    (fun _ packet => packet.slice.subtypeSites_image_val.trans packet.slice.integerPoints_eq_commonStrideBox)
    (fun _ packet => packet.slice.subtypeSites_dense packet.dense)
    (fun _ packet => packet.nativeModel.complexity)
    (fun _ packet => by exact_mod_cast packet.nativeModel.norm)
    data input hinput
  simpa only [UniversalLocalMajorSliceTest.weight_eq_native_eval] using hmodel

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

theorem mass_after_native_selection
    {retained : Finset A.Path} {selectionLog : ℝ}
    (hmass : Real.exp (-selectionLog) * A.law.mass selected.retained ≤ A.law.mass retained) :
    Real.exp (-(q + selectionLog)) * A.law.mass P.productive ≤ A.law.mass retained := by
  calc
    _ = Real.exp (-selectionLog) * (A.law.mass P.productive * Real.exp (-q)) := by
      rw [neg_add, Real.exp_add]
      ring
    _ ≤ Real.exp (-selectionLog) * A.law.mass selected.retained :=
      mul_le_mul_of_nonneg_left selected.mass (Real.exp_nonneg _)
    _ ≤ A.law.mass retained := hmass

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

theorem fixedCenter_residual_budget
    {Bin : Type} [Fintype Bin] {binLog massLog Eres u : ℝ}
    (hmass : Real.exp (-massLog) ≤ A.law.mass P.productive)
    (hbin : (Fintype.card Bin : ℝ) ≤ Real.exp binLog)
    (hu : (q + binLog) + Eres + (massLog + q) + 2 ≤ u) :
    (Fintype.card (early.Freq × Bin) : ℝ) * Real.exp (-u) ≤
      Real.exp (-Eres) * A.law.mass selected.retained / 2 := by
  have hselected : Real.exp (-(massLog + q)) ≤ A.law.mass selected.retained := by
    calc
      _ = Real.exp (-massLog) * Real.exp (-q) := by rw [neg_add, Real.exp_add]
      _ ≤ A.law.mass P.productive * Real.exp (-q) :=
        mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)
      _ ≤ _ := selected.mass
  have hcard : (Fintype.card (early.Freq × Bin) : ℝ) ≤ Real.exp (q + binLog) := by
    rw [Fintype.card_prod, Nat.cast_mul, Real.exp_add]
    exact mul_le_mul early.card_bound hbin (Nat.cast_nonneg _) (Real.exp_nonneg _)
  exact FiniteProbabilityWeights.uniformResidualGood_exp_budget hselected hcard hu

theorem fixedCenter_mass_after_native_selection
    {retained : Finset A.Path} {selectionLog : ℝ}
    (hmass : Real.exp (-selectionLog) * (A.law.mass selected.retained / 2) ≤
      A.law.mass retained) :
    Real.exp (-(q + selectionLog + 2)) * A.law.mass P.productive ≤ A.law.mass retained := by
  have hhalf : Real.exp (-(selectionLog + 2)) ≤ Real.exp (-selectionLog) / 2 := by
    simpa using precenter_native_selection_model_error_budget 0 selectionLog
  have h := selected.mass_after_native_selection (selectionLog := selectionLog + 2) (by
    calc
      _ ≤ (Real.exp (-selectionLog) / 2) * A.law.mass selected.retained :=
        mul_le_mul_of_nonneg_right hhalf (A.law.mass_nonneg _)
      _ = Real.exp (-selectionLog) * (A.law.mass selected.retained / 2) := by ring
      _ ≤ _ := hmass)
  simpa only [add_assoc] using h

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalLocalChart
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem tagAnchor_quotient_bound
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ))
    (hQU : U j ≤ LinearMap.ker Q) {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ : ∀ x i, |Q x i| ≤ CQ * ‖x‖) (i : T) :
    |Q (C.tagAnchor j) i| ≤ CQ * (Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j)) :=
  C.recovered.integerFrozenFullChart_anchor_bound B U b hb o S hR hσ poly hm
    hσone Cgeo hCgeo hchart hp C.centerLift C.path.1.val C.path.2.val C.sample C.read
    j Q hQU hCQ hQ C.keep C.fixed C.fixed_abs_le_box i

theorem tagAnchor_quotient_grid
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (den : ℕ)
    (hgrid : ∀ z : J j → ℤ, ∀ i, ∃ a : ℤ, (den : ℝ) * Q (fun i => (z i : ℝ)) i = a)
    (i : T) : ∃ a : ℤ, (den : ℝ) * Q (C.tagAnchor j) i = a :=
  allocatedFrozenIntegerFullChart_anchor_grid B U b o poly hm
    C.centerLift C.path.1.val C.path.2.val C.sample j Q (den : ℝ) hgrid C.keep C.fixed i

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_common_affine_anchor_refinement
    (Q : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (den : Fin m → ℕ)
    (hden : ∀ j, 0 < den j) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hdenp : ∀ j, (den j : ℝ) ≤ Real.exp p)
    (hgrid : ∀ j (z : J j → ℤ) i, ∃ a : ℤ, (den j : ℝ) * Q j (fun i => (z i : ℝ)) i = a)
    (hbound : ∀ z : P.productive, ∀ j i,
      |Q j ((P.chart z).tagAnchor j) i| ≤ Real.exp p)
    (hmass : 0 < massThreshold) :
    ∃ (c : ∀ j, J j → ℝ)
      (refinement : P.Refinement cost
        (Real.exp (-((2*p+3)^3)) * massThreshold) scoreThreshold),
      (∀ j i, |c j i| ≤ Real.exp p) ∧
      (∀ j i, ∃ a : ℤ, (den j : ℝ) * c j i = a) ∧
      (∀ z : refinement.problem.productive, ∀ j,
        Q j ((refinement.problem.chart z).tagAnchor j) = c j) ∧
      (∀ z : refinement.problem.productive,
        (refinement.problem.chart z).slice.integerPoints =
          (P.chart ⟨z.val, refinement.subset z.property⟩).slice.integerPoints) := by
  let v (a : A.Path) : (Σ j, J j) → ℝ :=
    if ha : a ∈ P.productive then fun i => Q i.1 ((P.chart ⟨a,ha⟩).tagAnchor i.1) i.2
    else 0
  have hv (z : P.productive) (i : Σ j, J j) :
      v z.val i = Q i.1 ((P.chart z).tagAnchor i.1) i.2 := by
    simp only [v, dif_pos z.property]
  obtain ⟨a₀, ha₀, retained, hsub, haT, hsame, hmassT⟩ :=
    exists_weighted_common_coordinate_grid_vector A.law P.productive (hmass.trans_le P.mass)
      v (fun i => den i.1) (fun i => hden i.1) hp hdim (fun i => hdenp i.1)
      (by
        intro a ha i
        rw [hv ⟨a,ha⟩]
        exact (P.chart ⟨a,ha⟩).tagAnchor_quotient_grid i.1 (Q i.1) (den i.1) (hgrid i.1) i.2)
      (by intro a ha i; rw [hv ⟨a,ha⟩]; exact hbound ⟨a,ha⟩ i.1 i.2)
  let refinement : P.Refinement cost
      (Real.exp (-((2*p+3)^3)) * massThreshold) scoreThreshold :=
    { retained := retained
      subset := hsub
      mass := (mul_le_mul_of_nonneg_left P.mass (Real.exp_nonneg _)).trans hmassT
      cost_le := le_rfl
      step := fun z => (P.chart ⟨z.val,hsub z.property⟩).step
      step_pos := fun z => (P.chart ⟨z.val,hsub z.property⟩).step_pos
      slice := fun z => (P.chart ⟨z.val,hsub z.property⟩).slice
      dense := fun z => (P.chart ⟨z.val,hsub z.property⟩).dense
      inside := fun _ => Finset.Subset.refl _
      scoreLower := fun z => P.score ⟨z.val,hsub z.property⟩ }
  refine ⟨fun j i => v a₀ ⟨j,i⟩, refinement, ?_, ?_, ?_, ?_⟩
  · intro j i
    change |v a₀ ⟨j,i⟩| ≤ Real.exp p
    rw [hv ⟨a₀,ha₀⟩ ⟨j,i⟩]
    exact hbound ⟨a₀,ha₀⟩ j i
  · intro j i
    change ∃ a : ℤ, (den j : ℝ) * v a₀ ⟨j,i⟩ = a
    rw [hv ⟨a₀,ha₀⟩ ⟨j,i⟩]
    exact (P.chart ⟨a₀,ha₀⟩).tagAnchor_quotient_grid j (Q j) (den j) (hgrid j) i
  · intro z j
    funext i
    change Q j ((P.chart ⟨z.val,hsub z.property⟩).tagAnchor j) i = v a₀ ⟨j,i⟩
    exact (hv ⟨z.val,hsub z.property⟩ ⟨j,i⟩).symm.trans
      (congrFun (hsame z.val z.property) ⟨j,i⟩)
  · intro z
    rfl

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalLocalChart
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem tag_values_sub_anchor_mem
    (hσone : ∀ j, σ j ≤ 1)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {p Mbound H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K p blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hM : 0 ≤ Mbound)
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ Mbound)
    (hlong : ∀ i, C.keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * Mbound < H)
    (x : C.Variables → ℝ) :
    (fun i => MvPolynomial.eval x (integerSampledRealChart C.integerChart i) -
      MvPolynomial.eval 0 (integerSampledRealChart C.integerChart i)) ∈ K :=
  C.recovered.integerFullChart_certified_frozen_affine_range B U b hb o S hR hσ poly hm
    hσone C.centerLift C.path.1.val C.path.2.val C.sample C.read K hcertificate hretained
    hp le_rfl hJ Cgeo hCgeo hchart hM hcap C.keep hlong hthreshold C.fixed x

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_certifiedAffineRefinement
    (hσone : ∀ j, σ j ≤ 1)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {p H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K p blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : (blocks : ℝ) ≤ p)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ Real.exp p)
    (hlong : ∀ z : P.productive, ∀ i, (P.chart z).keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * Real.exp p < H)
    (hmass : 0 < massThreshold) : Nonempty (P.CertifiedAffineRefinement K p) := by
  let q := p + ((p+2)^2+2)^63
  let labelBudget := certifiedAffineCenterBudget p
  have hlabel : labelBudget = 2*p+(q+2)^10+(q+2)^8+1 := rfl
  have hbudget := affineCenterBudget_arithmetic hp
    (show 0 ≤ (q+2)^10 from by positivity) (show 0 ≤ (q+2)^8 from by positivity)
  have hlabel0 : 0 ≤ labelBudget := hlabel.symm ▸ hbudget.1
  have hplabel : p ≤ labelBudget := hlabel.symm ▸ hbudget.2.1
  have hdenlabel : (q+2)^10 ≤ labelBudget := hlabel.symm ▸ hbudget.2.2.1
  have hdimj (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective (Sigma.mk j) (by intro a b h; cases h; rfl))).trans hdim
  obtain ⟨V, projection, den, hK, hP⟩ :=
    hcertificate.exists_bounded_rational_retractions J hp hdimj hblocks
  let Q := fun j => rationalTagProjectionComplement (projection j)
  have hQU (j : Fin m) : U j ≤ LinearMap.ker (Q j) := by
    rw [rationalTagProjectionComplement_ker (projection j) (V j) (hP j).1 (hP j).2.1]
    exact retained_tag_le_of_product_constraint K (fun j => realRationalCoordinateSpan (V j)) hK hretained j
  have hgrid (j : Fin m) (z : J j → ℤ) (i : J j) :
      ∃ a : ℤ, (den j : ℝ) * Q j (fun i => (z i : ℝ)) i = a := by
    obtain ⟨a, ha⟩ := rationalTagProjectionComplement_integer_grid (projection j) (den j)
      (hP j).2.2.2.2.2.1 z
    exact ⟨a i, ha i⟩
  have hbound (z : P.productive) (j : Fin m) (i : J j) :
      |Q j ((P.chart z).tagAnchor j) i| ≤ Real.exp labelBudget := by
    have hraw := (P.chart z).tagAnchor_quotient_bound hσone Cgeo hCgeo hchart hpoly
      j (Q j) (hQU j) (Real.exp_nonneg (p+(q+2)^8+1))
      (rationalTagProjectionComplement_coordinate_exp_bound (projection j) hp
        (by positivity : 0 ≤ (q+2)^8) (hdimj j) (hP j).2.2.1) i
    calc
      _ ≤ Real.exp (p+(q+2)^8+1) *
          (Cgeo j * (((Fintype.card (I j) : ℝ)+1)*R j)) := hraw
      _ ≤ Real.exp (p+(q+2)^8+1) * Real.exp p :=
        mul_le_mul_of_nonneg_left (hcap j) (Real.exp_nonneg _)
      _ = Real.exp (2*p+(q+2)^8+1) := affineCenterBudget_exp
      _ ≤ Real.exp labelBudget := Real.exp_le_exp.mpr (hlabel.symm ▸ hbudget.2.2.2)
  obtain ⟨c, refinement, hcBound, hcGrid, hc, hpoints⟩ :=
    P.exists_common_affine_anchor_refinement Q den (fun j => (hP j).2.2.2.1)
      hlabel0 (hdim.trans hplabel)
      (fun j => (hP j).2.2.2.2.1.trans (Real.exp_le_exp.mpr hdenlabel))
      hgrid hbound hmass
  have hnonempty : refinement.problem.productive.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    have h := refinement.mass
    change Real.exp (-((2*labelBudget+3)^3)) * massThreshold ≤
      A.law.mass refinement.problem.productive at h
    rw [he] at h
    have hpos : 0 < Real.exp (-((2*labelBudget+3)^3)) * massThreshold :=
      mul_pos (Real.exp_pos _) hmass
    simpa [FiniteProbabilityWeights.mass] using hpos.trans_le h
  obtain ⟨z₀,hz₀⟩ := hnonempty
  have hcFixed (j : Fin m) : Q j (c j) = c j := by
    rw [← hc ⟨z₀,hz₀⟩ j]
    exact rationalTagProjectionComplement_idempotent (projection j) (V j)
      (hP j).1 (hP j).2.1 _
  refine ⟨{
    space := V
    projection := projection
    denominator := den
    constraint := hK
    range_eq := fun j => (hP j).1
    fixes_space := fun j => (hP j).2.1
    projection_height := fun j => (hP j).2.2.1
    denominator_pos := fun j => (hP j).2.2.2.1
    denominator_bound := fun j => (hP j).2.2.2.2.1.trans (Real.exp_le_exp.mpr hdenlabel)
    projection_grid := fun j => (hP j).2.2.2.2.2.1
    translate := c
    translate_bound := hcBound
    translate_grid := hcGrid
    translate_fixed := hcFixed
    refinement := refinement
    slice_points := hpoints
    chart_fixed := ?_ }⟩
  intro z x
  apply fullTaggedAffineMatrixChart_eval_eq_of_anchor J projection c
    (refinement.problem.chart z).tagAnchor _ ?_ (hc z) hcFixed
  intro j
  have hkeep (i) (hi : (refinement.problem.chart z).keep i) : H ≤ layerSamplerBox B U b S i :=
    hlong ⟨z.val,refinement.subset z.property⟩ i hi
  have hrange := (refinement.problem.chart z).tag_values_sub_anchor_mem hσone K
    hcertificate hretained hp hdimj Cgeo hCgeo hchart (Real.exp_nonneg _) hcap hkeep hthreshold x
  rw [hK] at hrange
  have hmem := hrange j
  rw [← rationalTagProjectionComplement_ker (projection j) (V j) (hP j).1 (hP j).2.1] at hmem
  exact hmem

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateThresholdSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration RationalFilteredNilmanifold

theorem candidatePrimitiveFreezingCutoff_le_budget (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitiveFreezingCutoff s a p ≤
      (p + candidatePrimitivePhysicalBudgetExponent s a) ^
        candidatePrimitivePhysicalBudgetExponent s a :=
  (candidatePrimitiveFreezingCutoff_le_geometry s a hp).trans
    (candidatePrimitivePhysicalScalarBounds s a hp).geometry_budget

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedCandidateHistoryLocalNiltests
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

theorem exists_history_current_grade_local_niltests
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (r a : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bhistory Bstage budget : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      (eQ.baseChange ℝ) lift Z Set.univ U poly N Bhistory r)
    (hcontrol : FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2 budget)
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K Bstage
      (r * (Fintype.card η * m)))
    (HMap l : ℕ) (pMap : ℝ) (hHMap : 1 ≤ HMap) (hl : 0 < l) (hpMap : 0 ≤ pMap)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ pMap)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ pMap)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp pMap) (hlExp : (l : ℝ) ≤ Real.exp pMap)
    (H : ℕ) (p qNative : ℝ) (hH : 1 ≤ H) (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hVars : (Fintype.card Vars : ℝ) ≤ p)
    (hχ : (Fintype.card χ : ℝ) ≤ p) (hHExp : (H : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (hcommon : Real.exp budget * Real.exp ((pMap + 2) ^ 4) ≤ Real.exp p)
    (hmapSlow : Real.exp ((pMap + 2) ^ 3 + qNative) ≤ Real.exp ((p + 2) ^ a))
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ Real.exp ((p + 2) ^ a))
    (hNreset : ∀ i : Vars, Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
      allocatedFrozenCurrentGradeResetConstant s a) ≤ (A.sides i.val : ℝ))
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) = (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pK Mbound LongSide : ℝ) (hpK : 0 ≤ pK) (hBstage : Bstage ≤ pK)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pK) (hM : 0 ≤ Mbound)
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ Mbound)
    (hLong : 1 ≤ LongSide) (hlong : ∀ i, keep i → LongSide ≤ layerSamplerBox B U btag S i)
    (hthreshold : Real.exp ((pK + 2) ^ 9) ^ 2 * Mbound < LongSide)
    (hlength : ∀ z : P.productive, ∀ i, s < ((Q).chart z).slice.length i)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (Hθ : ℕ) (pLocal : ℝ)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hpLocal : 1 ≤ pLocal) (hLocalDim : (Fintype.card Vars : ℝ) ≤ pLocal)
    (hLocalSize : (Fintype.card κ : ℝ) * Hθ * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hLocalDen : ((Hθ ^ Fintype.card κ : ℕ) : ℝ) * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hNLocal : ∀ i : Vars, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (A.sides i.val : ℝ)) :
    ∃ reset : ℕ, 0 < reset ∧
      (reset : ℝ) ≤ Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ∧
      ∀ (j : η) (z : P.productive) (score : (Vars → ℤ) → ℝ),
      ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card κ * reset ∧
      ∃ slice : ResidueBoxSlice (fun i : Vars => A.sides i.val) q,
        IsDenseCommonStrideBox (fun i : Vars => A.sides i.val)
          ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) slice.integerPoints ∧
        (𝔼 x : (∀ i : Vars, Fin (A.sides i.val)), score (fun i => ((x i).val : ℤ))) ≤
          (𝔼 x ∈ slice.integerPoints, score x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold r).Niltest (fun _ : Vars => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget r) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ slice.integerPoints,
          majorPhasePlateauSignal J (r + 1) poly
            (fun i => (P.centerLift (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
            (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J (r + 1) (Fmark.realSymbolGradeQuotientPolynomial bF ν hF
                (fullTaggedVariableWeight J) (fast).toSubmodule (r + 1)
                (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord)))
            (jointIntegerPhysicalSite (finiteSplitPoint keep x ((Q).chart z).fixed)
              (z.val.1.val, z.val.2.val)) *
              star (T.eval (commonStrideIndex (fun i => (slice.start i : ℤ)) q x))‖ := by
  obtain ⟨lLocal, hlLocal, hlLocalBound, _, hmarkedFactors⟩ :=
    P.exists_withKeep_marked_frozen_symbol_factors keep hkeep bD ω hD bF ν hF hφ
      hHMap hl hentries hpMap hsource htarget hHMapExp hlExp
  have hcommon' : Real.exp budget * (lLocal : ℝ) ≤ Real.exp p :=
    (mul_le_mul_of_nonneg_left hlLocalBound (Real.exp_nonneg _)).trans hcommon
  obtain ⟨qCurrent, _, _, reset, hreset, hresetBound, _, hlocal⟩ :=
    exists_allocated_controlled_frozen_current_grade_local_niltest (Deck := Deck) B U btag hb o S hRad hσ poly hm
      s a keep Fmark bF ν hF H lLocal p hH hlLocal hp hκ hVars hχ hHExp hbracket
      history.outer.1 history.outer.2 N A.size_pos hcontrol hcommon' hallowance hNreset
  refine ⟨reset, hreset, hresetBound, ?_⟩
  intro j z score
  obtain ⟨El, Pl, Rl, hprod, hPl, hEl, hRl⟩ :=
    hmarkedFactors z qNative W (hlength z) (hfactor z)
  have hsidePos : ∀ i : Vars, (0 : ℝ) < A.sides i.val :=
    fun i => (Real.exp_pos _).trans_le (hNreset i)
  have hEl' := Fmark.symbolSlowBound_mono bF ν hF (fun _ : Vars => 1)
    (fun i => (A.sides i.val : ℝ)) hsidePos hmapSlow El hEl
  have hden : ((Hθ ^ Fintype.card κ * reset : ℕ) : ℝ) ≤ Real.exp pLocal := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hresetBound (Nat.cast_nonneg _)).trans hLocalDen
  have hrecover := P.withKeep_chart_recovered z
  have hspatial := P.currentGrade_spatial_support z
  have hfixed := ((Q).chart z).fixed_in_box
  exact hlocal hr fast vg hspan hvg eQ j P.centerLift z.val.1.val z.val.2.val
    (P.chart z).sample (P.chart z).read hrecover A.trim_pos hτ hξ hspatial
    ((Q).chart z).fixed hfixed hσone Cgeo hCgeo hchart hsmall hpoly
    history.K Bstage pK Mbound LongSide (r * (Fintype.card η * m)) hcertificate
    (fun point hpoint => history.retained point (Set.mem_univ _) hpoint)
    hpK hBstage hJ hM hcap hLong hlong hthreshold gmark
    (fun point hpoint d hd => history.invariant_outer point hpoint d (by omega))
    El Pl Rl hprod hPl hEl' hRl Hθ pLocal (hθ j) hpLocal hLocalDim hLocalSize hden score hNLocal

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenPrefixStageData
namespace OAI

section

namespace Erdos3.VectorPolynomial

 theorem allocatedCandidateStageBase_le_forwardWork (s m Cprimitive A : ℕ)
    (count : ℕ → ℕ) (r : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hCA : allocatedCandidateStageBaseExponent s m Cprimitive ≤ A) :
    allocatedCandidateStageBase s m Cprimitive (preparedFiniteForwardParameter A count r x) ≤
      preparedFiniteForwardWork A count r x := by
  let b := preparedFiniteForwardParameter A count r x
  let C := allocatedCandidateStageBaseExponent s m Cprimitive
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A count r hx
  have hA : (2 : ℝ) ≤ A := Nat.cast_le.mpr
    ((allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1.trans hCA)
  rw [preparedFiniteForwardWork_eq]
  change (b + C) ^ C ≤ (b + A) ^ A
  exact (pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg _))
    (add_le_add (le_refl b) (Nat.cast_le.mpr hCA)) C).trans
      (pow_le_pow_right₀ (by linarith) hCA)

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    {D : RationalFilteredNilmanifold L s d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_axisFreezing_of_side_bounds
    (keep : LayerSamplerVariables G I n B → Prop) (pSlice : ℝ)
    (hcost : cost < pSlice)
    (hkept : ∀ i, keep i → Real.exp pSlice ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Real.exp pSlice) :
    Nonempty (P.AxisFreezing (fun _ => keep) pSlice) := by
  refine P.exists_axisFreezing (fun _ => keep) ?_ pSlice ?_
  · intro z i hi
    by_contra hnot
    have hupper := P.frozen_side z ⟨i, hnot⟩
    have hlower := (Real.exp_lt_exp.mpr hcost).trans_le (hkept i hi)
    exact (not_lt_of_ge hupper) hlower
  · intro z i hi
    exact hfrozen i.val hi

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOrdinaryLongPhysicalTerminalConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial

theorem nativePhysicalTerminalBudgets_nonneg
    (s m Cprimitive scheduleExponent : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ nativePhysicalTerminalAffineBudget s scheduleExponent x ∧
    0 ≤ nativePhysicalTerminalWorkBudget s scheduleExponent x ∧
    0 ≤ nativePhysicalTerminalFullBudget s m Cprimitive scheduleExponent x := by
  have hcum := (preparedFiniteForward_prefix_bounds scheduleExponent
    (fun n => fullChartStageCountConstant (n + 1) 254) s hx).1.1
  have hwork := preparedFiniteForwardWork_nonneg scheduleExponent
    (fun n => fullChartStageCountConstant (n + 1) 254) s hx
  exact ⟨hcum, hwork,
    (allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hwork hcum).1⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

def actualSourceProblemOn
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {massThreshold : ℝ} (hmass : massThreshold ≤ A.law.mass retained) :
    AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold where
  productive := retained
  mass := hmass
  chart a := F.chart a.val
  chart_path a := hpath a.val (hsub a.property)
  centerLift := sourceCenter
  chart_centerLift a := hcenter a.val (hsub a.property)
  frozen_side a := hfrozen a.val (hsub a.property)
  candidate a := F.candidate a.val
  score a := by
    exact (hscore a.val (hsub a.property)).trans_eq
      ((F.sourceCandidate a.val).withKeep_score
        (observable := observable) (weight := weight) keep (F.keep_eq a.val)).symm

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeAdaptedConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable {originalMass originalScore : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost originalMass originalScore)
    (hH : H ⊆ P.productive)
    (hsourceChart : ∀ a (ha : a ∈ H), F.sourceChart a = P.chart ⟨a, hH ha⟩)
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {massThreshold : ℝ} (hmass : massThreshold ≤ A.law.mass retained)

def conclusion_of_actualSourceProblemOn {outputCost outputMass outputScore : ℝ}
    (result : (F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore retained hsub hmass).Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore := by
  let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
    scoreThreshold hscore retained hsub hmass
  have hsourceSub : source.productive ⊆ P.productive := fun _ ha => hH (hsub ha)
  have hsourceKeep (z : source.productive) :
      (P.chart ⟨z.val, hsourceSub z.property⟩).keep = keep := by
    rw [← hsourceChart z.val (hsub z.property)]
    exact F.keep_eq z.val
  have hchart (z : source.productive) :
      source.chart z =
        (P.chart ⟨z.val, hsourceSub z.property⟩).withKeep keep (hsourceKeep z) := by
    change (F.sourceChart z.val).withKeep keep (F.keep_eq z.val) = _
    congr 1
    exact hsourceChart z.val (hsub z.property)
  exact P.conclusion_of_chartwise_withKeep source hsourceSub keep hsourceKeep hchart result

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

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

@[simp] theorem actualSourceProblemOn_withKeep
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {massThreshold : ℝ} (hmass : massThreshold ≤ A.law.mass retained) :
    (F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore retained hsub hmass).withKeep keep (fun _ => rfl) =
    F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore retained hsub hmass := rfl

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

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable {originalMass originalScore : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost originalMass originalScore)
    (hH : H ⊆ P.productive)
    (hsourceChart : ∀ a (ha : a ∈ H), F.sourceChart a = P.chart ⟨a, hH ha⟩)
    (retained : Finset A.Path) (hsub : retained ⊆ H)
    {massThreshold : ℝ} (hmass : massThreshold ≤ A.law.mass retained)

include hH hsourceChart in

theorem conclusion_of_actualSourceAdaptedOptionQuotient
    (ideal : LieIdeal ℚ LG)
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
    (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)
    {outputCost outputMass outputScore : ℝ}
    (result : (((F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore retained hsub hmass).withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        ideal hI Q hQ hker descended hrecovery adapted).Conclusion
          outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  obtain ⟨original⟩ :=
    ((F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
      scoreThreshold hscore retained hsub hmass).withKeep keep (fun _ => rfl)).conclusion_of_adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        ideal hI Q hQ hker descended hrecovery adapted result
  exact ⟨F.conclusion_of_actualSourceProblemOn H sourceCenter hpath hcenter hfrozen
    observable weight scoreThreshold hscore P hH hsourceChart retained hsub hmass original⟩

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end


