-- Prove2me | Definitions.Def_OAIE3v2B219
-- name    : OAIE3v2B219
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:24:27.000429+00:00
-- url     : https://prove2.me/theorems/6d01808d-dfba-4e00-aa5f-09778a023cd2
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 223 of 311
-- statement:
--   Definitions bundle 223 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateOptionJointConclusion.lean`, `Lattices/AllocatedModularRankIntegerDecay.lean`, `Linear/CommonFreeSpanBounds.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem dependentFreeSpan_le_coefficientFreeSpan (d : Fin s) :
    D.dependentFreeSpan d ≤ D.coefficientFreeSpan d := le_sup_right

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

local notation "selected" => allocatedCongruenceIntegerSelectedCoefficients
  inactive noise r projection spatial kernel block

noncomputable def allocatedCongruenceBadDepth
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ) : ℕ → ℕ :=
  fun p => largestTestedBadDepth A
    (allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C) p selected

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion
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

theorem integerChart_support (i) :
    integerSampledRealChart C.integerChart i ∈
      weightedSupportLE (fun _ : C.Variables => 1) (fullTaggedVariableWeight J i) :=
  allocatedFrozenIntegerFullChart_support B U b o poly hm C.centerLift
    C.path.1.val C.path.2.val C.sample C.keep C.fixed i

end AllocatedExternalLocalChart

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

structure Conclusion (outputCost outputMass outputScore : ℝ) where
  ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)
  marked : map (realLieHomToRat (realificationLieHom φ)).toLinearMap ambient.log = marked.log
  retained : Finset A.Path
  subset : retained ⊆ P.productive
  mass : outputMass ≤ A.law.mass retained
  step : ∀ _z : retained, ℕ
  step_pos : ∀ z, 0 < step z
  slice : ∀ z : retained, ResidueBoxSlice
    (fun i : (P.chart ⟨z.val, subset z.property⟩).Variables => A.sides i.val) (step z)
  dense : ∀ z, IsDenseCommonStrideBox
    (fun i : (P.chart ⟨z.val, subset z.property⟩).Variables => A.sides i.val)
      outputCost (slice z).integerPoints
  inside : ∀ z, (slice z).integerPoints ⊆
    (P.chart ⟨z.val, subset z.property⟩).slice.integerPoints
  score : ∀ z, outputScore ≤ P.ambientScore ambient
    ⟨z.val, subset z.property⟩ (slice z).integerPoints

end AllocatedExternalCandidateProblem

end Erdos3.VectorPolynomial

end

section

universe u v

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

theorem polynomialOrbitIntegerChart_eval
    {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) (x : τ → ℤ) :
    F.realification.polynomialOrbitEval v x
      (F.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ g) =
    F.realification.polynomialOrbitEval w (fun i => MvPolynomial.eval x (β i)) g := by
  rw [← F.realification.polynomialOrbitRealEval_integer,
    F.polynomialOrbitRealChart_realEval]
  simp only [integerSampledRealChart_eval]
  rw [F.realification.polynomialOrbitRealEval_integer]

end Erdos3.NilpotentLieFiltration

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d : ℕ} {dp : Pivot → ℕ} (D : RationalFilteredNilmanifold L s d)
    (Fmark : NilpotentLieFiltration M s) (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))

namespace AllocatedExternalLocalCandidate

variable {C D Fmark φ marked}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))
    (Q : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

noncomputable def optionJointLocalOrbits : ∀ i : Option Pivot,
    (optionFactors D partners i).filtration.realification.PolynomialOrbit
      (fun _ : C.Variables => 1)
  | none => candidate.orbit
  | some j => (partners j).filtration.polynomialOrbitRealChart
      (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
      (integerSampledRealChart C.integerChart) C.integerChart_support (Q j)

omit [Fintype Pivot] in
@[simp] theorem optionJointLocalOrbits_none :
    candidate.optionJointLocalOrbits partners Q none = candidate.orbit := rfl

omit [Fintype Pivot] in
@[simp] theorem optionJointLocalOrbits_some (j : Pivot) :
    candidate.optionJointLocalOrbits partners Q (some j) =
      (partners j).filtration.polynomialOrbitRealChart
        (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
        (integerSampledRealChart C.integerChart) C.integerChart_support (Q j) := rfl

noncomputable def optionJointMarkedOrbits : ∀ i : Option Pivot,
    (optionFiltrations Fmark (fun j => (partners j).filtration) i).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)
  | none => marked
  | some j => Q j

noncomputable def optionJoint :
    AllocatedExternalLocalCandidate C (optionProduct D partners)
      (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => (partners j).filtration)))
      (optionMarkedLieMap (L := P) φ)
      (piRealOrbit (optionFiltrations Fmark (fun j => (partners j).filtration))
        (optionJointMarkedOrbits (marked := marked) (partners := partners) Q)) where
  orbit := piRealOrbit (fun i => (optionFactors D partners i).filtration)
    (candidate.optionJointLocalOrbits partners Q)
  mark_on_slice := by
    intro x hx
    apply (realBCHPiEquiv
      (optionFiltrations Fmark (fun j => (partners j).filtration))).injective
    funext i
    cases i with
    | none =>
      rw [realBCHPiEquiv_optionMarkedLieMap_none D.filtration Fmark
        (fun j => (partners j).filtration) φ]
      exact (congrArg
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.lowerCentralSeries_eq_bot) φ)
        (piRealOrbit_eval (fun i => (optionFactors D partners i).filtration)
          (candidate.optionJointLocalOrbits partners Q) x none)).trans
        ((candidate.mark_on_slice x hx).trans
          (piRealOrbit_eval (optionFiltrations Fmark (fun j => (partners j).filtration))
            (optionJointMarkedOrbits (marked := marked) (partners := partners) Q)
            (C.chartValues x) none).symm)
    | some j =>
      rw [realBCHPiEquiv_optionMarkedLieMap_some D.filtration Fmark
        (fun j => (partners j).filtration) φ]
      exact (piRealOrbit_eval (fun i => (optionFactors D partners i).filtration)
        (candidate.optionJointLocalOrbits partners Q) x (some j)).trans
        (((partners j).filtration.polynomialOrbitIntegerChart_eval
          (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
          C.integerChart C.integerChart_support (Q j) x).trans
          (piRealOrbit_eval (optionFiltrations Fmark (fun j => (partners j).filtration))
            (optionJointMarkedOrbits (marked := marked) (partners := partners) Q)
            (C.chartValues x) (some j)).symm)

@[simp] theorem optionJoint_orbit :
    (candidate.optionJoint partners Q).orbit =
      piRealOrbit (fun i => (optionFactors D partners i).filtration)
        (candidate.optionJointLocalOrbits partners Q) := rfl

@[simp] theorem optionJoint_value_projection (x : C.Variables → ℤ) :
    optionOriginalSpaceProjection D partners ((candidate.optionJoint partners Q).value x) =
      candidate.value x :=
  optionOriginalSpaceProjection_piRealOrbit D partners
    (candidate.optionJointLocalOrbits partners Q) x

@[simp] theorem optionJoint_score (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) :
    (candidate.optionJoint partners Q).score
      (optionOriginalObservable D partners observable) weight =
      candidate.score observable weight := by
  unfold score
  simp only [optionOriginalObservable_apply, optionJoint_value_projection]

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
    (Q : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

def optionJoint :
    AllocatedExternalCandidateProblem (E := E) A (optionProduct D partners)
      (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => (partners j).filtration)))
      (optionMarkedLieMap (L := MG) φ)
      (piRealOrbit (optionFiltrations Fmark (fun j => (partners j).filtration))
        (AllocatedExternalLocalCandidate.optionJointMarkedOrbits
          (marked := marked) (partners := partners) Q))
      (optionOriginalObservable D partners observable) weight cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (P.candidate z).optionJoint partners Q
  score z := by
    rw [AllocatedExternalLocalCandidate.optionJoint_score]
    exact P.score z

@[simp] theorem optionJoint_productive : (P.optionJoint partners Q).productive = P.productive := rfl

@[simp] theorem optionJoint_chart (z : P.productive) :
    (P.optionJoint partners Q).chart z = P.chart z := rfl

@[simp] theorem optionJoint_candidate_orbit (z : P.productive) :
    ((P.optionJoint partners Q).candidate z).orbit =
      piRealOrbit (fun i => (optionFactors D partners i).filtration)
        ((P.candidate z).optionJointLocalOrbits partners Q) := rfl

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
    (Q : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

@[simp] theorem optionJoint_ambientScore
    (ambient : (optionProduct D partners).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) :
    (P.optionJoint partners Q).ambientScore ambient z points =
      P.ambientScore (optionOriginalOrbit D partners ambient) z points := by
  unfold ambientScore
  exact congrArg Complex.re (optionOriginalOrbit_score D partners ambient observable
    points (P.chart z).physical (P.chart z).chartValues (fun u => weight ((P.chart z).physical u)))

def conclusion_of_optionJoint {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore where
  ambient := optionOriginalOrbit D partners result.ambient
  marked := optionOriginalOrbit_mark_log D partners Fmark φ result.ambient
    (AllocatedExternalLocalCandidate.optionJointMarkedOrbits
      (marked := marked) (partners := partners) Q) result.marked
  retained := result.retained
  subset := result.subset
  mass := result.mass
  step := result.step
  step_pos := result.step_pos
  slice := result.slice
  dense := result.dense
  inside := result.inside
  score z := (result.score z).trans_eq
    (P.optionJoint_ambientScore partners Q result.ambient _ _)

@[simp] theorem conclusion_of_optionJoint_ambient {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_optionJoint partners Q result).ambient =
      optionOriginalOrbit D partners result.ambient := rfl

@[simp] theorem conclusion_of_optionJoint_retained {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_optionJoint partners Q result).retained = result.retained := rfl

@[simp] theorem conclusion_of_optionJoint_step {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore)
    (z : result.retained) :
    (P.conclusion_of_optionJoint partners Q result).step z = result.step z := rfl

@[simp] theorem conclusion_of_optionJoint_slice {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore)
    (z : result.retained) :
    (P.conclusion_of_optionJoint partners Q result).slice z = result.slice z := rfl

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

end OAI
end


