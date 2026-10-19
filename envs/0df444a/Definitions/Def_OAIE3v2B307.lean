-- Prove2me | Definitions.Def_OAIE3v2B307
-- name    : OAIE3v2B307
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:04:18.257826+00:00
-- url     : https://prove2.me/theorems/13aa073c-d587-4283-8daa-4b920f23173b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 280 of 311
-- statement:
--   Definitions bundle 280 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B304`, `OAIE3v2B269` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidateRealThreshold.lean`, `Lattices/AllocatedAffineCanonicalBackendBudget.lean`, `Lattices/AllocatedAffinePhysicalBoundsSuccessor.lean`, `Lattices/AllocatedCertifiedAffinePhysicalSlowBound.lean`, `Lattices/CertifiedAffineNormalizedBudget.lean`, `Linear/ActualCandidateSlowProjectionMass.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B269

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

namespace AllocatedExternalLocalChart

variable {cost shortCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

variable (fixed : {i : C.Variables // ¬keep i.val} → ℤ)

variable (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
    (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

theorem freezeAxes_physical (u : {i // keep i} → ℤ) :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).physical u =
      C.physical (C.axisPoint keep fixed u) := by
  unfold physical
  rw [C.freezeAxes_parameter keep hkeep fixed hfixed]

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

def thresholdKeep (H : ℕ) (z : P.productive) (i : LayerSamplerVariables G I n B) : Prop :=
  (P.chart z).keep i ∧ H ≤ A.sides i

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRealThreshold
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

noncomputable def realThresholdKeep (bound : ℝ) :
    P.productive → LayerSamplerVariables G I n B → Prop :=
  P.thresholdKeep (candidateSideCutoff bound)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualCandidateSlowProjectionMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

omit [∀ j, Fintype (J j)] in
theorem fullTaggedCenteredCoordinates_support
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, J j → ℝ) (a : Σ j, J j) :
    fullTaggedCenteredCoordinates J poly c a ∈
      weightedSupportLE (fun _ : X => 1) (a.1.val + 1) := by
  apply (weightedSupportLE _ _).sub_mem ?_ (weightedSupportLE_C _ _ _)
  apply (mem_weightedSupportLE_iff _ _ _).mpr
  apply (scalar_weightedDegree_le_iff _ _ _).mpr
  intro α hα
  rw [coeff_coordinate, hp a.1 α hα, map_zero]

omit [∀ j, Fintype (J j)] in
theorem fullTaggedCenteredCoordinates_top
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (a : Σ j, J j) :
    homogeneousComponent (a.1.val + 1) (fullTaggedCenteredCoordinates J poly c a) =
      fullTaggedMajorTopCoordinates J poly a := by
  have hc : homogeneousComponent (a.1.val + 1) (C (c a.1 a.2) : MvPolynomial X ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simp
  simp only [fullTaggedCenteredCoordinates, map_sub, hc, sub_zero,
    fullTaggedMajorTopCoordinates]

theorem fullTaggedSlowProjectionChart_support
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, J j → ℝ) (z : X ⊕ (Σ j, J j)) :
    fullTaggedSlowProjectionChart J P N poly c z ∈
      weightedSupportLE (fullTaggedVariableWeight J) (fullTaggedVariableWeight J z) := by
  cases z with
  | inl x =>
    rw [fullTaggedSlowProjectionChart_inl, ← smul_eq_C_mul]
    exact (weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ _)
  | inr a =>
    rw [fullTaggedSlowProjectionChart_inr]
    apply (weightedSupportLE _ _).sub_mem
    · intro α hα
      exact (fullTaggedLinearMapChart_homogeneous J P (Sum.inr a) (mem_support_iff.mp hα)).le
    · exact majorParameterRename_degree (fun _ : X => 1) (fun a : Σ j, J j => a.1.val + 1)
        (fullTaggedCenteredCoordinates_support J poly hp c a)

theorem fullTaggedSlowProjectionChart_top
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (z : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J z)
        (fullTaggedSlowProjectionChart J P N poly c z) =
      aeval (fullTaggedLinearMapChart J P)
        (normalizedRealPolynomialChart N (fullTaggedMajorTopCoordinates J poly) z) := by
  rw [fullTaggedSlowProjectionChart, ← aeval_weightedHomogeneousComponent
    (fullTaggedVariableWeight J) (fullTaggedVariableWeight J) _
    (fullTaggedLinearMapChart_homogeneous J P)]
  congr 1
  cases z with
  | inl x =>
    exact weightedHomogeneousComponent_eq_self
      ((isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inl x)).C_mul _)
  | inr a =>
    rw [normalizedRealPolynomialChart_inr, normalizedRealPolynomialChart_inr, map_sub,
      weightedHomogeneousComponent_eq_self
        (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr a))]
    congr 1
    rw [rename_eq_aeval, ← aeval_weightedHomogeneousComponent (fun _ : X => 1)
      (fullTaggedVariableWeight J) (MvPolynomial.X ∘ Sum.inl)
      (fun x => isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inl x))]
    rw [← rename_eq_aeval]
    exact congrArg (rename Sum.inl) (fullTaggedCenteredCoordinates_top J poly c a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedSlowProjectionChart_physical_tag_abs_le
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j y, y ∈ U j → P j y = y) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (c : ∀ j, U j) (x : X → ℤ) (j : Fin m) (i : J j) :
    |MvPolynomial.eval
      (fun z => (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x z : ℝ))
      (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inr ⟨j, i⟩))| ≤
      ∑ a : J j, |P j (Pi.single a 1) i| := by
  rw [fullTaggedSlowProjectionChart_physical_tag J U P hP N poly hm c x j i,
    linearMap_pi_apply_eq_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [abs_mul]
  apply mul_le_of_le_one_right (abs_nonneg _)
  rw [abs_sub_comm]
  exact (abs_sub_round _).trans (by norm_num)

theorem fullTaggedSlowProjectionChart_physical_abs_le [Fintype X]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j y, y ∈ U j → P j y = y) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (c : ∀ j, U j) (x : X → ℤ) (hx : x ∈ integerBox N) {M : ℝ}
    (hrows : ∀ j i, (∑ a : J j, |P j (Pi.single a 1) i|) ≤ M)
    (z : X ⊕ (Σ j, J j)) :
    |MvPolynomial.eval
      (fun v => (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x v : ℝ))
      (fullTaggedSlowProjectionChart J P (fun v => (N v : ℝ)) poly (fun j => (c j).val) z)| ≤
      max 1 M := by
  cases z with
  | inl a =>
    exact (fullTaggedSlowProjectionChart_physical_spatial_abs_le_one
      J P N poly (fun j => (c j).val) x hx a).trans (le_max_left _ _)
  | inr a =>
    exact (fullTaggedSlowProjectionChart_physical_tag_abs_le
      J U P hP (fun v => (N v : ℝ)) poly hm c x a.1 a.2).trans
        ((hrows a.1 a.2).trans (le_max_right _ _))

theorem fullTaggedSlowProjectionChart_physical_abs_le_rational [Fintype X]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (Q : ∀ j, Matrix (J j) (J j) ℚ)
    (hQ : ∀ j y, y ∈ U j → fullTaggedRealMatrixProjection J Q j y = y)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (c : ∀ j, U j) (x : X → ℤ) (hx : x ∈ integerBox N) {H d : ℝ}
    (hheight : ∀ j i a, rationalLogHeight (Q j i a) ≤ H)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d)
    (z : X ⊕ (Σ j, J j)) :
    |MvPolynomial.eval
      (fun v => (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x v : ℝ))
      (fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J Q)
        (fun v => (N v : ℝ)) poly (fun j => (c j).val) z)| ≤ max 1 (d * Real.exp H) := by
  apply fullTaggedSlowProjectionChart_physical_abs_le J U
    (fullTaggedRealMatrixProjection J Q) hQ N poly hm c x hx _ z
  intro j i
  exact (fullTaggedRealMatrixProjection_rowSum_le J Q hheight j i).trans
    (mul_le_mul_of_nonneg_right (hdim j) (Real.exp_nonneg H))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCertifiedAffinePhysicalSlowBound
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
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

namespace AllocatedExternalCandidateProblem.CertifiedAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
    (C : P.CertifiedAffineRefinement K pAffine)

local notation "wt" => fullTaggedVariableWeight (X := X) J

theorem slowChart_support
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (i : X ⊕ (Σ j, J j)) :
    C.slowChart i ∈ weightedSupportLE wt (wt i) :=
  fullTaggedSlowProjectionChart_support J _ _ poly hpoly _ i

theorem slowChart_top (i : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent wt (wt i) (C.slowChart i) =
      aeval (fun a => weightedHomogeneousComponent wt (wt a) (C.globalChart a))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ))
          (fullTaggedMajorTopCoordinates J poly) i) := by
  simp only [C.globalChart_top]
  exact fullTaggedSlowProjectionChart_top J _ _ poly _ i

end AllocatedExternalCandidateProblem.CertifiedAffineRefinement
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound

theorem exists_allocatedCertifiedAffineFamilyReset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
      {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ i, Fintype (B i)]
      {U : ∀ j, Submodule ℝ (J j → ℝ)}
      {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
      {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
      {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
      {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
      {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
      {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
      {hm : ∀ j e, coefficients (poly j) e ∈ U j}
      {τ narrow : ℝ} {stride : X → ℕ}
      {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
      {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      {sampler : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ narrow stride cells center}
      {L M κ ξ μ χ : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [Fintype κ] [Fintype ξ] [Fintype μ] [Fintype χ]
      {d f : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
      (ω : Fin d → ℕ)
      (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
      (bF : Basis κ ℚ M) (ν : κ → ℕ)
      (hF : ∀ j, Fmark.filtration.layer j = span ℚ (bF '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    ∀ (keep : LayerSamplerVariables G I n B → Prop),
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : μ → D.filtration.AssociatedGraded),
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → Fmark.filtration.PolynomialSymbol (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      Submodule.span ℚ (Set.range vg) =
        (Fmark.filtration.symbolPointwiseSubalgebra bF ν hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ν)]
      (H l nFinal : ℕ) (pMap pNative : ℝ),
      1 ≤ H → 0 < l → 0 < nFinal → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → ((l * nFinal : ℕ) : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (d : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) H) →
      (∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H) →
      (∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (bF.repr (φ (D.basis i)) k) H) →
      (∀ j i, RationalHeightLE ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((Fmark.filtration.polynomialSymbolBasis bF ν hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)).repr (vg i) z) H) →
    ∃ mMap mReset : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l * nFinal ∣ mMap ∧ 0 < mReset ∧
      (mReset : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput (s + 1) a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ mReset ∧
    ∀ (marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      {cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := E) sampler D Fmark.filtration φ marked
        observable weight cost massThreshold scoreThreshold)
      {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
      (affine : P.CertifiedAffineRefinement K pAffine)
      (hkeep : ∀ z : affine.refinement.problem.productive,
        (affine.refinement.problem.chart z).keep = keep)
      (EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (factors : GlobalMarkedNativeFactors Fmark.filtration bF ν hF
        (fullTaggedVariableWeight J)
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))
        (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fullTaggedVariableWeight J) affine.globalChart affine.globalChart_support
          (Fmark.filtration.realification.polynomialOrbitCoordinates _ marked)) EF RF),
      Fmark.filtration.PolynomialRationalGrid bF (fullTaggedVariableWeight J) nFinal factors.right →
      (∀ z : affine.refinement.problem.productive,
        let C := affine.refinement.problem.chart z
        Fmark.filtration.PolynomialSlowBound bF (fun _ : C.Variables => 1)
          (fun i => (sampler.sides i.val : ℝ)) (Real.exp ((pNative + 2) ^ a))
          (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
            (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
            C.integerChart_support factors.left)) →
      (∀ i : {i : LayerSamplerVariables G I n B // keep i},
        Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ (sampler.sides i.val : ℝ)) →
    ∀ (q densityCost cutoff : ℝ),
      Real.exp q ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ a) →
      (∀ z : affine.refinement.problem.productive,
        let C := affine.refinement.problem.chart z
        IsDenseCommonStrideBox (fun i : C.Variables => sampler.sides i.val)
          densityCost C.slice.integerPoints) →
      Real.exp densityCost * ((s + 1 + 1 : ℕ) : ℝ) ≤ cutoff →
      (∀ i, keep i → cutoff ≤ layerSamplerBox B U btag S i) →
      (∀ z : (affine.refinement.problem.withKeep keep hkeep).productive,
        D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
          (fun i : {i : LayerSamplerVariables G I n B // keep i} => (sampler.sides i.val : ℝ))
          q l W (D.filtration.realification.polynomialOrbitCoordinates _
            ((affine.refinement.problem.withKeep keep hkeep).candidate z).orbit)) →
      Nonempty (AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
        affine.refinement.problem keep hkeep W factors
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput (s + 1) a Cf pNative)
          + Cnative) ^ Cnative)) mReset) := by
  classical
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_common_refiltered_globalMarked_family_reset (s + 1) a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ narrow stride cells center _ sampler L M κ ξ μ χ _ _ _ _ _ _ _ _ d f
    D Fmark φ hφ ω hD bF ν hF hsurj keep bk W v hW hvspan vg hvgspan _ _
    H l nFinal pMap pNative hH hl hnFinal hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
    hd hκ hξ hμ hχ hvars hHp hbracketD hbracketF hkernel hentries hv hvg
  obtain ⟨mMap, mReset, hmMap, hmMapBound, hdiv, hmReset, hmResetBound, hmMapReset, hrun⟩ :=
    hreset D.filtration Fmark.filtration φ hφ D.basis ω hD bF ν hF hsurj
      bk W v hW hvspan vg hvgspan H l nFinal pMap pNative hH hl hnFinal hpMap hpNative
      hsrc htgt hHmap hlmap hmabsorb (by simpa using hd) hκ hξ hμ hχ hvars hHp
      hbracketD hbracketF hkernel hentries hv hvg
  refine ⟨mMap, mReset, hmMap, hmMapBound, hdiv, hmReset, hmResetBound, hmMapReset, ?_⟩
  intro marked observable weight cost massThreshold scoreThreshold P K pAffine affine hkeep
    EF RF factors hgrid hslow hside q densityCost cutoff hq hqmap hdensity hcutoff hlong hcommon
  let Q := affine.refinement.problem.withKeep keep hkeep
  have hfixed (z : Q.productive) :=
    (affine.refinement.problem.chart z).withKeep_chart_fixed keep (hkeep z)
      affine.globalChart (affine.chart_fixed z)
  have hslow' (z : Q.productive) :=
    (affine.refinement.problem.chart z).withKeep_polynomialSlowBound keep (hkeep z)
      Fmark.filtration bF factors.left (Real.exp ((pNative + 2) ^ a)) (hslow z)
  have hmarked (z : Q.productive) := (Q.candidate z).formal_mark_group hφ (by
    simp only [max_self]
    apply (Q.chart z).slice_length_gt_of_dense_cutoff
      ((affine.refinement.problem.chart z).withKeep_dense keep (hkeep z) densityCost (hdensity z))
      (s + 1) hcutoff
    exact hlong)
  obtain ⟨left, middle, right, native, hfactors⟩ := hrun
    (fullTaggedVariableWeight J) affine.globalChart affine.globalChart_support
    (Fmark.filtration.realification.polynomialOrbitCoordinates _ marked) EF RF factors hgrid
    (fun _ : Q.productive => fun i : {i : LayerSamplerVariables G I n B // keep i} => (sampler.sides i.val : ℝ))
    (fun _ => q) (fun z => (Q.chart z).integerChart) (fun z => (Q.chart z).integerChart_support)
    (fun _ => hside) (fun _ => hq) (fun _ => hqmap) hfixed hslow'
    (fun z => D.filtration.realification.polynomialOrbitCoordinates _ (Q.candidate z).orbit)
    hmarked hcommon
  exact ⟨{
    localLeft := left
    localMiddle := middle
    localRight := right
    native := native
    source_factor := fun z => (hfactors z).1
    projection_left := fun z => (hfactors z).2.1
    projection_right := fun z => (hfactors z).2.2.1
    projection_middle := fun z => (hfactors z).2.2.2.1
    slow_left := fun z => (hfactors z).2.2.2.2.1
    grid_right := fun z => (hfactors z).2.2.2.2.2.1
    native_log := fun z => (hfactors z).2.2.2.2.2.2.1 }⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realChartSubstitute PolynomialRationalGrid PolynomialSlowBound
  CertifiedFullChartFiniteHistory.outer

theorem exists_allocatedCertifiedAffineGlobalTerminal (t a : ℕ) :
    ∃ Ce Cr : ℕ, 2 ≤ Ce ∧ 2 ≤ Cr ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
      {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ i, Fintype (B i)]
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
      {sampler : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
      {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
      {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
      {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
      {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
      {cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := E) sampler D Fmark φ marked observable weight
        cost massThreshold scoreThreshold)
      {ι η : Type} [Fintype ι] [Fintype η]
      (bF : Basis ι ℚ M) (ω : ι → ℕ)
      (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ Fmark.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.AssociatedGraded ⧸ W.toSubmodule)))
      (lift : (Fmark.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
      (Z : Fmark.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Bphase budget pAffine : ℝ)
      (history : CertifiedFullChartFiniteHistory Fmark bF ω hF J W.toSubmodule basis lift
        Z Set.univ U poly N Bphase t)
      (affine : P.CertifiedAffineRefinement history.K pAffine),
      BasisGradedSubmodule (Fmark.associatedGradedBasis bF ω hF) ω W.toSubmodule →
      FullChartControlledFactors Fmark bF ω hF J poly N history.outer.1 history.outer.2 budget →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      Fmark.realPolynomialSymbolHom bF ω hF (fullTaggedVariableWeight (X := X) J)
        (Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked) = Z →
    ∀ (H : ℕ) (pFull : ℝ), 1 ≤ H → 0 ≤ pFull →
      (Fintype.card ι : ℝ) ≤ pFull →
      (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pFull →
      (H : ℝ) ≤ Real.exp pFull →
      Real.exp budget * (Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine)) ^ t ≤
        Real.exp pFull →
      (∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H) →
      let wt := fullTaggedVariableWeight (X := X) J
      let β := affine.globalChart
      let δ := affine.slowChart
      let pull := Fmark.realSymbolHomogeneousPullbackHom bF ω hF wt wt
        (fun i => weightedHomogeneousComponent wt (wt i) (β i))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      0 < affine.commonDenominator ∧
      (affine.commonDenominator : ℝ) ≤ Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine) ∧
      ∃ q nFinal : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
        0 < nFinal ∧ (nFinal : ℝ) ≤ Real.exp ((pFull + Cr) ^ Cr) ∧
        q * affine.commonDenominator ^ t ∣ nFinal ∧
        ∃ factors : GlobalMarkedNativeFactors Fmark bF ω hF wt W
          (Fmark.weightedAdaptedRealChartHom wt wt β affine.globalChart_support
            (Fmark.realification.polynomialOrbitCoordinates wt marked))
          (pull history.outer.1) (pull history.outer.2),
          Fmark.PolynomialRationalGrid bF wt nFinal factors.right ∧
          ∀ {Υ : Type*} [Fintype Υ] (v : Υ → ℕ), (∀ i, 0 < v i) →
            (Fintype.card Υ : ℝ) ≤ pFull →
            ∀ (γ : (X ⊕ (Σ j, J j)) → MvPolynomial Υ ℝ)
              (hγ : ∀ i, γ i ∈ weightedSupportLE v (wt i))
              (T : Υ → ℝ), (∀ i, 0 < T i) →
            ∀ mass : ℝ, 1 ≤ mass →
              (∀ i, realPolynomialMass
                (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ mass) →
              (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ t *
                Real.exp budget * mass ^ t ≤ Real.exp ((pFull + 2) ^ a)) →
              Fmark.PolynomialSlowBound bF v T (Real.exp ((pFull + Ce) ^ Ce))
                (Fmark.weightedAdaptedRealChartHom wt v γ hγ factors.left) := by
  obtain ⟨Ce, Cr, hCe, hCr, hterminal⟩ :=
    exists_controlled_terminal_globalMarkedNativeFactors t a
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ ξ stride cells center _ sampler L M _ _ _ _ s d D Fmark φ marked observable weight
    cost massThreshold scoreThreshold P ι η _ _ bF ω hF W basis lift Z Bphase budget pAffine
    history affine hW hcontrol hpoly hZ H pFull hH hpFull hι hvars hHp hden hbracket
  let wt := fullTaggedVariableWeight (X := X) J
  let β := affine.globalChart
  let δ := affine.slowChart
  have hden' : Real.exp budget * (affine.commonDenominator : ℝ) ^ t ≤ Real.exp pFull :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) affine.commonDenominator_bound t)
      (Real.exp_nonneg _)).trans hden
  obtain ⟨q, nFinal, hq, hqB, hn, hnB, hdiv, hproduce⟩ := hterminal
    Fmark bF ω hF J W basis lift Z Set.univ U poly N Bphase budget history hW hcontrol
    β δ affine.globalChart_support (affine.slowChart_support hpoly)
    affine.slowChart_top affine.globalChart_top_mem
    affine.commonDenominator H pFull affine.commonDenominator_pos hH hpFull hι hvars hHp
    hden' hbracket affine.globalChart_top_grid
  refine ⟨affine.commonDenominator_pos, affine.commonDenominator_bound,
    q, nFinal, hq, hqB, hn, hnB, hdiv, ?_⟩
  exact hproduce (Fmark.realification.polynomialOrbitCoordinates wt marked) hZ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem

noncomputable def allocatedAffineResetCompareExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_allocatedCertifiedAffineFamilyReset s 1)

noncomputable def allocatedAffineResetFactorExponent (s : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (exists_allocatedCertifiedAffineFamilyReset s 1))

noncomputable def allocatedAffineResetLiftExponent (s : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_allocatedCertifiedAffineFamilyReset s 1)))

noncomputable def allocatedAffineResetLogBudget (s : ℕ) (pNative : ℝ) : ℝ :=
  (markedNativeLiftInput
    (fullMarkedNativeInput (s + 1) 1 (allocatedAffineResetFactorExponent s) pNative) +
    allocatedAffineResetLiftExponent s) ^ allocatedAffineResetLiftExponent s

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
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

namespace AllocatedExternalCandidateProblem.CertifiedAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
    (C : P.CertifiedAffineRefinement K pAffine)

theorem slowChart_physical_abs_le
    (hretained : ∀ x, (∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ U j) → x ∈ K)
    {dTag : ℝ} (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ dTag)
    (x : X → ℤ) (hx : x ∈ integerBox N) (z : X ⊕ (Σ j, J j)) :
    |MvPolynomial.eval (fun v => (P.physicalIntegerPoint x v : ℝ)) (C.slowChart z)| ≤
      max 1 (dTag * Real.exp (((pAffine + ((pAffine + 2) ^ 2 + 2) ^ 63) + 2) ^ 8)) := by
  exact fullTaggedSlowProjectionChart_physical_abs_le_rational J U C.projection
    (C.projection_fixes_original hretained) N poly hm P.centerLift x hx
    C.projection_height hdim z

end AllocatedExternalCandidateProblem.CertifiedAffineRefinement
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineNormalizedBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] integerProgressionSupport

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

structure CertifiedThresholdAffineRefinement
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (p separation : ℝ) where
  freezing : P.AxisFreezing (P.realThresholdKeep separation) (candidateSideCutoffCost separation)
  affine : freezing.problem.CertifiedAffineRefinement K p

namespace CertifiedThresholdAffineRefinement

variable {P} {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}
    (selected : P.CertifiedThresholdAffineRefinement K p separation)

noncomputable abbrev problem := selected.affine.refinement.problem

end CertifiedThresholdAffineRefinement

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

namespace AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}

theorem common_keep (selected : P.CertifiedThresholdAffineRefinement K p separation)
    (hcost : Real.exp cost ≤ separation) (z : selected.problem.productive) :
    (selected.problem.chart z).keep =
      fun i => candidateSideCutoff separation ≤ A.sides i := by
  funext i
  apply propext
  change ((P.chart ⟨z.val, selected.affine.refinement.subset z.property⟩).keep i ∧
    candidateSideCutoff separation ≤ A.sides i) ↔ _
  constructor
  · exact fun hi => hi.2
  · intro hi
    refine ⟨?_, hi⟩
    by_contra hnot
    have hfrozen := P.frozen_side
      ⟨z.val, selected.affine.refinement.subset z.property⟩ ⟨i, hnot⟩
    have hside : (candidateSideCutoff separation : ℝ) ≤ (A.sides i : ℝ) :=
      Nat.cast_le.mpr hi
    exact (not_lt_of_ge (hfrozen.trans hcost))
      ((lt_candidateSideCutoff separation).trans_le hside)

end AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineCanonicalBackendBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

noncomputable def allocatedAffineResetCompareLog (s : ℕ) (pNative : ℝ) : ℝ :=
  (pNative + allocatedAffineResetCompareExponent s) ^ allocatedAffineResetCompareExponent s

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalBoundsSuccessor
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

namespace AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}

variable (selected : P.CertifiedThresholdAffineRefinement K p separation)

@[simp] theorem problem_physicalIntegerPoint (x : X → ℤ) :
    selected.problem.physicalIntegerPoint x = P.physicalIntegerPoint x := rfl

@[simp] theorem withKeep_physicalIntegerPoint
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : selected.problem.productive, (selected.problem.chart z).keep = keep)
    (x : X → ℤ) :
    (selected.problem.withKeep keep hkeep).physicalIntegerPoint x =
      P.physicalIntegerPoint x := rfl

end AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement
end Erdos3.VectorPolynomial

end

end OAI
end


