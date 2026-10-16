-- Prove2me | Definitions.Def_OAIErdos3B1410
-- name    : OAIErdos3B1410
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T08:24:09.046609+00:00
-- url     : https://prove2.me/theorems/51264ba8-d840-4af2-871e-51e173c60939
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1411 of 1413
-- statement:
--   Definitions bundle 1411 of 1413 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1409`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1411 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.instNonemptySite_2`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.instNonemptySite_4`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.instNonemptySite_5`, `OAI.Erdos3.unconditionedSpatialWidthCutoff_le_exp`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1349

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateShearBufferedModel
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

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

local instance : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem unconditionedSpatialWidthCutoff_le_exp {P Q W τ : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hW : W ≤ Real.exp Q)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    unconditionedSpatialWidthCutoff W τ 1 ≤ Real.exp (Q + 2 * P + 16) := by
  have heP : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have heQ : 1 ≤ Real.exp Q := Real.one_le_exp_iff.mpr hQ
  have hfour : (4 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h128 : (128 : ℝ) ≤ Real.exp 16 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    have hp' : (128 : ℝ) ≤ Real.exp 7 := by
      norm_num [← Real.exp_nat_mul] at hp
      exact hp
    exact hp'.trans (Real.exp_le_exp.mpr (by norm_num))
  have hmax : max (8 * (probabilityProfileLipschitz : ℝ)) 1 ≤ 8 * Real.exp P :=
    max_le (mul_le_mul_of_nonneg_left hprofile (by norm_num)) (by linarith)
  unfold unconditionedSpatialWidthCutoff
  apply max_le
  · calc
      4 / τ ≤ Real.exp 16 * Real.exp P := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hfour hτP (inv_nonneg.mpr hτ.le) (Real.exp_nonneg _)
      _ = Real.exp (P + 16) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      8 * (1 + W) * max (8 * (probabilityProfileLipschitz : ℝ)) 1 / τ ≤
          8 * (2 * Real.exp Q) * (8 * Real.exp P) * Real.exp P := by
        rw [div_eq_mul_inv]
        gcongr
        linarith
      _ = 128 * Real.exp (Q + 2 * P) := by rw [Real.exp_add, two_mul P, Real.exp_add]; ring
      _ ≤ Real.exp 16 * Real.exp (Q + 2 * P) :=
        mul_le_mul_of_nonneg_right h128 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore
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

namespace AllocatedExternalCandidateProblem

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

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

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

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

local instance : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal TensorProduct Matrix

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

section AtLaw

variable [DecidableEq G]
variable {nX : ℕ} (N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
variable {Path : Type} [Fintype Path] [MeasurableSpace Path] [MeasurableSingletonClass Path]
variable (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hbox : (integerBox N).Nonempty)
variable (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U → FiniteProbabilityWeights Path)
variable (hweight : ∀ z, Measurable (fun center => (law center).weight z))

end AtLaw
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I J Eout : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {hmem : ∀ j d, coefficients (poly j) d ∈ U j}
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hmem
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem.Conclusion
local instance : Nonempty A.Site := A.site_nonempty
variable {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {degree d t : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable {Fmark : NilpotentLieFiltration M t}
variable {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
variable {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost massThreshold scoreThreshold outputMass outputScore : ℝ}
variable {P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le) Fmark φ marked
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost massThreshold scoreThreshold}
variable (out : P.Conclusion cost outputMass outputScore)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : out.retained, ActualFixedSpatialForecastPath (Eout := Eout)
  B U b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : out.retained, ∀ k,
  (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

local notation "input" z => out.denseSliceInput s qnum z (hkeep z) (ActualFixedSpatialForecastPath.commonTuple (path z))
  hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI

end


