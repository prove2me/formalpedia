-- Prove2me | Definitions.Def_OAIErdos3B1389
-- name    : OAIErdos3B1389
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T08:34:30.274979+00:00
-- url     : https://prove2.me/theorems/e5a7112c-f01e-4eb3-81c7-c004c5088b6d
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1390 of 1413
-- statement:
--   Definitions bundle 1390 of 1413 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1388`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1390 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.forecastResidueTest_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedActiveContainedProgression_value`, `OAI.Erdos3.VectorPolynomial.allocatedActiveContainedTupleMap_eq`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceMap_contained_physical`, `OAI.Erdos3.VectorPolynomial.forecastJointCoordinateJoinEquiv_apply`, `OAI.Erdos3.VectorPolynomial.forecastJointCoordinateJoinEquiv_measurePreserving`, `OAI.Erdos3.VectorPolynomial.forecastJointCoordinateJoin_integral`, `OAI.Erdos3.VectorPolynomial.forecastJointCoordinateJoin_isometry`, `OAI.Erdos3.VectorPolynomial.forecastJointCoordinateJoin_lipschitz`, `OAI.Erdos3.VectorPolynomial.forecastJointCoordinateJoin_norm`, `OAI.Erdos3.VectorPolynomial.forecastJointCoordinateJoin_zero`, `OAI.Erdos3.VectorPolynomial.rowsAmbientSite_eq`, `OAI.Erdos3.VectorPolynomial.rowsAmbientSite_lipschitz`, `OAI.Erdos3.fixedSpatialEmptyDensity_bounds`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1388

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActiveContainedTupleMap
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedActiveContainedProgression_value
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0) (j : Input) :
    (allocatedActiveContainedProgression B U basis S step H c hsubset v j none : ℤ) =
      c j + (step j : ℤ) * (v j none : ℤ) := by
  have hb := integerScalarCubePi_root_bounds H hH v hv j
  have hc : IntegerScalarCube (H j) (fun i => (v j i : ℤ)) := by
    intro t
    have ht : t = ∅ := Subsingleton.elim _ _
    subst t
    simpa only [integerScalarCubeValue, Finset.sum_empty, add_zero] using
      (show 0 ≤ (v j none : ℤ) ∧ (v j none : ℤ) < (H j : ℤ) from ⟨hb.1, by have := hH j; omega⟩)
  simpa only [allocatedActiveContainedProgression, ite_true] using
    containedProgressionCubeMap_value Empty S.value (H j) (step j) (c j)
      S.positive (hsubset j) (v j) hc none

theorem allocatedOriginalSampleFullSliceMap_contained_physical
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (u : PrincipalAxisTuples (α := Empty) short sides) :
    allocatedOriginalSampleFullSliceMap B U basis S x u
      (fun _ _ => 0) (fun _ _ => 1) sample
      (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value) =
      fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
        (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x
          (principalAxisJoin short u
            (allocatedActiveContainedProgression B U basis S step H c hsubset v))) o.1.val := by
  have he (j : Input) :
      (allocatedActiveContainedProgression B U basis S step H c hsubset v j none : ℝ) =
      (c j : ℝ) + (step j : ℝ) * (v j none : ℝ) := by
    exact_mod_cast allocatedActiveContainedProgression_value B U basis S step H c hH hsubset v hv j
  simpa only [he] using allocatedOriginalSampleFullSliceMap_physical_join B U basis S sample x u
    (allocatedActiveContainedProgression B U basis S step H c hsubset v)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => layerSamplerDegree I n (Subtype.val a))
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedActiveContainedTupleMap_eq
    (step H : Input → ℕ) (c : Input → ℤ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ)) :
    containedProgressionTupleMap (α := Empty)
      (fun a : Active => B (Subtype.val a)) (fun a : Active => layerSamplerDegree I n (Subtype.val a))
      (principalAxisLength (fun a => ¬short a) sides) H step c
      (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)
      (fun j => by
        simpa only [principalAxisLength, allocatedPrincipalSides_not_short B U basis S j.1 j.2]
          using hsubset j) =
      allocatedActiveContainedProgression B U basis S step H c hsubset := by
  funext v j i
  apply Subtype.ext
  simp only [containedProgressionTupleMap, allocatedActiveContainedProgression,
    containedProgressionCubeMap]
  split_ifs <;> rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiniteModelPhysicalExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {O J : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

omit [Fintype α] in
theorem rowsAmbientSite_eq (s : Finset α) (d : ℕ)
    (y : EuclideanJetLayers U (fun j => {t : Finset α // t ∈ rowSets j})) :
    rowsAmbientSite rowSets s (coveredJetAmbientTorus U d y) =
      coveredJetAmbientTorus U d (coveredRowsSiteValue rowSets U y s) := by
  funext a
  simp only [rowsAmbientSite, coveredRowsSiteValue, coveredJetAmbientTorus,
    map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]

omit [Fintype α] in
theorem rowsAmbientSite_lipschitz (s : Finset α) :
    LipschitzWith (∑ j : Fin m, ((rowSets j).card : ℝ≥0))
      (rowsAmbientSite (J := J) rowSets s) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, t, i⟩
  have hterm (r : {t : Finset α // t ∈ rowSets j}) :
      dist (rowRestrictedSiteMatrix (rowSets j) s r • z ⟨j,r,i⟩)
        (rowRestrictedSiteMatrix (rowSets j) s r • w ⟨j,r,i⟩) ≤ dist z w := by
    simp only [rowRestrictedSiteMatrix, booleanReconstructionMatrix]
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨j,r,i⟩
    · simpa only [zero_zsmul, dist_self] using (dist_nonneg : 0 ≤ dist z w)
  have hc : ((rowSets j).card : ℝ≥0) ≤ ∑ j : Fin m, ((rowSets j).card : ℝ≥0) :=
    Finset.single_le_sum (f := fun j : Fin m => ((rowSets j).card : ℝ≥0))
      (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _r : {t : Finset α // t ∈ rowSets j}, dist z w :=
      (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun r _ => hterm r))
    _ = ((rowSets j).card : ℝ) * dist z w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSpatialEmptyCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {X : Type*}

variable [Fintype X]

theorem fixedSpatialEmptyDensity_bounds (f : (X → ℝ) → ℝ) {C : ℝ} {L : ℝ≥0}
    (hC : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hL : LipschitzWith L f) :
    (∀ v, fixedSpatialEmptyDensity f v ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith L (fixedSpatialEmptyDensity f) := by
  refine ⟨fun v => hC _, ?_⟩
  have hi : LipschitzWith 1 (fun v : (Σ _ : X, Unit ⊕ Empty) → ℝ =>
      (fixedSpatialEmptyCoordinates (X := X)).symm v) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simp only [NNReal.coe_one, one_mul]
    exact le_of_eq ((fixedSpatialEmptyCoordinates (X := X)).symm.isometry.dist_eq v w)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
    (by simpa only [NNReal.coe_one, one_mul] using hi.dist_le_mul v w) (NNReal.coe_nonneg L))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastNativeResidueTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical Matrix

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ) (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E P)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit)

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {L : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)

theorem forecastResidueTest_bounds (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (sheet : ∀ j, {i : Fin (n j) // P ⟨j, .inr i⟩} → ℤ)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (center : X → ℝ) (τ : ℝ) (out : Out → ZMod q) :
    (∀ y, ‖W.forecastResidueTest U b hb o bW R P q hm hperiod hcover sheet frozen center τ out y‖ ≤ 1) ∧
      LipschitzWith (L * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
        (W.forecastResidueTest U b hb o bW R P q hm hperiod hcover sheet frozen center τ out) :=
  ⟨W.forecastPullback_norm_le U b o R P _ _ center τ frozen,
    W.forecastPullback_lipschitz U b o R P _ _ center τ frozen⟩

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastActiveGridIntegralComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical NNReal

variable {X : Type*} [Fintype X]
variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis L a}, Unit)
local notation "Cont" => (Σ j : Fin m, I j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L

omit [Fintype X] [∀ j, Fintype (I j)] in
theorem forecastJointCoordinateJoinEquiv_apply
    (p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ)) :
    forecastJointCoordinateJoinEquiv U basis L p =
      forecastJointCoordinateJoin U basis L p.1 p.2 := by
  apply Prod.ext
  · funext a
    simp [forecastJointCoordinateJoinEquiv, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
      forecastJointCoordinateJoin, forecastJointAxisEquiv]
  · funext a
    cases h : forecastActiveAxisEquiv U basis L a <;>
      simp [forecastJointCoordinateJoinEquiv, MeasurableEquiv.sumPiEquivProdPi,
        MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
        forecastJointCoordinateJoin, forecastJointAxisEquiv, forecastActiveCoordinateJoin, h]

theorem forecastJointCoordinateJoinEquiv_measurePreserving :
    MeasurePreserving (forecastJointCoordinateJoinEquiv (X := X) (I := I) U basis L)
      volume volume := by
  exact (volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Spatial ⊕ Output => ℝ)).comp
      ((volume_measurePreserving_piCongrLeft (fun _ : Spatial ⊕ Output => ℝ)
        (forecastJointAxisEquiv (X := X) (I := I) U basis L).symm).comp
          (volume_measurePreserving_sumPiEquivProdPi_symm
            (fun _ : Cont ⊕ (X ⊕ IntAxis) => ℝ)))

theorem forecastJointCoordinateJoin_isometry :
    Isometry (fun p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ) =>
      forecastJointCoordinateJoin U basis L p.1 p.2) := by
  let e : ((Cont → ℝ) × ((X ⊕ IntAxis) → ℝ)) ≃ᵢ
      ((Spatial → ℝ) × (Output → ℝ)) :=
    IsometryEquiv.sumArrowIsometryEquivProdArrow.symm.trans
      ((IsometryEquiv.piCongrLeft (Y := fun _ : Spatial ⊕ Output => ℝ)
        (forecastJointAxisEquiv (X := X) (I := I) U basis L).symm).trans
          IsometryEquiv.sumArrowIsometryEquivProdArrow)
  have he : (e : _ → _) = fun p => forecastJointCoordinateJoin U basis L p.1 p.2 := by
    funext p
    exact forecastJointCoordinateJoinEquiv_apply U basis L p
  rw [← he]
  exact e.isometry

theorem forecastJointCoordinateJoin_lipschitz :
    LipschitzWith 1 (fun p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ) =>
      forecastJointCoordinateJoin U basis L p.1 p.2) :=
  (forecastJointCoordinateJoin_isometry (X := X) (I := I) U basis L).lipschitz

omit [Fintype X] [∀ j, Fintype (I j)] in
theorem forecastJointCoordinateJoin_zero :
    forecastJointCoordinateJoin (X := X) (I := I) U basis L 0 0 = 0 := by
  apply Prod.ext <;> funext a
  · rfl
  · change Sum.elim (fun _ => (0 : ℝ)) (fun _ => 0)
      (forecastActiveAxisEquiv U basis L a) = 0
    cases forecastActiveAxisEquiv U basis L a <;> rfl

theorem forecastJointCoordinateJoin_norm (c : Cont → ℝ) (z : (X ⊕ IntAxis) → ℝ) :
    ‖forecastJointCoordinateJoin U basis L c z‖ = max ‖c‖ ‖z‖ := by
  have h := (forecastJointCoordinateJoin_isometry (X := X) (I := I) U basis L).dist_eq
    (c, z) (0, 0)
  simpa only [forecastJointCoordinateJoin_zero, Prod.dist_eq, dist_zero_right, Prod.norm_def] using h

theorem forecastJointCoordinateJoin_integral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ((Spatial → ℝ) × (Output → ℝ)) → V) :
    (∫ y, F y) = ∫ p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ),
      F (forecastJointCoordinateJoin U basis L p.1 p.2) := by
  simpa only [forecastJointCoordinateJoinEquiv_apply] using
    ((forecastJointCoordinateJoinEquiv_measurePreserving (X := X) (I := I) U basis L).integral_comp (forecastJointCoordinateJoinEquiv U basis L).measurableEmbedding F).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

end OAI

end


