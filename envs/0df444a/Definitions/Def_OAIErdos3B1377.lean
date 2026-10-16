-- Prove2me | Definitions.Def_OAIErdos3B1377
-- name    : OAIErdos3B1377
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T00:25:26.174636+00:00
-- url     : https://prove2.me/theorems/943bccb3-c04e-4519-bb0d-d8d4bd173c47
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1378 of 1379
-- statement:
--   Definitions bundle 1378 of 1379 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1376`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1378 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.allocatedFullGridChartModel_mixed`, `OAI.Erdos3.VectorPolynomial.allocatedFullGridChartModel_norm_le`, `OAI.Erdos3.VectorPolynomial.allocatedFullGridNaturalVolume_pos`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalGridJetPMF_restrict_join`, `OAI.Erdos3.VectorPolynomial.allocatedProductFullGridPrefactor_zero`, `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalJointPMF_grid_marginal`, `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalJointPMF_grid_mean`, `OAI.Erdos3.complex_div_two_norm_le`, `OAI.Erdos3.lipschitz_complex_div_two`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198
import Definitions.Def_OAIErdos3B1375

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealPhysicalCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))
variable (k : ∀ a, (e a).Term) (s : S)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem lipschitz_complex_div_two {X : Type*} [PseudoMetricSpace X]
    (f : X → ℂ) (K : ℝ≥0) (hf : LipschitzWith (2 * K) f) :
    LipschitzWith K (fun x => f x / 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← sub_div, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h := hf.dist_le_mul x y
  simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat] at h
  nlinarith only [h]

theorem complex_div_two_norm_le {z : ℂ} (hz : ‖z‖ ≤ 2) : ‖z / 2‖ ≤ 1 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_div, h2]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using hz)

attribute [local instance] ScalarSiteExpansion.termFinite

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite

open Module Submodule

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}

attribute [local instance 2000] activeAmbientAxisDecidableEq

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))


variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d]
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d]
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S

variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S

variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedGridMarginal
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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

variable (hselected : Function.Injective selected)
variable (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
  ⟨(selected a).1, Sum.inr (selected a).2⟩)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

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
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (rows : A → Finset (Finset α))

end Erdos3.VectorPolynomial

end

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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell grid

omit [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] in
theorem allocatedPhysicalGridJetPMF_restrict_join (j : Fin m) (i : Fin (n j))
    (hgrid : grid ⟨j, Sum.inr i⟩)
    (row : Finset (Finset α))
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) (fun t : row => (t : Finset α)))
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid (principalAxisRestrict grid y) v₀))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid (principalAxisRestrict grid y) v₀))
      (j.val + 1) (fun t : row => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i) := by
  rw [allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid x y,
    allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid x (principalAxisJoin grid (principalAxisRestrict grid y) v₀)]
  congr 1
  funext c t
  simp only [principalAxisJoin, principalAxisRestrict, hgrid, ↓reduceDIte]

theorem allocatedSupportedSlicedPhysicalJointPMF_grid_marginal
    (hgrid : ∀ a, grid ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)) :
    allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x =
      (gridLaw).toPMF.bind (fun u => dependentProductPMF (fun a =>
        integerMatrixImagePMF (boundedCoefficientJetMatrix
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v₀))
          (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v₀)) ((selected a).1.val + 1)
          (fun t : rows a => (t : Finset α)))
          (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2))) := by
  let k (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)) : PMF (∀ a, rows a → ℤ) :=
    dependentProductPMF (fun a => integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v₀))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v₀)) ((selected a).1.val + 1)
      (fun t : rows a => (t : Finset α)))
      (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2))
  have hm := congrArg (fun p => p.bind k)
    (containedSupportedProgressionLaw_axis_marginal B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S)
      hH hsubset q r hcell grid)
  rw [PMF.bind_map] at hm
  refine Eq.trans ?_ hm
  apply congrArg (conditioned).toPMF.bind
  funext y
  apply congrArg dependentProductPMF
  funext a
  exact allocatedPhysicalGridJetPMF_restrict_join B U basis hR hσ S x (selected a).1 (selected a).2
    (hgrid a) (rows a) y v₀

theorem allocatedSupportedSlicedPhysicalJointPMF_grid_mean
    (hgrid : ∀ a, grid ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (z : ∀ a, rows a → ℤ) :
    (allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x z).toReal =
      (gridLaw).mean (fun u => ∏ a,
        (integerMatrixImagePMF (boundedCoefficientJetMatrix
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v₀))
          (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v₀)) ((selected a).1.val + 1)
          (fun t : rows a => (t : Finset α)))
          (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2) (z a)).toReal) := by
  rw [allocatedSupportedSlicedPhysicalJointPMF_grid_marginal B U basis hR hσ S q r H step c hH hsubset hcell
    selected rows x hgrid v₀, FiniteProbabilityWeights.toPMF_bind_toReal]
  apply congrArg (gridLaw).mean
  funext u
  rw [dependentProductPMF_apply, ENNReal.toReal_prod]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedFullGridNaturalVolume_pos : 0 < allocatedFullGridNaturalVolume B U b S rowSets :=
  Finset.prod_pos (fun a _ => pow_pos (Nat.cast_pos.mpr (allocatedGridNaturalScale_pos B U b hR S a)) _)

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (rowSets : Fin m → Finset (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


variable {D : ℝ} (hd : AllocatedComparisonDimensions (G := G) B α (fun j : Fin m => (rowSets j : Type uα)) D)

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

variable (x : G → IntegerScalarCubeBox α S.value)

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{uα,uα} (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (q : ℕ)


variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a // allocatedGridAxis (I := I) U b S.value a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (T : Fin m → ℝ)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (T : Fin m → ℝ)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFullGridChartModelMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedProductFullGridPrefactor_zero (y : EuclideanJetLayers U rowTypes)
    (hy : y ∉ chart '' region) :
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f y = 0 := by
  have hp : allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f y = 0 := by
    unfold allocatedWholeMaskedGridlessProfile allocatedGridlessCoveredProfile
    exact restrictedChartDensity_zero _ _ _ _ hy
  rw [allocatedProductFullGridPrefactor, hp, Complex.ofReal_zero, mul_zero, mul_zero]

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedFullGridChartModel_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedFullGridChartModel B U b S rowSets d hb o bW e (chart z) =
      allocatedFullGridSiteApproximation B U b S rowSets e
        (allocatedFullGridRowsOfMixed B U b S rowSets z.1) :=
  allocatedComplexGridMultiplier_apply B U b S rowTypes hb o bW d _ z hz

theorem allocatedFullGridChartModel_norm_le
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤ ∏ a, Cc a := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedFullGridChartModel_mixed B U b S rowSets d hb o bW e z hz,
      allocatedFullGridSiteApproximation, siteFamilyEval_eq, norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun axis _ => (e axis).eval_norm_le (he axis) _ _)
  · rw [allocatedFullGridChartModel, allocatedComplexGridMultiplier_zero B U b S rowTypes hb o bW d _ y hy, norm_zero]
    exact Finset.prod_nonneg (fun a _ => (Finset.sum_nonneg (fun k _ => norm_nonneg _)).trans (he a).coefficient_le)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

end Erdos3.VectorPolynomial

end

end OAI

end


