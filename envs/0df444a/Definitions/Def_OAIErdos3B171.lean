-- Prove2me | Definitions.Def_OAIErdos3B171
-- name    : OAIErdos3B171
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T23:20:20.946644+00:00
-- url     : https://prove2.me/theorems/190375d9-4288-4cd0-864b-d57027f38f80
-- title:
--   OpenAI Erdős-3 split, definitions bundle 172 of 177
-- statement:
--   Definitions bundle 172 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B170`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 172 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.recOn`, `OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial`, `OAI.Erdos3.VectorPolynomial.allocatedInactiveAffineIntervalLaw`, `OAI.Erdos3.VectorPolynomial.allocatedJointResidueOutput`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleCongruenceProjection`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleDeckValue`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalResidueJoin`, `OAI.Erdos3.VectorPolynomial.allocatedRowIdealCoordinates`, `OAI.Erdos3.VectorPolynomial.allocatedRowSlicedIdeal`, `OAI.Erdos3.VectorPolynomial.allocatedRowSlicedSiteRadius`, `OAI.Erdos3.VectorPolynomial.allocatedShortPrincipalRaw`, `OAI.Erdos3.VectorPolynomial.exists_measurable_coefficient_representative_of_layers`, `OAI.Erdos3.VectorPolynomial.exists_measurable_subtractive_constant_center`, `OAI.Erdos3.VectorPolynomial.exists_measurable_subtractive_constant_center_of_representative`, `OAI.Erdos3.VectorPolynomial.forecastInactiveFixedOutput`, `OAI.Erdos3.VectorPolynomial.fullBooleanRowSetFintype`, `OAI.Erdos3.exists_finite_triangular_rational_correction`, `OAI.Erdos3.exists_triangular_rational_correction_enumeration`, `OAI.Erdos3.realRowsSiteValue`, `_private.Estimates.FiniteTriangularRationalCorrection.0.OAI.Erdos3.exists_finite_triangular_correction_of_windows`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B135
import Definitions.Def_OAIErdos3B141
import Definitions.Def_OAIErdos3B174

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedWholeProfileEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

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
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (q : ℕ) [NeZero q]
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (CM Cf : ℝ≥0) (hCM : 1 ≤ (CM : ℝ)) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (P δ Λ : ℝ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

@[instance_reducible]
noncomputable def fullBooleanRowSetFintype (dim degree : ℕ) :
    Fintype {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) degree} :=
  Finset.Subtype.fintype _

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable (q : ℕ) [NeZero q]
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable (hq : 0 < q) (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
variable (P δ Λ : ℝ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) [Fintype Z] {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def realRowsSiteValue (rows : Finset (Finset α))
    (v : rows → ℝ) (s : Finset α) : ℝ :=
  ∑ t : rows, v t * (if t.val ⊆ s then 1 else 0)

namespace VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedRowIdealCoordinates (z : AllocatedLongJetRows B U b S rowTypes) :
    Finset α → LayerSamplerAxis I n → ℝ :=
  fun s a => realRowsSiteValue (rowSets a.1) (fun t =>
    if ha : ¬grid a then allocatedLongJetRealCoordinates B U b S z ⟨⟨a, ha⟩, t⟩ / R a.1
    else 0) s

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))

noncomputable def allocatedRowSlicedIdeal (ρ : ℝ≥0) (center width : input → ℝ) :
    (output → ℝ) → ℝ :=
  diagonalImageDensity (fun o : output => R o.1.val.1)
    (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α)) ρ center width)

noncomputable def allocatedRowSlicedSiteRadius : ℝ≥0 :=
  ⟨1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1), by
    have := partitionedIdealRadius_nonneg α m
    positivity⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSourceNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

structure AllocatedSourceNumerics (P : ℝ) : Prop where
  nonneg : 0 ≤ P
  degree : (m : ℝ) ≤ P
  variable_count : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P
  length : (S.value : ℝ) ≤ Real.exp P
  radius_inv : ∀ j, (R j)⁻¹ ≤ Real.exp P
  width_inv : ∀ j, (σ j)⁻¹ ≤ Real.exp P
  coefficients : ∀ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P
  real_axes : ∀ j, (Fintype.card (I j) : ℝ) ≤ P
  integer_axes : ∀ j, (n j : ℝ) ≤ P
  ambient_axes : ∀ j, (Fintype.card (J j) : ℝ) ≤ P
  profile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P
  chart : ∀ j, (C j : ℝ) ≤ Real.exp P
  covolume : ∀ j, (V j : ℝ) ≤ Real.exp P
  root : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ Real.exp P

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uX

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleResidueMixtureForecast
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

end Erdos3.FiniteProbabilityWeights

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

local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Short" => {a : LayerSamplerAxis I n // short a}
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "ActiveInput" => PrincipalTupleIndex activeB activeDegree
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides

noncomputable def allocatedPrincipalResidueJoin (q : ℕ) (u : ShortTuple)
    (r : ActiveInput → ZMod q) : FullInput → Option Empty → ZMod q :=
  principalAxisResidueJoin short u q (fun j _ => r j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]

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

local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "ActiveInput" => PrincipalTupleIndex activeB activeDegree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "sides" => allocatedPrincipalSides B U basis S

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Output" => (Σ _a : Active, Unit)
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "sides" => allocatedPrincipalSides B U basis S

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastInactiveAffineIntervalFixedResidueSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

noncomputable def forecastInactiveFixedOutput
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)) :
    A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ := fun a =>
  boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
    (allocatedPhysicalCubeDirections B U b S x y) ((selected a).1.val + 1)
    (fun t : (Finset.univ : Finset (Finset Empty)) => (t : Finset Empty)) *ᵥ c a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

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
variable (q : ℕ) [NeZero q]
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]

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
variable (q : ℕ) [NeZero q]
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ c j + (step j : ℤ) * t.val ∧
    c j + (step j : ℤ) * t.val < allocatedPrincipalSides B U basis S j)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable def allocatedForecastPolynomial
    (inactive : LayerSamplerAxis I n → Prop)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : Sigma (AllocatedCongruenceRankOutput X E inactive)) :
    MvPolynomial (LayerSamplerLongVariables inactive G B ⊕
      (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ :=
  allocatedSeparatedCongruencePolynomial inactive o.1 base noise r (projection o.1) o.2

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

end Erdos3.VectorPolynomial

end

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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides

noncomputable def allocatedShortPrincipalRaw (u : ShortTuple)
    (k : PrincipalTupleIndex B degree × Option Empty) : ℤ :=
  if hk : short k.1.1 then (u ⟨⟨k.1.1, hk⟩, k.1.2⟩ k.2 : ℤ) else 0

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V Short Out : Type*} [Fintype L] [Fintype V]
  [Fintype Out] [DecidableEq Out]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < (allocatedPrincipalSides B U basis S) j)
variable (hH : ∀ j, 0 < H j)

noncomputable def allocatedInactiveAffineIntervalLaw
    (H step : (PrincipalTupleIndex B (layerSamplerDegree I n)) → ℕ) (start : (PrincipalTupleIndex B (layerSamplerDegree I n)) → ℤ)
    (hinside : ∀ j (t : Fin (H j)),
      0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < (allocatedPrincipalSides B U basis S) j)
    (hH : ∀ j, 0 < H j) : FiniteProbabilityWeights (PrincipalAxisTuples (α := Empty) (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)) :=
  principalAffineIntervalAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside hH (allocatedShortAxis (I := I) U basis S.value)

variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)

variable {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
variable (active : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) → FiniteProbabilityWeights Ω) (Y : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) → Ω → Out → ℤ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "AI" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (deck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis short j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)

noncomputable def allocatedJointResidueOutput
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ) (rG : G → ZMod q)
    (r : FullInput → Option Empty → ZMod q) : Out → ZMod q :=
  fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
    (Sum.elim (Sum.elim rG (fun j : AI => r ⟨j.1.val, j.2⟩ none))
      (fun k => r k.1 k.2)) (allocatedForecastPolynomial short base noise deck projection o)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

variable (H parameterStep : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (parameterStep j : ℤ) * t.val ∧
    start j + (parameterStep j : ℤ) * t.val < allocatedPrincipalSides B U basis S j)
variable (hH : ∀ j, 0 < H j)

variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical
open BooleanCubeKernel

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

def allocatedOriginalSampleCongruenceProjection
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (j : Fin m) (a : AllocatedDegreeActiveAxis short j) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ :=
  match a.val with
  | .inl _ => fun _ => 0
  | .inr i => (sample j).2 i

noncomputable def allocatedOriginalSampleDeckValue
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides)
    (j : Fin m) (e : E j) : ℤ :=
  MvPolynomial.eval (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
    (modularBoundedCoefficientPolynomial (j.val + 1) (fun d => deck j d e))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteTriangularRationalCorrection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_triangular_correction_of_windows
    (B : ℝ) (hB : 0 ≤ B) (q W : ℕ)
    (hwindow : ∀ c : ℝ, ∃ S : Finset ℚ, S.card ≤ W ∧ ∀ r : ℚ,
      r ∈ S ↔ (∃ z : ℤ, r = (z : ℚ) / q) ∧ |(r : ℝ) - c| ≤ B) :
    ∀ n (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ),
      (∀ i j, i < j → A i j = 0) →
      (∀ i, A i i ≠ 0 ∧ |A i i| ≤ 1) →
      ∃ S : Finset ((Fin n → ℝ) × (Fin n → ℚ)), S.card ≤ W ^ n ∧
        ∀ sr, sr ∈ S ↔ sr ∈ triangularCorrectionSolutions A c B q := by
  classical
  choose window hcard hmem using hwindow
  intro n
  induction n with
  | zero =>
    intro A c htri hdiag
    let z : (Fin 0 → ℝ) × (Fin 0 → ℚ) := (0, 0)
    refine ⟨{z}, by simp, ?_⟩
    intro sr
    have he : sr = z := Subsingleton.elim _ _
    subst sr
    simp [triangularCorrectionSolutions]
  | succ n ih =>
    intro A c htri hdiag
    let A' : Matrix (Fin n) (Fin n) ℝ := fun i j => A i.castSucc j.castSucc
    let c' : Fin n → ℝ := fun i => c i.castSucc
    obtain ⟨S, hS, hSiff⟩ := ih A' c'
      (fun i j hij => htri i.castSucc j.castSucc hij) (fun i => hdiag i.castSucc)
    let center : ((Fin n → ℝ) × (Fin n → ℚ)) → ℝ :=
      fun u => c (Fin.last n) - ∑ j, A (Fin.last n) j.castSucc * u.1 j
    let extend : ((Fin n → ℝ) × (Fin n → ℚ)) → ℚ →
        ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)) := fun u r =>
      (Fin.snoc u.1 ((center u - (r : ℝ)) / A (Fin.last n) (Fin.last n)), Fin.snoc u.2 r)
    let all := S.biUnion (fun u => (window (center u)).image (extend u))
    let out := all.filter (fun sr => sr ∈ triangularCorrectionSolutions A c B q)
    have hallcard : all.card ≤ W ^ (n + 1) := by
      calc
        all.card ≤ ∑ u ∈ S, ((window (center u)).image (extend u)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ S, W := Finset.sum_le_sum
          (fun u _ => Finset.card_image_le.trans (hcard (center u)))
        _ = S.card * W := by simp
        _ ≤ W ^ n * W := Nat.mul_le_mul_right W hS
        _ = W ^ (n + 1) := (pow_succ W n).symm
    refine ⟨out, (Finset.card_filter_le _ _).trans hallcard, ?_⟩
    intro sr
    constructor
    · intro hs
      exact (Finset.mem_filter.mp hs).2
    · intro hsr
      apply Finset.mem_filter.mpr
      refine ⟨?_, hsr⟩
      let u : (Fin n → ℝ) × (Fin n → ℚ) :=
        (fun i => sr.1 i.castSucc, fun i => sr.2 i.castSucc)
      have hu : u ∈ S := (hSiff u).mpr
        (triangularCorrectionSolutions_prefix htri hsr)
      have hr : sr.2 (Fin.last n) ∈ window (center u) := by
        apply (hmem _ _).mpr
        refine ⟨hsr.2.1 (Fin.last n), ?_⟩
        exact triangularCorrectionSolutions_last_window hsr hB
          (hdiag (Fin.last n)).2
      apply Finset.mem_biUnion.mpr
      refine ⟨u, hu, Finset.mem_image.mpr ⟨sr.2 (Fin.last n), hr, ?_⟩⟩
      have hlast := triangularCorrectionSolutions_last_eq hsr
        (hdiag (Fin.last n)).1
      apply Prod.ext
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [extend, Fin.snoc_last, center, u] using hlast.symm
        · simp only [extend, Fin.snoc_castSucc, u]
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [extend, Fin.snoc_last]
        · simp only [extend, Fin.snoc_castSucc, u]

theorem exists_finite_triangular_rational_correction
    (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (htri : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ S : Finset ((Fin n → ℝ) × (Fin n → ℚ)),
      S.card ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ n ∧
      ∀ sr, sr ∈ S ↔ sr ∈ triangularCorrectionSolutions A c B q := by
  apply exists_finite_triangular_correction_of_windows B hB q
    (2 * ⌈(q : ℝ) * B⌉₊ + 3) ?_ n A c htri (fun i => ⟨hdiag i, hdiagBound i⟩)
  intro center
  obtain ⟨S, hS, hmem⟩ := exists_scalar_rational_grid_window q hq center B
  refine ⟨S, hS, ?_⟩
  intro r
  rw [hmem]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by exact_mod_cast hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by exact_mod_cast hz⟩

theorem exists_triangular_rational_correction_enumeration
    (q : ℕ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (htri : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0) (hdiagBound : ∀ i, |A i i| ≤ 1) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ n ∧
      ∃ candidate : Fin m → ((Fin n → ℝ) × (Fin n → ℚ)),
        (∀ j, candidate j ∈ triangularCorrectionSolutions A c B q) ∧
        ∀ sr, sr ∈ triangularCorrectionSolutions A c B q → ∃ j, candidate j = sr := by
  classical
  obtain ⟨S, hS, hmem⟩ := exists_finite_triangular_rational_correction q hq B hB
    n A c htri hdiag hdiagBound
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, ?_, fun j => (e.symm j).val, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hS
  · intro j
    exact (hmem _).mp (e.symm j).property
  · intro sr hsr
    let v : S := ⟨sr, (hmem sr).mpr hsr⟩
    exact ⟨e v, congrArg Subtype.val (e.symm_apply_apply v)⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MeasurableConstantCenterRepresentative
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem exists_measurable_coefficient_representative_of_layers
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    (hsection : ∀ j, ∃ r : (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) →
        euclideanSubspace (U j), Measurable r ∧
        ∀ x, QuotientAddGroup.mk' _ (r x) = x) :
    ∃ r : CoefficientTorus (K := K) U → CoefficientArray (K := K) U,
      Measurable r ∧ ∀ x, QuotientAddGroup.mk' (coefficientIntegerLattice U) (r x) = x := by
  classical
  choose r hr hright using hsection
  let f : CoefficientTorus (K := K) U → CoefficientArray (K := K) U :=
    fun x s => euclideanSubspaceArrayEquiv (U s.1)
      (r s.1 (euclideanCoefficientEquiv U x s.1 s.2)) ()
  refine ⟨f, ?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro s
    exact (measurable_pi_apply ()).comp
      ((euclideanSubspaceArrayEquiv (U s.1)).continuous.measurable.comp
        ((hr s.1).comp ((measurable_pi_apply s.2).comp
          ((measurable_pi_apply s.1).comp
            (euclideanCoefficientEquiv_continuous U).measurable))))
  · intro x
    apply coefficientCoordinateTorus_injective U
    funext s
    rw [coefficientCoordinateTorus_mk]
    have hunit : (fun _ : Unit => f x s) = euclideanSubspaceArrayEquiv (U s.1)
        (r s.1 (euclideanCoefficientEquiv U x s.1 s.2)) := by
      funext a
      cases a
      rfl
    rw [hunit, ← euclideanSubspaceTorusEquiv_mk, hright]
    exact (euclideanSubspaceTorusEquiv (U s.1)).apply_symm_apply _

theorem exists_measurable_subtractive_constant_center_of_representative
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := Empty) U)]
    [BorelSpace (CoefficientTorus (K := Empty) U)]
    (r : CoefficientTorus (K := Empty) U → CoefficientArray (K := Empty) U)
    (hr : Measurable r)
    (hright : ∀ x, QuotientAddGroup.mk' (coefficientIntegerLattice U) (r x) = x) :
    ∃ c : CoefficientTorus (K := K) U → ∀ j, U j, Measurable c ∧
      ∀ x, coefficientConstantCenter U x =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray (K := K) U (fun s => c x s.1))) := by
  let v : CoefficientTorus (K := K) U → CoefficientArray (K := Empty) U :=
    fun x => r (-(coefficientEvaluationTorus U 0 x))
  let c : CoefficientTorus (K := K) U → ∀ j, U j :=
    fun x j => v x ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩
  refine ⟨c, ?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply _).comp
      (hr.comp (coefficientEvaluationTorus_continuous U 0).neg.measurable)
  · intro x
    have hc : (fun s : CoefficientSlot Empty m => c x s.1) = v x := by
      funext s
      rcases s with ⟨j,d⟩
      rw [emptyCoefficientExponent_eq (j.val + 1) d]
    rw [← constantCoefficientTorusMap_mk, hc]
    change coefficientConstantCenter U x = -(constantCoefficientTorusMap U
      (QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (r (-(coefficientEvaluationTorus U 0 x)))))
    rw [hright, map_neg, neg_neg]
    rfl

theorem exists_measurable_subtractive_constant_center
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (bW : ∀ j, Basis (B j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    ∃ c : CoefficientTorus (K := K) U → ∀ j, U j, Measurable c ∧
      ∀ x, coefficientConstantCenter U x =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray (K := K) U (fun s => c x s.1))) := by
  let : MeasurableSpace (CoefficientTorus (K := Empty) U) := borel _
  let : BorelSpace (CoefficientTorus (K := Empty) U) := ⟨rfl⟩
  obtain ⟨r, hr, hright⟩ := exists_measurable_coefficient_representative_of_layers
    (K := Empty) U (fun j => lattice_exists_measurable_representative
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))) (bW j))
  exact exists_measurable_subtractive_constant_center_of_representative U r hr hright

end Erdos3.VectorPolynomial

end

end OAI

end


