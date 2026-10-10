-- Prove2me | Definitions.Def_OAIErdos3B136
-- name    : OAIErdos3B136
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T23:32:35.294991+00:00
-- url     : https://prove2.me/theorems/012be753-2901-4de1-ac57-5bcb18824321
-- title:
--   OpenAI Erdős-3 split, definitions bundle 137 of 177
-- statement:
--   Definitions bundle 137 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B135`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 137 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedAffineCoefficientComparison`, `OAI.Erdos3.VectorPolynomial.AllocatedAffineCoveredComparison`, `OAI.Erdos3.VectorPolynomial.AllocatedAffineReferenceComparison`, `OAI.Erdos3.VectorPolynomial.CoefficientChartResidues`, `OAI.Erdos3.VectorPolynomial.CoefficientDeckDensityLaw`, `OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetDensity`, `OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy`, `OAI.Erdos3.VectorPolynomial.allocatedAffinePartitionLog`, `OAI.Erdos3.VectorPolynomial.allocatedAffinePartitionRadiusLog`, `OAI.Erdos3.VectorPolynomial.allocatedAffineRadiusLog`, `OAI.Erdos3.VectorPolynomial.allocatedAffineSourceReferenceError`, `OAI.Erdos3.VectorPolynomial.allocatedAffineSourceTolerance`, `OAI.Erdos3.VectorPolynomial.allocatedAffineToleranceLog`, `OAI.Erdos3.VectorPolynomial.allocatedProgressionCoveredExpectation`, `OAI.Erdos3.VectorPolynomial.coefficientDeckResidueMask`, `OAI.Erdos3.VectorPolynomial.coefficientDeckResidueRead`, `OAI.Erdos3.VectorPolynomial.coefficientSamplerChartResidues`, `OAI.Erdos3.affineBooleanAxisWeightCost`, `OAI.Erdos3.affineBooleanAxisWeightLog`, `OAI.Erdos3.affineDerivativeAxisEnvelope`, `OAI.Erdos3.affineDerivativeAxisEnvelope_nonneg`, `OAI.Erdos3.affineInverseAxisEnvelope`, `OAI.Erdos3.affineInverseAxisEnvelope_nonneg`, `OAI.Erdos3.affineMinorConstantEnvelope`, `OAI.Erdos3.affineMinorConstantEnvelope_nonneg`, `OAI.Erdos3.affineMinorDegreeEnvelope`, `OAI.Erdos3.affineMinorDegreeEnvelope_nonneg`, `OAI.Erdos3.affineMinorLogEnvelope`, `OAI.Erdos3.affineMinorLogEnvelope_nonneg`, `OAI.Erdos3.affineMinorVariableEnvelope`, `OAI.Erdos3.affineMinorVariableEnvelope_nonneg`, `OAI.Erdos3.affineProfileCoefficientEnvelope`, `OAI.Erdos3.affineProfileInputEnvelope`, `OAI.Erdos3.affineProfileToleranceEnvelope`, `OAI.Erdos3.affineWeightAxisEnvelope`, `OAI.Erdos3.affineWeightAxisEnvelope_nonneg`, `OAI.Erdos3.canonicalAffineMinorLog`, `OAI.Erdos3.jointAffineBooleanWeightLog`, `OAI.Erdos3.jointAffineDerivativeEnvelope`, `OAI.Erdos3.jointAffineInverseEnvelope`, `OAI.Erdos3.jointAffineInverseLog`, `OAI.Erdos3.jointAffinePerturbationLog`, `OAI.Erdos3.jointAffineSourceEnvelope`, `OAI.Erdos3.jointAffineSourceEnvelope_nonneg`, `OAI.Erdos3.jointAffineSourceInputLog`, `OAI.Erdos3.jointAffineTranslationLog`, `OAI.Erdos3.jointAffineWeightEnvelope`, `OAI.Erdos3.normalizedDeckResidueRead`, `OAI.Erdos3.partitionedAffineSourceRadius`, `OAI.Erdos3.partitionedAffineSourceTolerance`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169
import Definitions.Def_OAIErdos3B176

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

noncomputable def canonicalAffineMinorLog (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) (P E F : ℝ) : ℝ :=
  canonicalBooleanMinorLog O α h P E +
    (cubeMinorVariableCount O α h * cubeMinorDegree O h : ℕ) *
      (cubeMinorVariableCount O α h : ℝ) * F

noncomputable def jointAffineInverseLog {D α : Type*} [Fintype D] [Fintype α]
    {O : D → Type*} [∀ d, Fintype (O d)] (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card D + ∑ d, (F + productMinorInverseLog (Fintype.card (O d)) (Fintype.card α) (h d) P
    (canonicalAffineMinorLog (O d) α (h d) P E F))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def affineBooleanAxisWeightLog (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) (P E F : ℝ) : ℝ :=
  (scalarCubeDerivativeLog (Fintype.card α) P+2*Fintype.card (B × Fin h)+E+1)+
  (Fintype.card (BlockParameter B (Fin h) α)+P+canonicalAffineMinorLog O α h P E F+
    productMinorDeterminantLog (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h P)+1

noncomputable def jointAffineBooleanWeightLog {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card D + ∑ d, affineBooleanAxisWeightLog (B d) (O d) α (h d) P E F

noncomputable def affineBooleanAxisWeightCost (B O α : Type*) [Fintype B] [Fintype O]
    [Fintype α] [DecidableEq α] (h : ℕ) (C : ℝ) (A T : ℝ≥0) (c₀ δ η : ℝ) : ℝ :=
  (∑ _i : B × Fin h, ((2*2^Fintype.card α : ℕ) : ℝ)*((Fintype.card α : ℝ)+1)^2*T/
    scalarCubeProductBoundaryRadius (B × Fin h) α (η/2))+
  (Fintype.card (BlockParameter B (Fin h) α) : ℝ)*
    ((A : ℝ)/canonicalAffineCubeMinorThreshold O α h c₀ δ η*
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C 1)

end Erdos3

end

section

namespace Erdos3

section Definitions
variable {A : Type*} [Semiring A]
def affineMinorVariableEnvelope (D : A) : A := D * (D * (D + 1))
def affineMinorDegreeEnvelope (D : A) : A := 1 + D * D
def affineMinorConstantEnvelope (D : A) : A :=
  D * D * (D + 1)^2 + 3 * affineMinorVariableEnvelope D +
    (affineMinorDegreeEnvelope D + 1) +
    affineMinorDegreeEnvelope D * (8 + (affineMinorDegreeEnvelope D + 1))
def affineMinorLogEnvelope (D P E F : A) : A :=
  affineMinorVariableEnvelope D * affineMinorDegreeEnvelope D + D * P + 2 +
    affineMinorVariableEnvelope D * affineMinorDegreeEnvelope D *
      (affineMinorConstantEnvelope D + 1 + E + 2) +
    affineMinorVariableEnvelope D * affineMinorDegreeEnvelope D * affineMinorVariableEnvelope D * F
end Definitions

 theorem affineMinorVariableEnvelope_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ affineMinorVariableEnvelope D := by unfold affineMinorVariableEnvelope; positivity
 theorem affineMinorDegreeEnvelope_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ affineMinorDegreeEnvelope D := by unfold affineMinorDegreeEnvelope; positivity
 theorem affineMinorConstantEnvelope_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ affineMinorConstantEnvelope D := by
  have := affineMinorVariableEnvelope_nonneg hD
  have := affineMinorDegreeEnvelope_nonneg hD
  unfold affineMinorConstantEnvelope
  positivity
 theorem affineMinorLogEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ affineMinorLogEnvelope D P E F := by
  have := affineMinorVariableEnvelope_nonneg hD
  have := affineMinorDegreeEnvelope_nonneg hD
  have := affineMinorConstantEnvelope_nonneg hD
  unfold affineMinorLogEnvelope
  positivity

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointAffineTranslationLog (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card (Σ d, O d) + Fintype.card (JointBlockParameter B h α) +
    3 * jointAffineInverseLog (O := O) (α := α) h P E F +
    jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P +
    jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F + 1

noncomputable def jointAffinePerturbationLog (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card (JointBlockParameter B h α) +
    3 * jointAffineInverseLog (O := O) (α := α) h P E F +
    jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P +
    jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F + 6

end Erdos3

end

section

namespace Erdos3

section Definitions
variable {A : Type*} [Semiring A]
def affineInverseAxisEnvelope (D P E F : A) : A :=
  F + (D + D^2 + D * (P + D + D * D) + affineMinorLogEnvelope D P E F)

def affineDerivativeAxisEnvelope (D P : A) : A :=
  affineMinorVariableEnvelope D + D + (P + 2 * D + D * D)

def affineWeightAxisEnvelope (D P E F : A) : A :=
  (P + 3 * D + 1 + ((D + 1)^2 + 2 * D + 2) + 2 * (D * D) + E + 1) +
    (affineMinorVariableEnvelope D + P + affineMinorLogEnvelope D P E F +
      (affineMinorVariableEnvelope D + D^2 + D + (P + 2 * D + D * D) +
        D * (P + D + D * D + 1))) + 1
end Definitions

 theorem affineInverseAxisEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ affineInverseAxisEnvelope D P E F := by
  have := affineMinorLogEnvelope_nonneg hD hP hE hF
  unfold affineInverseAxisEnvelope
  positivity
 theorem affineDerivativeAxisEnvelope_nonneg {D P : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) :
    0 ≤ affineDerivativeAxisEnvelope D P := by
  have := affineMinorVariableEnvelope_nonneg hD
  unfold affineDerivativeAxisEnvelope
  positivity
 theorem affineWeightAxisEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ affineWeightAxisEnvelope D P E F := by
  have := affineMinorLogEnvelope_nonneg hD hP hE hF
  have := affineMinorVariableEnvelope_nonneg hD
  unfold affineWeightAxisEnvelope
  positivity

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

noncomputable def jointAffineSourceInputLog (h : D → ℕ) (P E F : ℝ) : ℝ :=
  jointAffineTranslationLog (B := B) (O := O) (α := α) h P E F +
    jointAffinePerturbationLog (B := B) (O := O) (α := α) h P E F +
    jointAffineInverseLog (O := O) (α := α) h P E F + Fintype.card (Σ d, O d) + E + 4

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D α Z : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [Fintype Z] [DecidableEq Z]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

section Definitions
variable {A : Type*} [Semiring A]
def jointAffineInverseEnvelope (D P E F : A) : A := D + D * affineInverseAxisEnvelope D P E F
def jointAffineDerivativeEnvelope (D P : A) : A := D + D * affineDerivativeAxisEnvelope D P
def jointAffineWeightEnvelope (D P E F : A) : A := D + D * affineWeightAxisEnvelope D P E F
def jointAffineSourceEnvelope (D P E F : A) : A :=
  let out := D * D
  let param := D * affineMinorVariableEnvelope D
  let inv := jointAffineInverseEnvelope D P E F
  let deriv := jointAffineDerivativeEnvelope D P
  let weight := jointAffineWeightEnvelope D P E F
  (out + param + 3 * inv + deriv + weight + 1) +
    (param + 3 * inv + deriv + weight + 6) + inv + out + E + 4
end Definitions

variable {ι α : Type*} [Fintype ι] [Fintype α]
  {B O : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (O i)]

 theorem jointAffineSourceEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ jointAffineSourceEnvelope D P E F := by
  have := affineMinorVariableEnvelope_nonneg hD
  have := affineInverseAxisEnvelope_nonneg hD hP hE hF
  have := affineDerivativeAxisEnvelope_nonneg hD hP
  have := affineWeightAxisEnvelope_nonneg hD hP hE hF
  unfold jointAffineSourceEnvelope jointAffineInverseEnvelope jointAffineDerivativeEnvelope jointAffineWeightEnvelope
  positivity

end Erdos3

end

section

namespace Erdos3
open scoped NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]

noncomputable def partitionedAffineSourceRadius (A T : ℝ≥0) (δ E : ℝ) : ℝ :=
  jointAffineSourceRadius (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
    (fun d => h d.val) (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val) A T δ E

noncomputable def partitionedAffineSourceTolerance (A T : ℝ≥0) (degree : ℕ) (δ E : ℝ) : ℝ :=
  jointAffineCoefficientTolerance (Z := PartitionedProfileNoiseIndex G Z α B h P)
    (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
    (fun d => h d.val) (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val) A T degree 1 1 δ E

end Erdos3

end

section

namespace Erdos3
open scoped NNReal BigOperators Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

section Definitions
variable {A : Type*} [Semiring A]
def affineProfileCoefficientEnvelope (D A₀ T₀ : A) : A := D * D + A₀ + T₀ + 7
def affineProfileInputEnvelope (D A₀ T₀ E F : A) : A :=
  jointAffineSourceEnvelope D (affineProfileCoefficientEnvelope D A₀ T₀) (E + D + 4) F

def affineProfileToleranceEnvelope (degree : ℕ) (D N A₀ T₀ E F : A) : A :=
  16 + 6 * affineProfileInputEnvelope D A₀ T₀ E F +
    (3 * N * (degree + 2 : ℕ) +
      (2 * (D + affineProfileCoefficientEnvelope D A₀ T₀ + degree * D) + 1)) + 1
end Definitions

variable {ι G Z α : Type*} [Fintype ι] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B O : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (O i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRadiusLog
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

noncomputable def allocatedAffineLongJetDensity (y : activeInput → ℝ) : (realOutput → ℝ) → ℝ := by
  exact allocatedNormalizedLongJetDensity B U basis S x u rows s hA (fun i => center i + width i * y i)

noncomputable def allocatedAffineLongJetProxy : (realOutput → ℝ) → ℝ :=
  densityMixture (jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))
    (allocatedAffineLongJetDensity B U basis S x u rows s hA center width)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

noncomputable def allocatedAffineSourceTolerance (A T : ℝ≥0) (δ ε : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun P : LayerSamplerAxis I n → Prop =>
    partitionedAffineSourceTolerance (G := G) (Z := G × Option α) (B := B)
      (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T m δ ε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

noncomputable def allocatedAffinePartitionLog (A T : ℝ≥0) (E F : ℝ)
    (P : LayerSamplerAxis I n → Prop) : ℝ :=
  let Clog := unitProfileCoefficientLog (B := B) A T
  let Elog := E + Fintype.card {a // ¬P a} + 4
  let Qlog := jointAffineSourceInputLog (B := fun a : {a // ¬P a} => B a.val)
    (O := fun a : {a // ¬P a} => O a.val.1) (α := α)
    (fun a => layerSamplerDegree I n a.val) Clog Elog F
  Real.log 16 + 6 * Qlog +
    booleanToleranceC2Log (B := fun a : {a // ¬P a} => B a.val) (α := α)
      (PartitionedProfileNoiseIndex G (G × Option α) α B (layerSamplerDegree I n) P)
      (fun a => layerSamplerDegree I n a.val) m Clog + 1

noncomputable def allocatedAffineToleranceLog (A T : ℝ≥0) (E F : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (allocatedAffinePartitionLog (G := G) (O := O) (α := α) B A T E F)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

noncomputable def allocatedAffinePartitionRadiusLog (A T : ℝ≥0) (E F : ℝ)
    (P : LayerSamplerAxis I n → Prop) : ℝ :=
  2 * jointAffineSourceInputLog (B := fun a : {a // ¬P a} => B a.val)
    (O := fun a : {a // ¬P a} => O a.val.1) (α := α)
    (fun a => layerSamplerDegree I n a.val) (unitProfileCoefficientLog (B := B) A T)
    (E + Fintype.card {a // ¬P a} + 4) F + 2

noncomputable def allocatedAffineRadiusLog (A T : ℝ≥0) (E F : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (allocatedAffinePartitionRadiusLog (O := O) (α := α) B A T E F)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedProgressionDensityIdentity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] in
def CoefficientDeckDensityLaw
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d] : Prop :=
    (source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
      (fun x : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
        canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2) =
      realDensityMeasure μ (fun y => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => (∫ p, FiniteProbabilityWeights.complexMean wholeLaw (fun y =>
  F (Prod.fst ((allocatedCoefficientSplit B U basis S) (Prod.fst p)),
    euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
      (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
  ∂(Measure.prod source (PMF.toMeasure deck)))

noncomputable def allocatedProgressionCoveredExpectation : ℂ := actual

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineWholeProfileComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (α : Type*) [Fintype α] [DecidableEq α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedAffineSourceReferenceError (ρ : ℝ≥0) (P η : ℝ)
    (M H : PrincipalTupleIndex
      (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val)
      (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) → ℕ)
    (ε mesh Cmask : ℝ) : ℝ :=
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
      let cap := bound ^ Fintype.card (LayerSamplerAxis I n)
      let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
      let sourceError := η +
        ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
          (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
          (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1)
      let radius := max (Real.exp P * (partitionedIdealRadius α m + 1)) (Real.exp (allocatedJetSupportLog (G := G) B α O P))
      let Ki : ℝ≥0 := ‖(∏ o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1), |R o.1.val.1|)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) ρ * ⟨Real.exp P, Real.exp_nonneg _⟩)
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
          (sourceError + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
            ((2 * radius + 2) ^ Fintype.card {o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) // allocatedLongIntegerCoordinate B U basis S (O := O) o} *
              ((Ki : ℝ) + lip) * mesh))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (α : Type*) [Fintype α] [DecidableEq α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

def AllocatedAffineReferenceComparison
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) : Prop :=
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      ∀ (L step H M : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
        (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
        (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (outputModulus : ℕ)
        (outputResidue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod outputModulus))
        {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j outputModulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j outputModulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let discrete := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
          (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      (∫ z, |allocatedLongProfileDensity B U basis S x rows outputModulus outputResidue ideal z -
          allocatedLongProfileDensity B U basis S x rows outputModulus outputResidue discrete z|
        ∂allocatedLongJetReference B U basis S O) ≤
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η M H ε mesh Cmask

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

def AllocatedAffineCoefficientComparison
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1) : Prop :=
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (hq : Fintype.card α ≤ m + 1)
        {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
        (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
        (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (hv₀ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA
            (fun j => (hσsmall j).trans htone) z) -
          allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z|
        ∂allocatedLongJetReference B U basis S O) ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

def AllocatedAffineCoveredComparison
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (_ : t ≤ 1) : Prop :=
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (hq : Fintype.card α ≤ m + 1)
        {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
        (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
        (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (hv₀ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      ∀ (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
        (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)
        (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1),
      ‖(∫ p, law.complexMean (fun v => F (((allocatedCoefficientSplit B U basis S) p.1).1,
          euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v))
            (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v)) rows
            (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
          ∂(allocatedCoefficientSource B U basis hR hσ S).prod
            (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).toMeasure) -
        ∫ a₀, ∫ z, (allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z : ℂ) *
          allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d F a₀ z
          ∂allocatedLongJetReference B U basis S O ∂allocatedFrozenCoefficientSource B U basis hR hσ S‖ ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => O

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => O

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : EuclideanJetLayers U O → ℂ)

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientDeckResidueMask
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (q : ℕ) [NeZero q]

noncomputable def normalizedDeckResidueRead (a : D → ZMod q) : Fin n ⊕ I → ZMod q :=
  integerResidueMatrix (Classical.choose (standardLatticeCoordinates_residue W bW b hb q)) q
    *ᵥ (-a)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

abbrev CoefficientChartResidues (K : Type*) {m : ℕ} (n : Fin m → ℕ) (E : Fin m → Type*) (q : ℕ) :=
  ∀ j, BoundedCoefficientExponent K (j.val + 1) → (Fin (n j) ⊕ E j) → ZMod q

noncomputable def coefficientDeckResidueRead (q : ℕ) [NeZero q]
    (a : CoefficientAmbientIndex K J → ZMod q) : CoefficientChartResidues K n E q :=
  fun j e => normalizedDeckResidueRead (euclideanSubspace (U j)) (bW j) (b j) (hb j) q
    (fun i => a ⟨⟨j, e⟩, i⟩)

def coefficientSamplerChartResidues (q : ℕ)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) E q) :
    CoefficientChartResidues K n E q :=
  fun j e => Sum.elim (fun i => ((x j).2 i e : ZMod q)) (r j e)

noncomputable def coefficientDeckResidueMask (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues K n E q → ℝ) :
    (CoefficientAmbientIndex K J → ZMod q) → ℝ :=
  fun a => test (coefficientDeckResidueRead U bW b hb q a)

end Erdos3.VectorPolynomial

end

end OAI

end


