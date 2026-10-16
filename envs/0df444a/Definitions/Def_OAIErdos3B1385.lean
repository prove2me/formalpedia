-- Prove2me | Definitions.Def_OAIErdos3B1385
-- name    : OAIErdos3B1385
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T04:51:27.495561+00:00
-- url     : https://prove2.me/theorems/c39fce01-a17a-41f4-9455-3486e2ee06bc
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1386 of 1398
-- statement:
--   Definitions bundle 1386 of 1398 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1384`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1386 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedComparisonDimensions.active_outputs`, `OAI.Erdos3.VectorPolynomial.AllocatedComparisonDimensions.kernel_coefficients`, `OAI.Erdos3.VectorPolynomial.AllocatedComparisonDimensions.nonkernel_coefficients`, `OAI.Erdos3.VectorPolynomial.allocatedAffineL1_primitive_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedDensityLog_le_envelope`, `OAI.Erdos3.VectorPolynomial.allocatedJetSupportLog_le_envelope`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceLip_coe_le_two`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceLip_le_two`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceLip_le_two_exp_of_allAxis`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleLiftInput_card_le_allAxis`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleLiftLip_coe_le_allAxis`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleLiftLip_eq_card`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleLiftLip_le_exp_of_allAxis`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleLiftLip_le_fullInputCount`, `OAI.Erdos3.VectorPolynomial.allocatedProfile_dimensions`, `OAI.Erdos3.VectorPolynomial.allocatedUnitProfilePrincipalLowerBound_inv_le_exp`, `OAI.Erdos3.affineReferenceCoefficient_bounds`, `OAI.Erdos3.affineReferenceError_accuracy_separated`, `OAI.Erdos3.affineSourceAccuracy_budget`, `OAI.Erdos3.diagonalProfileLip_le_exp`, `OAI.Erdos3.exp_neg_le_half_exp_neg`, `OAI.Erdos3.inverseProduct_norm_le_exp`, `OAI.Erdos3.kernelGeometryLog_le_envelope`, `OAI.Erdos3.kernelInverseLog_le_envelope`, `OAI.Erdos3.kernelRowOutputLog_le_envelope`, `OAI.Erdos3.principalBlock_card_le_input_card`, `OAI.Erdos3.slicedEndpointUniformScale_inverse_le_exp`, `OAI.Erdos3.slicedPrincipalBoundaryRadius_inverse_le_exp`, `OAI.Erdos3.slicedPrincipalComparisonBudget_le_exp`, `OAI.Erdos3.slicedPrincipalMinor_inverse_le_exp`, `OAI.Erdos3.slicedSourceAccuracy_bounds`, `OAI.Erdos3.unitProfilePrincipalLowerBound_inv_le_exp`, `OAI.Erdos3.unitProfilePrincipalLowerBound_inv_le_exp_of_input_card`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1384

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScalarEnvelope
namespace OAI

section

namespace Erdos3

theorem kernelInverseLog_le_envelope {q n j d : ℕ} {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : (q : ℝ) ≤ D) (hn : (n : ℝ) ≤ D)
    (hj : (j : ℝ) ≤ D) (hd : (d : ℝ) ≤ D) :
    kernelInverseLog q n j d p ≤ kernelInverseEnvelope D p := by
  have hj' : ((j-1 : ℕ) : ℝ) ≤ D := (Nat.cast_le.mpr (Nat.sub_le j 1)).trans hj
  unfold kernelInverseLog kernelInverseEnvelope
  gcongr

theorem kernelGeometryLog_le_envelope {q n j k d : ℕ} {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : (q : ℝ) ≤ D) (hn : (n : ℝ) ≤ D)
    (hj : (j : ℝ) ≤ D) (hk : (k : ℝ) ≤ D) (hd : (d : ℝ) ≤ D) :
    kernelGeometryLog q n j k d p ≤ kernelGeometryEnvelope D p := by
  have hi := kernelInverseLog_le_envelope hD hp hq hn hj hd
  unfold kernelGeometryLog kernelGeometryEnvelope
  gcongr

theorem kernelRowOutputLog_le_envelope {q n j k u d : ℕ} {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : (q : ℝ) ≤ D) (hn : (n : ℝ) ≤ D)
    (hj : (j : ℝ) ≤ D) (hk : (k : ℝ) ≤ D) (hu : (u : ℝ) ≤ D)
    (hd : (d : ℝ) ≤ D) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D) :
    kernelRowOutputLog q n j k u d p ≤ kernelOutputEnvelope D p := by
  have hG := kernelGeometryLog_le_envelope hD hp hq hn hj hk hd
  have hG0 := (kernelGeometryLog_bounds q n j k d hp).1
  have hGe := kernelGeometryEnvelope_nonneg hD hp
  dsimp only [kernelRowOutputLog, kernelOutputEnvelope, affineProfileLogBound, jetOutputRadiusLog]
  gcongr

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)] {D : ℝ}

theorem AllocatedComparisonDimensions.kernel_coefficients
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    (Fintype.card (BoundedIntegerExponent G (j.val+1)) : ℝ) ≤ D := by
  have hc := Fintype.card_congr (allocatedKernelCoefficientEquiv (G := G) B j)
  rw [Fintype.card_sum] at hc
  exact (Nat.cast_le.mpr (by omega)).trans (h.coefficients j)

theorem AllocatedComparisonDimensions.nonkernel_coefficients
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) : ℝ) ≤ D := by
  have hc := Fintype.card_congr (allocatedKernelCoefficientEquiv (G := G) B j)
  rw [Fintype.card_sum] at hc
  exact (Nat.cast_le.mpr (by omega)).trans (h.coefficients j)

section Envelopes

variable {A : Type*} [Semiring A]

end Envelopes

variable (h : AllocatedComparisonDimensions (G := G) B α O D) {p e : ℝ} (hp : 0 ≤ p)

include h hp

theorem allocatedDensityLog_le_envelope :
    allocatedDensityLog (G := G) B α O p ≤ allocatedDensityEnvelope m D p := by
  have hD := h.nonneg
  have ht : 0 ≤ 4*(p+8) := by positivity
  have hk (j : Fin m) := kernelRowOutputLog_le_envelope h.nonneg ht h.cube h.kernel_variables
    (h.rows j) (h.kernel_coefficients B j) (h.nonkernel_coefficients B j)
    (h.layer_degree B j) h.profile
  have hsum : (∑ j : Fin m, kernelRowOutputLog (Fintype.card α) (Fintype.card G)
      (Fintype.card (O j)) (Fintype.card (BoundedIntegerExponent G (j.val+1)))
      (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j)) (j.val+1) (4*(p+8))) ≤
      (m : ℝ)*kernelOutputEnvelope D (4*(p+8)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hk j)
  have hc (j : Fin m) : allocatedDensityColumnLog (G := G) B α j ≤ D+3*D*D+D*(D+1) := by
    have hd := h.layer_degree B j
    have hn := h.nonkernel_coefficients B j
    have hparam := h.parameters
    have hq := h.cube
    have hplus : (j.val : ℝ)+2 ≤ D+1 := by
      push_cast at hd
      linarith
    unfold allocatedDensityColumnLog
    push_cast at hd ⊢
    gcongr
  have hcols : (∑ j : Fin m, allocatedDensityColumnLog (G := G) B α j) ≤
      (m : ℝ)*(D+3*D*D+D*(D+1)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hc j)
  unfold allocatedDensityLog allocatedDensityEnvelope kernelFamilyOutputLog
  linarith

theorem allocatedJetSupportLog_le_envelope :
    allocatedJetSupportLog (G := G) B α O p ≤ allocatedSupportEnvelope m D p := by
  have hD := h.nonneg
  have hden := allocatedDensityLog_le_envelope B h hp
  have hc (j : Fin m) :
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1) ≤ D+D*(D+1) := by
    have hd := h.layer_degree B j
    have hn := h.coefficients j
    have hq := h.cube
    gcongr
  have hs : (∑ j : Fin m,
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1))) ≤ (m : ℝ)*(D+D*(D+1)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hc j)
  unfold allocatedJetSupportLog allocatedSupportEnvelope
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, IsEmpty (I j)]
variable {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include U b o

theorem allocatedProfile_dimensions
    {G : Type*} [Fintype G] (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D : ℝ} (hd : AllocatedComparisonDimensions (G := G) B α O D)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    (∀ j, (Fintype.card (J j) : ℝ) ≤ D) ∧ (∀ j, (Fintype.card (Q j) : ℝ) ≤ D) := by
  have hJ (j) : (Fintype.card (J j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U b o j)).trans hd.axes
  exact ⟨hJ, fun j => (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans (hJ j)⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z]
  [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  (sets : ∀ d : {d // ¬P d}, O d.val → Finset α)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
  (R : D → ℝ) (hR : ∀ d, 0 < R d)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {D G α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
  (Z : Type*) {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
  (R : D → ℝ) (hR : ∀ d, 0 < R d)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem inverseProduct_norm_le_exp {Q : Type*} [Fintype Q]
    (R : Q → ℝ) (hR : ∀ q, 0 ≤ R q) {p : ℝ}
    (hRi : ∀ q, (R q)⁻¹ ≤ Real.exp p) :
    ‖(∏ q, R q)⁻¹‖ ≤ Real.exp ((Fintype.card Q : ℝ) * p) := by
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => hR q))),
    ← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ _q : Q, Real.exp p :=
      Finset.prod_le_prod (fun q _ => inv_nonneg.mpr (hR q)) (fun q _ => hRi q)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]

theorem diagonalProfileLip_le_exp {Q : Type*} [Fintype Q]
    (R : Q → ℝ) (hR : ∀ q, 0 ≤ R q) {D p e : ℝ} {δ : ℝ≥0}
    (hp : 0 ≤ p) (he : 0 ≤ e)
    (hcard : (Fintype.card Q : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D)
    (hRi : ∀ q, (R q)⁻¹ ≤ Real.exp p) (hδ : (δ : ℝ)⁻¹ ≤ Real.exp e) :
    (‖(∏ q, R q)⁻¹‖₊ *
      (affineProductProfileLip Q δ * NNReal.mk (Real.exp p) (Real.exp_pos p).le) : ℝ≥0) ≤
      Real.exp (D * p + 2 * D + (D + 1) * e + p) := by
  have hJ : ‖(∏ q, R q)⁻¹‖ ≤ Real.exp (D * p) :=
    (inverseProduct_norm_le_exp R hR hRi).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard hp))
  have hL : (affineProductProfileLip Q δ : ℝ) ≤ Real.exp (2 * D + (D + 1) * e) := by
    apply (affineProductProfileLip_le_exp Q hδ).trans
    apply Real.exp_le_exp.mpr
    unfold affineProfileLogBound
    nlinarith
  simp only [NNReal.coe_mul, NNReal.coe_mk, coe_nnnorm]
  calc
    _ ≤ Real.exp (D * p) * (Real.exp (2 * D + (D + 1) * e) * Real.exp p) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealRefinedPointwise
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)

include h

theorem AllocatedComparisonDimensions.active_outputs
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    (Fintype.card (Σ a : {a // ¬P a}, O a.val.1) : ℝ) ≤ D := by
  let emb : (Σ a : {a // ¬P a}, O a.val.1) ↪ (Σ a : LayerSamplerAxis I n, O a.1) :=
    Function.Embedding.sigmaMap (Function.Embedding.subtype (fun a => ¬P a))
      (fun a => Function.Embedding.refl (O a.val.1))
  have hc := Fintype.card_le_of_embedding emb
  exact (Nat.cast_le.mpr hc).trans h.outputs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D p e w E : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)
variable (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E)

include h hp he hw hE

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable {D p e w E : ℝ}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy
namespace OAI

section

namespace Erdos3

theorem exp_neg_le_half_exp_neg {A B : ℝ} (hAB : B + 1 ≤ A) :
    Real.exp (-A) ≤ (1 / 2) * Real.exp (-B) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (-(B + 1)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 1 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-B) / 2 := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h2
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

theorem slicedSourceAccuracy_bounds {Q G E : ℝ} (hQ : 0 ≤ Q) (hG : 0 ≤ G) (hE : 0 ≤ E) :
    let εgrid := Real.exp (-(Q + E + 1))
    let εlong := Real.exp (-(G + E + 1))
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Q + E + 1) ∧
    0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ = Real.exp (G + E + 1) ∧
    ∀ C : ℝ, C ≤ Real.exp G → Real.exp Q * εgrid + εlong * C ≤ Real.exp (-E) := by
  intro εgrid εlong
  have hg : εgrid ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hQ, hE])
  have hl : εlong ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hG, hE])
  refine ⟨Real.exp_pos _, hg, ?_, Real.exp_pos _, hl, ?_, ?_⟩
  · simp only [εgrid, Real.exp_neg, inv_inv]
  · simp only [εlong, Real.exp_neg, inv_inv]
  · intro C hC
    have hhalf := exp_neg_le_half_exp_neg (A := E + 1) (B := E) le_rfl
    have hgrid : Real.exp Q * εgrid = Real.exp (-(E + 1)) := by
      dsimp [εgrid]
      rw [← Real.exp_add]
      congr 1
      ring
    have hlong : εlong * Real.exp G = Real.exp (-(E + 1)) := by
      dsimp [εlong]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Real.exp Q * εgrid + εlong * Real.exp G :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hC (Real.exp_nonneg _))
      _ = 2 * Real.exp (-(E + 1)) := by rw [hgrid, hlong]; ring
      _ ≤ Real.exp (-E) := by linarith only [hhalf]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSourceAccuracy
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

theorem affineSourceAccuracy_budget
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Dout Dgrid Prho Pbox Op E F C : ℝ}
    (hDout : 0 ≤ Dout) (hDgrid : 0 ≤ Dgrid) (hPrho : 0 ≤ Prho)
    (hPbox : 0 ≤ Pbox) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hout : (Fintype.card κ : ℝ) ≤ Dout) (hgrid : (Fintype.card ι : ℝ) ≤ Dgrid)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hC0 : 0 ≤ C) (hC : C ≤ Real.exp F) :
    let G := Dgrid * max Op 0
    let εgrid := Real.exp (-(Dout * Prho + (E + F) + 1))
    let εlong := Real.exp (-(G + (E + F) + 1))
    let Plong := Pbox + Prho + G + (E + F) + 2
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Dout * Prho + (E + F) + 1) ∧
      0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp Plong ∧
      0 ≤ Plong ∧ Pbox ≤ Plong ∧ (ρ : ℝ)⁻¹ ≤ Real.exp Plong ∧
      C * ((ρ⁻¹ ^ Fintype.card κ : ℝ≥0) * εgrid +
        εlong * ∏ _i : ι, Real.exp Op) ≤ Real.exp (-E) := by
  intro G εgrid εlong Plong
  have hG : 0 ≤ G := mul_nonneg hDgrid (le_max_right _ _)
  obtain ⟨hg0, hg1, hgi, hl0, hl1, hli, herr⟩ :=
    slicedSourceAccuracy_bounds (mul_nonneg hDout hPrho) hG (add_nonneg hE hF)
  have hPlong : G + (E + F) + 1 ≤ Plong := by dsimp [Plong]; linarith
  have hb : Pbox ≤ Plong := by dsimp [Plong]; linarith
  have hr : Prho ≤ Plong := by dsimp [Plong]; linarith
  have hcap : (ρ⁻¹ ^ Fintype.card κ : ℝ≥0) ≤ Real.exp (Dout * Prho) := by
    rw [NNReal.coe_pow, NNReal.coe_inv]
    calc
      _ ≤ (Real.exp Prho) ^ Fintype.card κ := pow_le_pow_left₀ (inv_nonneg.mpr ρ.coe_nonneg) hρ _
      _ = Real.exp (Fintype.card κ * Prho) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hout hPrho)
  have hprod : (∏ _i : ι, Real.exp Op) ≤ Real.exp G := by
    simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hgrid (le_max_right _ _))
  refine ⟨hg0, hg1, hgi, hl0, hl1, hli.trans_le (Real.exp_le_exp.mpr hPlong),
    hPbox.trans hb, hb, hρ.trans (Real.exp_le_exp.mpr hr), ?_⟩
  calc
    _ ≤ C * (Real.exp (Dout * Prho) * εgrid + εlong * ∏ _i : ι, Real.exp Op) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact add_le_add (mul_le_mul_of_nonneg_right hcap hg0.le) le_rfl
    _ ≤ C * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_left (herr _ hprod) hC0
    _ ≤ Real.exp F * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3

theorem affineReferenceCoefficient_bounds
    {D L dlog slog P ideal Ki Cmask boundary : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hdlog : dlog ≤ L) (hslog : slog ≤ L) (hP : P ≤ L)
    (hideal : ideal ≤ Real.exp L) (hKi : Ki ≤ Real.exp L)
    (hCmask0 : 0 ≤ Cmask) (hCmask : Cmask ≤ Real.exp L)
    (hb0 : 0 ≤ boundary) (hb : boundary ≤ Real.exp L)
    (axes output unselected integer : ℕ)
    (ha : (axes : ℝ) ≤ D) (ho : (output : ℝ) ≤ D)
    (hu : (unselected : ℝ) ≤ D) (hi : (integer : ℝ) ≤ D) :
    let cap := (Real.exp dlog) ^ axes
    let lip := (axes : ℝ) * Real.exp dlog * cap
    let radius := max (Real.exp P * ideal) (Real.exp slog)
    let mask := Cmask ^ axes
    let support := (2 * Real.exp slog) ^ output
    let Q := affineReferenceCoefficientLog D L
    mask ≤ Real.exp Q ∧
    mask * (2 * cap * boundary + lip * 2) * support ≤ Real.exp Q ∧
    mask * lip * support ≤ Real.exp Q ∧
    mask * (2 * radius) ^ unselected * ((2 * radius + 2) ^ integer * (Ki + lip)) ≤ Real.exp Q := by
  intro cap lip radius mask support Q
  have hDL : 0 ≤ D * L := mul_nonneg hD hL
  have hcap : cap ≤ Real.exp (D * L) :=
    pow_le_exp_mul_of_le_exp (Real.exp_pos _).le (Real.exp_le_exp.mpr hdlog) hL axes ha
  have hm : mask ≤ Real.exp (D * L) :=
    pow_le_exp_mul_of_le_exp hCmask0 hCmask hL axes ha
  have haxes : (axes : ℝ) ≤ Real.exp D := ha.trans (by linarith [Real.add_one_le_exp D])
  have hlip : lip ≤ Real.exp (D + L + D * L) := by
    calc
      _ ≤ Real.exp D * Real.exp L * Real.exp (D * L) := by dsimp [lip, cap]; gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hrad : radius ≤ Real.exp (2 * L) := by
    apply max_le
    · calc
        _ ≤ Real.exp P * Real.exp L := mul_le_mul_of_nonneg_left hideal (Real.exp_pos _).le
        _ ≤ Real.exp L * Real.exp L := by gcongr
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    · exact Real.exp_le_exp.mpr (by linarith)
  have hrad0 : 0 ≤ radius := (Real.exp_pos slog).le.trans (le_max_right _ _)
  have hsuppBase : 2 * Real.exp slog ≤ Real.exp (L + 2) := by
    calc
      _ ≤ Real.exp L * Real.exp 2 := by rw [mul_comm 2]; gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hsupp : support ≤ Real.exp (D * (L + 2)) :=
    pow_le_exp_mul_of_le_exp (by positivity) hsuppBase (by positivity) output ho
  have hradBase : 2 * radius ≤ Real.exp (2 * L + 2) := by
    calc
      _ ≤ Real.exp (2 * L) * Real.exp 2 := by rw [mul_comm 2]; gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hradPlus : 2 * radius + 2 ≤ Real.exp (2 * L + 4) := by
    have h1 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp_iff.mpr (by positivity)
    calc
      _ ≤ 4 * Real.exp (2 * L) := by linarith only [hrad, h1]
      _ ≤ Real.exp (2 * L) * Real.exp 4 := by nlinarith [Real.exp_pos (2 * L)]
      _ = _ := (Real.exp_add _ _).symm
  have hru := pow_le_exp_mul_of_le_exp (mul_nonneg (by norm_num) hrad0) hradBase
    (by positivity : 0 ≤ 2 * L + 2) unselected hu
  have hri := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * radius + 2) hradPlus
    (by positivity : 0 ≤ 2 * L + 4) integer hi
  have hbl : 2 * cap * boundary ≤ Real.exp (D * L + L + 2) := by
    calc
      _ ≤ Real.exp (D * L) * Real.exp L * Real.exp 2 := by
        rw [show 2 * cap * boundary = cap * boundary * 2 by ring]
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hll : lip * 2 ≤ Real.exp (D + L + D * L + 2) := by
    calc
      _ ≤ Real.exp (D + L + D * L) * Real.exp 2 := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hboundary := add_le_exp_add_one (by positivity : 0 ≤ D * L + L + 2)
    (by positivity : 0 ≤ D + L + D * L + 2) hbl hll
  have hsum := add_le_exp_add_one hL (by positivity : 0 ≤ D + L + D * L) hKi hlip
  have hlog₀ : D * L ≤ Q := by dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  have hlog₁ : D * L + ((D * L + L + 2) + (D + L + D * L + 2) + 1) + D * (L + 2) ≤ Q := by
    dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  have hlog₂ : D * L + (D + L + D * L) + D * (L + 2) ≤ Q := by
    dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  have hlog₃ : D * L + D * (2 * L + 2) +
      (D * (2 * L + 4) + (L + (D + L + D * L) + 1)) ≤ Q := by
    dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  refine ⟨hm.trans (Real.exp_le_exp.mpr hlog₀), ?_, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (D * L) * Real.exp ((D * L + L + 2) + (D + L + D * L + 2) + 1) *
          Real.exp (D * (L + 2)) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr hlog₁
  · calc
      _ ≤ Real.exp (D * L) * Real.exp (D + L + D * L) * Real.exp (D * (L + 2)) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr hlog₂
  · by_cases hneg : Ki + lip < 0
    · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le)).trans (Real.exp_pos Q).le
    · have hsum0 := le_of_not_gt hneg
      calc
        _ ≤ Real.exp (D * L) * Real.exp (D * (2 * L + 2)) *
            (Real.exp (D * (2 * L + 4)) * Real.exp (L + (D + L + D * L) + 1)) := by gcongr
        _ ≤ _ := by simp only [← Real.exp_add]; exact Real.exp_le_exp.mpr hlog₃

theorem affineReferenceError_accuracy_separated {target Q Qη mask cap lip boundary support volume Ki η ratio ε mesh : ℝ}
    (hη0 : 0 ≤ η) (hratio0 : 0 ≤ ratio) (hε0 : 0 ≤ ε) (hmesh0 : 0 ≤ mesh)
    (hcoeff : mask ≤ Real.exp Qη ∧
      mask * (2 * cap * boundary + lip * 2) * support ≤ Real.exp Q ∧
      mask * lip * support ≤ Real.exp Q ∧ mask * volume * (Ki + lip) ≤ Real.exp Q)
    (hη : η ≤ Real.exp (-(target + Qη + 4)))
    (hratio : ratio ≤ Real.exp (-(target + Q + 4)))
    (hε : ε ≤ Real.exp (-(target + Q + 4)))
    (hmesh : mesh ≤ Real.exp (-(target + Q + 4))) :
    mask * (η + ((2 * cap * boundary + lip * 2) * ratio + lip * ε) * support +
      volume * (Ki + lip) * mesh) ≤ Real.exp (-target) := by
  have hterm {c x Q : ℝ} (hc : c ≤ Real.exp Q) (hx0 : 0 ≤ x)
      (hx : x ≤ Real.exp (-(target + Q + 4))) : c * x ≤ Real.exp (-(target + 4)) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-(target + Q + 4)) :=
        (mul_le_mul_of_nonneg_right hc hx0).trans (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h₁ := hterm hcoeff.1 hη0 hη
  have h₂ := hterm hcoeff.2.1 hratio0 hratio
  have h₃ := hterm hcoeff.2.2.1 hε0 hε
  have h₄ := hterm hcoeff.2.2.2 hmesh0 hmesh
  have hsum : mask * (η + ((2 * cap * boundary + lip * 2) * ratio + lip * ε) * support +
      volume * (Ki + lip) * mesh) ≤ 4 * Real.exp (-(target + 4)) := by
    nlinarith only [h₁, h₂, h₃, h₄]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (-(target + 4)) := hsum
    _ ≤ Real.exp 4 * Real.exp (-(target + 4)) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedAffineL1_primitive_bounds {D P Prho Pk : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hPrho : 0 ≤ Prho) (hPk : 0 ≤ Pk)
    {Mk : ℕ} (hMk : (Mk : ℝ) ≤ Real.exp Pk)
    (partition : LayerSamplerAxis I n → Prop)
    (R : Fin m → ℝ) (hR : ∀ j, 0 ≤ R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho) :
    let L := allocatedAffineL1Log m D P Prho Pk
    let Output := Σ a : {a // ¬partition a}, O a.val.1
    0 ≤ L ∧ P ≤ L ∧
      allocatedDensityLog (G := G) B α O P ≤ L ∧
      allocatedJetSupportLog (G := G) B α O P ≤ L ∧
      (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) ≤ Real.exp L ∧
      partitionedIdealRadius α m + 1 ≤ Real.exp L ∧
      ‖(∏ o : Output, |R o.1.val.1|)⁻¹‖ *
        ((affineProductProfileLip Output ρ : ℝ) * Real.exp P) ≤ Real.exp L ∧
      ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk ≤ L ∧
      scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤ Real.exp L := by
  intro L Output
  have hD := hdim.nonneg
  have hden := allocatedDensityEnvelope_nonneg m hD hP
  have hsupp := allocatedSupportEnvelope_nonneg m hD hP
  have hindex : 0 ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk := mul_nonneg (Nat.cast_nonneg _) hPk
  have hlip : 0 ≤ allocatedIdealLipEnvelope D P Prho := by
    unfold allocatedIdealLipEnvelope
    positivity
  have hradius : 0 ≤ ((m + 1 : ℕ) : ℝ) * D + 2 := by positivity
  have hboundary : 0 ≤ scalarCubeRiemannLog D := by unfold scalarCubeRiemannLog; positivity
  have hpieces : 0 ≤ L ∧ P ≤ L ∧
      ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk + allocatedDensityEnvelope m D P ≤ L ∧
      allocatedSupportEnvelope m D P ≤ L ∧ allocatedIdealLipEnvelope D P Prho ≤ L ∧
      ((m + 1 : ℕ) : ℝ) * D + 2 ≤ L ∧ scalarCubeRiemannLog D ≤ L := by
    dsimp only [L, allocatedAffineL1Log]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hdenL : allocatedDensityEnvelope m D P ≤ L := by linarith only [hpieces.2.2.1, hindex]
  refine ⟨hpieces.1, hpieces.2.1, (allocatedDensityLog_le_envelope B hdim hP).trans hdenL,
    (allocatedJetSupportLog_le_envelope B hdim hP).trans hpieces.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk) * Real.exp (allocatedDensityEnvelope m D P) :=
        mul_le_mul (layerKernelIndexBound_le_exp m hMk)
          (Real.exp_le_exp.mpr (allocatedDensityLog_le_envelope B hdim hP)) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hpieces.2.2.1
  · apply (partitionedIdealRadius_add_one_le_exp α m).trans
    apply Real.exp_le_exp.mpr
    have hdim' := mul_le_mul_of_nonneg_left hdim.cube (by positivity : 0 ≤ (m : ℝ) + 1)
    have hb := hpieces.2.2.2.2.2.1
    push_cast at hb
    linarith
  · have hk := diagonalProfileLip_le_exp (fun o : Output => R o.1.val.1)
      (fun o => hR o.1.val.1) hP hPrho (hdim.active_outputs B partition) hdim.profile
      (fun o => hRi o.1.val.1) hρ
    simp only [NNReal.coe_mul, NNReal.coe_mk, coe_nnnorm] at hk
    simp_rw [abs_of_nonneg (hR _)]
    exact hk.trans (Real.exp_le_exp.mpr hpieces.2.2.2.2.1)
  · linarith only [hpieces.2.2.1, hden]
  · exact (scalarCubeRiemannBoundary_le_exp α hD hdim.cube).trans
      (Real.exp_le_exp.mpr hpieces.2.2.2.2.2.2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedPerturbativeSeedPowerBudget
namespace OAI

section

namespace Erdos3

theorem slicedPrincipalBoundaryRadius_inverse_le_exp (N : ℕ) {η P : ℝ}
    (hη : 0 < η) (hP : 0 ≤ P) (hN : (N : ℝ) + 1 ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P) :
    (slicedPrincipalBoundaryRadius N η)⁻¹ ≤ Real.exp (2 * P + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  unfold slicedPrincipalBoundaryRadius
  apply inv_min_le_of_inv_le
  · norm_num
    have he := Real.exp_le_exp.mpr (show 4 ≤ 2 * P + 4 by linarith)
    linarith [Real.add_one_le_exp (4 : ℝ)]
  · calc
      (η / (16 * ((N : ℝ) + 1)))⁻¹ = 16 * ((N : ℝ) + 1) * η⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 4 * Real.exp P * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem slicedPrincipalMinor_inverse_le_exp (N m : ℕ) {a δ η P : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (haP : a⁻¹ ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    (a * δ * (δ * slicedPrincipalBoundaryRadius N η) ^ m)⁻¹ ≤
      Real.exp (2 * P + (3 * P + 4) * m) := by
  have haInv : 0 < a⁻¹ := inv_pos.mpr ha
  have hr := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hrP := slicedPrincipalBoundaryRadius_inverse_le_exp N hη hP hN hηP
  calc
    _ = (a⁻¹ * δ⁻¹) * (δ⁻¹ * (slicedPrincipalBoundaryRadius N η)⁻¹) ^ m := by
      simp only [mul_inv_rev]
      ring
    _ ≤ (Real.exp P * Real.exp P) * (Real.exp P * Real.exp (2 * P + 4)) ^ m := by gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem slicedPrincipalComparisonBudget_le_exp (N m : ℕ) {C A r κ P : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hr : 0 < r) (hκ : 0 < κ) (hP : 0 ≤ P)
    (hN : (N : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (hCP : C ≤ Real.exp P) (hAP : A ≤ Real.exp P)
    (hrP : r⁻¹ ≤ Real.exp P) (hκP : κ⁻¹ ≤ Real.exp P) :
    slicedPrincipalComparisonBudget N m C A r κ ≤ Real.exp (8 * P + 5) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hH : (N : ℝ) * (N * ((m : ℝ) * ((m : ℝ) * C))) ≤ Real.exp (5 * P) := by
    calc
      _ ≤ Real.exp P * (Real.exp P * (Real.exp P * (Real.exp P * Real.exp P))) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hH1 : (N : ℝ) * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1 ≤ Real.exp (5 * P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (by positivity : 0 ≤ 5 * P) hH
  have hS : 2 * κ⁻¹ * (2 * (N : ℝ) ^ 2 * A / r) ≤ Real.exp (5 * P + 2) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 1 * Real.exp P * (Real.exp 1 * (Real.exp P)^2 * Real.exp P * Real.exp P) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring
  have hT : (N : ℝ) * ((2 * κ⁻¹)^2 * (N * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1)) ≤
      Real.exp (8 * P + 3) := by
    calc
      _ ≤ Real.exp P * ((Real.exp 1 * Real.exp P)^2 * Real.exp (5 * P + 1)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring
  have hS' := hS.trans (Real.exp_le_exp.mpr (show 5 * P + 2 ≤ 8 * P + 3 by linarith))
  have hsum : 2 * κ⁻¹ * (2 * (N : ℝ)^2 * A / r) +
      N * ((2 * κ⁻¹)^2 * (N * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1)) ≤ Real.exp (8 * P + 4) := by
    calc
      _ ≤ 2 * Real.exp (8 * P + 3) := by linarith
      _ ≤ Real.exp 1 * Real.exp (8 * P + 3) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hb := one_add_le_exp_succ (by positivity : 0 ≤ 8 * P + 4) hsum
  rw [show 8 * P + 4 + 1 = 8 * P + 5 by ring] at hb
  simpa only [slicedPrincipalComparisonBudget, ← add_assoc] using hb

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem slicedEndpointUniformScale_inverse_le_exp (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    let L := (3 * P + 4) * m + 5 * P + 10
    (slicedPolynomialScale N O N m m 1 1 a δ A η)⁻¹ ≤ Real.exp (48 * L + 2 * P + 2 * m + 47) := by
  let L := (3 * P + 4) * m + 5 * P + 10
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hPL : P ≤ L := by dsimp [L]; nlinarith
  have hLP : Real.exp P ≤ Real.exp L := Real.exp_le_exp.mpr hPL
  let r := slicedPrincipalBoundaryRadius N η
  let κ := a * δ * (δ * r)^m
  have hr : 0 < r := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hκ : 0 < κ := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr) _)
  have hN0 : (N : ℝ) ≤ Real.exp P := by linarith
  have hrL : r⁻¹ ≤ Real.exp L :=
    (slicedPrincipalBoundaryRadius_inverse_le_exp N hη hP hN hηP).trans
      (Real.exp_le_exp.mpr (by dsimp [L]; nlinarith))
  have hκL : κ⁻¹ ≤ Real.exp L :=
    (slicedPrincipalMinor_inverse_le_exp N m ha hδ hη hP hN haP hδP hηP).trans
      (Real.exp_le_exp.mpr (by dsimp [L]; nlinarith))
  let Q := slicedPrincipalComparisonBudget N m 1 A r κ
  have hQ : 0 ≤ Q := slicedPrincipalComparisonBudget_nonneg N m zero_le_one hA hr hκ
  have hQL : Q ≤ Real.exp (8 * L + 5) := slicedPrincipalComparisonBudget_le_exp N m
    zero_le_one hA hr hκ hL (hN0.trans hLP) (hm.trans hLP)
    (Real.one_le_exp_iff.mpr hL) (hAP.trans hLP) hrL hκL
  have hLS : L ≤ 8 * L + 6 := by linarith
  have hPS : P ≤ 8 * L + 6 := hPL.trans hLS
  have hhalf : (η / 2)⁻¹ ≤ Real.exp (8 * L + 6) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * η⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1 * Real.exp P := by gcongr
      _ = Real.exp (P + 1) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have ht : (slicedPrincipalC2Tolerance N O m 1 a δ A η)⁻¹ ≤ Real.exp (48 * L + 44) := by
    have he := polynomialPerturbationScale_inverse_le_exp (inv_nonneg.mpr hκ.le) zero_le_one hQ
      (half_pos hη) (show 0 ≤ 8 * L + 6 by positivity) O
      (hO.trans (Real.exp_le_exp.mpr hPS))
      (hκL.trans (Real.exp_le_exp.mpr hLS))
      (Real.one_le_exp_iff.mpr (by positivity))
      (hQL.trans (Real.exp_le_exp.mpr (by linarith))) hhalf
    change (slicedPrincipalC2Tolerance N O m 1 a δ A η)⁻¹ ≤ Real.exp (6 * (8 * L + 6) + 8) at he
    convert he using 1
    congr 1
    ring
  have hM : polynomialMassC2Budget N m 1 ≤ Real.exp (2 * P + 2 * m + 2) := by
    simpa only [add_zero] using polynomialMassC2Budget_le_exp N m hP zero_le_one hN0
      (show (1 : ℝ) ≤ Real.exp 0 by simp)
  have hM1 := one_add_le_exp_succ (show 0 ≤ 2 * P + 2 * m + 2 by positivity) hM
  have htpos := (slicedPrincipalC2Tolerance_pos_le_one N O m zero_le_one ha hδ hA hη).1
  change (slicedPolynomialScale N O N m m 1 1 a δ A η)⁻¹ ≤ _
  rw [slicedPolynomialScale, inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (2 * P + 2 * m + 2 + 1) * Real.exp (48 * L + 44) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

theorem unitProfilePrincipalLowerBound_inv_le_exp {C : ℝ}
    (hsize : ((∑ d, Fintype.card (B d) : ℕ) : ℝ) ≤ C) :
    (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (C + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hcard : ((∑ d, Fintype.card (B d) : ℕ) : ℝ) + 1 ≤ Real.exp C := by
    linarith [Real.add_one_le_exp C]
  simp only [unitProfilePrincipalLowerBound, one_div, inv_inv]
  calc
    _ ≤ Real.exp 3 * Real.exp C :=
      mul_le_mul h8 hcard (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (C + 3) := by rw [← Real.exp_add, add_comm]
    _ ≤ Real.exp (C + 4) := Real.exp_le_exp.mpr (by linarith)

theorem principalBlock_card_le_input_card (F : D → Type*) [∀ d, Fintype (F d)]
    (hF : ∀ d, 1 ≤ Fintype.card (F d)) :
    (∑ d, Fintype.card (B d)) ≤ Fintype.card (Σ d, B d × F d) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_le_sum
  intro d _
  rw [Fintype.card_prod]
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Fintype.card (B d)) (hF d)

theorem unitProfilePrincipalLowerBound_inv_le_exp_of_input_card
    (F : D → Type*) [∀ d, Fintype (F d)]
    (hF : ∀ d, 1 ≤ Fintype.card (F d)) {C : ℝ}
    (hsize : (Fintype.card (Σ d, B d × F d) : ℝ) ≤ C) :
    (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (C + 4) := by
  apply unitProfilePrincipalLowerBound_inv_le_exp B
  apply le_trans _ hsize
  exact_mod_cast principalBlock_card_le_input_card B F hF

namespace VectorPolynomial

theorem allocatedUnitProfilePrincipalLowerBound_inv_le_exp
    {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] {C : ℝ}
    (hsize : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ C) :
    (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (C + 4) := by
  exact unitProfilePrincipalLowerBound_inv_le_exp_of_input_card B
    (fun a => Fin (layerSamplerDegree I n a))
    (fun a => by
      rw [Fintype.card_fin]
      exact Nat.succ_le_succ (Nat.zero_le _)) hsize

end VectorPolynomial

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬short a},
  B (Subtype.val a) × Fin (degree (Subtype.val a)))

theorem allocatedOriginalSampleLiftLip_eq_card :
    allocatedOriginalSampleLiftLip B U basis S = (Fintype.card Input : ℝ≥0) * m := rfl

theorem allocatedOriginalSampleFullSliceLip_le_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    allocatedOriginalSampleFullSliceLip B U basis S t ≤
      2 * allocatedOriginalSampleLiftLip B U basis S := by
  unfold allocatedOriginalSampleFullSliceLip
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat,
    abs_of_nonneg ht0, Real.coe_toNNReal t ht0]
  linarith

theorem allocatedOriginalSampleFullSliceLip_coe_le_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) ≤
      2 * (allocatedOriginalSampleLiftLip B U basis S : ℝ) := by
  exact_mod_cast allocatedOriginalSampleFullSliceLip_le_two B U basis S ht0 ht1

theorem allocatedOriginalSampleLiftInput_card_le_allAxis :
    Fintype.card Input ≤ Fintype.card (PrincipalTupleIndex B degree) := by
  simp only [PrincipalTupleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  apply Finset.sum_le_sum_of_injOn Subtype.val
    (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact Nat.zero_le _

theorem allocatedOriginalSampleLiftLip_le_fullInputCount :
    allocatedOriginalSampleLiftLip B U basis S ≤
      (Fintype.card (PrincipalTupleIndex B degree) : ℝ≥0) * m := by
  rw [allocatedOriginalSampleLiftLip_eq_card]
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact_mod_cast allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S

theorem allocatedOriginalSampleLiftLip_coe_le_allAxis :
    (allocatedOriginalSampleLiftLip B U basis S : ℝ) ≤
      (Fintype.card (PrincipalTupleIndex B degree) : ℝ) * (m : ℝ) := by
  exact_mod_cast allocatedOriginalSampleLiftLip_le_fullInputCount B U basis S

theorem allocatedOriginalSampleLiftLip_le_exp_of_allAxis {P : ℝ}
    (hcount : (Fintype.card (PrincipalTupleIndex B degree) : ℝ) * (m : ℝ) ≤ P) :
    (allocatedOriginalSampleLiftLip B U basis S : ℝ) ≤ Real.exp P := by
  exact (allocatedOriginalSampleLiftLip_coe_le_allAxis B U basis S).trans
    (hcount.trans (by linarith [Real.add_one_le_exp P]))

theorem allocatedOriginalSampleFullSliceLip_le_two_exp_of_allAxis
    {P t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcount : (Fintype.card (PrincipalTupleIndex B degree) : ℝ) * (m : ℝ) ≤ P) :
    (allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) ≤ 2 * Real.exp P :=
  (allocatedOriginalSampleFullSliceLip_coe_le_two B U basis S ht0 ht1).trans
    (mul_le_mul_of_nonneg_left
      (allocatedOriginalSampleLiftLip_le_exp_of_allAxis B U basis S hcount) (by norm_num))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end


