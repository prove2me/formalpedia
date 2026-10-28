-- Prove2me | Definitions.Def_OAIQ6El006
-- name    : OAIQ6El006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T10:27:10.383592+00:00
-- url     : https://prove2.me/theorems/d9120982-37d3-47f8-86c9-f1d1089e2730
-- title:
--   Definitions bundle OAIQ6El006 of the split of OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 49 definitions and 2 theorems. The definitions and types are `OAI.ElasticityDistribution.leadingPair`, `OAI.ElasticityDistribution.leadingRCLM`, `OAI.ElasticityDistribution.leadingRd`, `OAI.ElasticityDistribution.leadingSCLM`, `OAI.ElasticityDistribution.leadingSd`, `OAI.ElasticityDistribution.lowerPart`, `OAI.ElasticityDistribution.normalCLM`, `OAI.ElasticityDistribution.planeSchwartz`, `OAI.ElasticityDistribution.rdCLM`, `OAI.ElasticityDistribution.scdCLM`, `OAI.ElasticityDistribution.schwartzDirection`, `OAI.ElasticityDistribution.schwartzLeadingR`, `OAI.ElasticityDistribution.schwartzLeadingS`, `OAI.ElasticityNegativeOrder.Pbeta`, `OAI.ElasticityNegativeOrder.Pdir`, `OAI.ElasticityNegativeOrder.W`, `OAI.ElasticityNegativeOrder.betaDeriv`, `OAI.ElasticityNegativeOrder.betaSystem`, `OAI.ElasticityNegativeOrder.conjugatedDeriv`, `OAI.ElasticityNegativeOrder.dirDeriv`, `OAI.ElasticityNegativeOrder.dirSystem`, `OAI.ElasticityNegativeOrder.expQuad`, `OAI.ElasticityNegativeOrder.lowerBeta`, `OAI.ElasticityNegativeOrder.lowerDir`, `OAI.ElasticityNegativeOrder.lowerOrder`, `OAI.ElasticityNegativeOrder.lowerSystem`, `OAI.ElasticityNegativeOrder.phaseSystem`, `OAI.ElasticityNegativeOrder.rotCoeff`, `OAI.ElasticityNegativeOrder.sobNorm`, `OAI.ElasticityNegativeOrder.sumNorm`, `OAI.ElasticityNegativeOrder.weightCut`, `OAI.ElasticityPhysicalAlgebra.divShift`, `OAI.ElasticityPhysicalAlgebra.lapShift`, `OAI.ElasticityPhysicalDual.embed`, `OAI.ElasticityPhysicalDual.physicalLM`, `OAI.ElasticityPhysicalDual.supported`, `OAI.ElasticityPhysicalEstimate.augmentedForcing`, `OAI.ElasticityPhysicalEstimate.physicalAug`, `OAI.ElasticityRecovery.EqualRestrictedTransports`, `OAI.ElasticityRecovery.Q` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: [`Elasticity_Bessel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Bessel.lean), [`Elasticity_CGO`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CGO.lean), [`Elasticity_Carleman`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Carleman.lean), [`Elasticity_Recovery`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Recovery.lean), [`Elasticity_Smoothing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Smoothing.lean), [`Elasticity_Solvability`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Solvability.lean), [`Elasticity_Transfer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean), [`Elasticity_WeakLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean).
--
--   **Imports.** It imports the bundles `OAIQ6El004` and `OAIQ6El005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ6El007`; the statements `OAI.ElasticityAugmented.restricted_transports_of_chart_equal`, `OAI_ElasticityCGO_cut_actual_augmented_bound`, `OAI_ElasticityCGO_formal_scalar_polynomial`, `OAI.ElasticityCGO.localized_actual_strong_bound`, `OAI.ElasticityCGO.localized_formal_L2_tendsto`, `OAI.ElasticityCGO.localized_formal_augmented_H1_bound`, `OAI_ElasticityCGO_localized_formal_divergence_H1_bound`, `OAI.ElasticityCGO.physical_column_shifted_realization`, `OAI.ElasticityDistribution.actual_transferred_limit`, `OAI.ElasticityDistribution.classical_quantitative_correction`, `OAI.ElasticityDistribution.exists_lower_realization`, `OAI.ElasticityDistribution.leading_matrix_local`, `OAI.ElasticityDistribution.lower_realization_bound`, `OAI_ElasticityDistribution_lp_cutoff_derivative`, `OAI.ElasticityDistribution.physical_quantitative_correction`, `OAI.ElasticityDistribution.scalar_principal_quantitative_gain`, `OAI.ElasticityDistribution.smooth_column_patch`, `OAI.ElasticityDistribution.weak_physical_leading`, `OAI.ElasticityDistribution.weak_smooth_solvability`, `OAI_ElasticityGeneralSlicing_coupled_slice_equations`, `OAI_ElasticityGeneralSlicing_weak_slice_from_product_tests`, `OAI_ElasticityPhysicalEstimate_compact_comparison_estimate`, `OAI.ElasticityPhysicalEstimate.physical_compact_comparison`, `OAI_ElasticityPlanar_smooth_operator_all_orders`, `OAI_ElasticityRecovery_coefficients_equal_of_restricted_transports`, `OAI_Elasticity_dn_common_leading_frame`, `OAI.Elasticity.dn_weak_transport_column`, `OAI_Elasticity_extended_dn_compact_comparison` and `OAI_Elasticity_physical_supported_transfer`; the proofs of `OAI.ElasticityAugmented.restricted_transports_of_chart_equal`, `OAI_ElasticityBoundaryPacket_Setup_field_force_mass`, `OAI_ElasticityCGO_cut_actual_augmented_bound`, `OAI_ElasticityCGO_formal_scalar_polynomial`, `OAI.ElasticityCGO.localized_actual_strong_bound`, `OAI.ElasticityCGO.localized_formal_L2_tendsto`, `OAI.ElasticityCGO.localized_formal_augmented_H1_bound`, `OAI_ElasticityCGO_localized_formal_divergence_H1_bound`, `OAI.ElasticityCGO.physical_cgo_from_recursion`, `OAI.ElasticityCGO.physical_column_shifted_realization`, `OAI.ElasticityDistribution.actual_transferred_limit`, `OAI.ElasticityDistribution.classical_quantitative_correction`, `OAI.ElasticityDistribution.compact_transport_smoothing`, `OAI.ElasticityDistribution.exists_lower_realization`, `OAI.ElasticityDistribution.leading_matrix_local`, `OAI.ElasticityDistribution.lower_realization_bound`, `OAI_ElasticityDistribution_lp_cutoff_derivative`, `OAI.ElasticityDistribution.normalized_quantitative_gain`, `OAI.ElasticityDistribution.physical_quantitative_correction`, `OAI.ElasticityDistribution.scalar_principal_quantitative_gain`, `OAI.ElasticityDistribution.smooth_column_patch`, `OAI.ElasticityDistribution.weak_physical_leading`, `OAI.ElasticityDistribution.weak_smooth_solvability`, `OAI_ElasticityGeneralSlicing_coupled_slice_equations`, `OAI_ElasticityGeneralSlicing_weak_slice_from_product_tests`, `OAI.ElasticityPhysicalEstimate.physical_compact_comparison`, `OAI_ElasticityPlanar_classical_parameter_smooth`, `OAI_ElasticityPlanar_exists_classical_variable`, `OAI_ElasticityPlanar_smooth_operator_all_orders`, `OAI_ElasticityRecovery_coefficients_equal_of_restricted_transports`, `OAI.Elasticity.dn_global_coefficients_equal`, `OAI.Elasticity.dn_smooth_transport_column`, `OAI.Elasticity.dn_weak_transport_column`, `OAI.Elasticity.physical_classical_transfer` and `OAI_Elasticity_physical_supported_transfer`.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ6El004
import Definitions.Def_OAIQ6El005

section
-- module Solutions.OAIQ6_Elast.Elasticity_Bessel
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete Fourier Bessel potentials for the required negative-order
supported Carleman estimate. All functions and operators are actual Schwartz
maps; no Sobolev-shift estimate is being assumed. -/
open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap
namespace ElasticitySchwartzCarleman

def mass (f : Test) : ℝ := (pair f f).re

def A (h a b : ℝ) : Test →ₗ[ℂ] Test :=
  -(h : ℂ)^2 • lap - (G a b).comp (G a b)

def B (h a b : ℝ) : Test →ₗ[ℂ] Test :=
  (2 * (h : ℂ)) • (G a b).comp (d (e 0)) + ((h : ℂ) * b) • LinearMap.id

def P (h a b : ℝ) : Test →ₗ[ℂ] Test := A h a b + B h a b

def gradientMass (f : Test) : ℝ := ∑ i : Fin 3, mass (d (e i) f)

end ElasticitySchwartzCarleman

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

def conjugatedDeriv (h b : ℝ) (i : Fin 3) (f : S) : S :=
  ((h^2:ℝ):ℂ) • d (e i) f - (if i=0 then (h:ℂ) • G (-1) b f else 0)

def lowerOrder (h b : ℝ) (a : Fin 3 → X → ℂ) (v : X → ℂ) (f : S) : S :=
  (∑ i : Fin 3, mult (a i) (conjugatedDeriv h b i f)) + ((h^2:ℝ):ℂ) • mult v f

/-- Componentwise ℓ¹ auxiliary norm; the actual Hermitian Sobolev norm is
`sobNorm` below, and is compared explicitly, not substituted in the statement. -/
def sumNorm {n : ℕ} (h s : ℝ) (U : Fin n → S) : ℝ :=
  ∑ i, norm2 (J h s (U i))

def sobNorm {n : ℕ} (h s : ℝ) (U : Fin n → S) : ℝ :=
  Real.sqrt (∑ i, norm2 (J h s (U i))^2)

def lowerSystem {n : ℕ} (h b : ℝ) (a : Fin 3 → Fin n → Fin n → X → ℂ)
    (v : Fin n → Fin n → X → ℂ) (U : Fin n → S) (i : Fin n) : S :=
  ∑ j, lowerOrder h b (fun k => a k i j) (v i j) (U j)

end

section

def expQuad (c : ℂ) (x : X) : ℂ := Complex.exp ((c/2)*(qCLM x)^2)

def weightCut (R : ℝ) (hR : 1 ≤ R) (c : ℂ) (x : X) : ℂ :=
  (cutoff R hR x : ℂ)*expQuad c x

def W (R : ℝ) (hR : 1 ≤ R) (c : ℂ) : S →L[ℂ] S := mult (weightCut R hR c)

end

/-- The actual conjugated differential operator, with a local cutoff that
is identically one on the support, not an abstract operator hypothesis. -/
def phaseSystem (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (U : Fin 4 → S) (i : Fin 4) : S :=
  O R hR (-β) h (P h (-1) 0 (O R hR β h (U i))+
    lowerSystem h 0 a v (fun j => O R hR β h (U j)) i)

def Pbeta (h : ℝ) (β : X) (f : S) : S :=
  ((-h^2 : ℝ) : ℂ) • (lap f + (∑ i : Fin 3, (2*oscRate β h (e i)) • d (e i) f) +
    (∑ i : Fin 3, (oscRate β h (e i))^2) • f) - f -
  ((2*h : ℝ) : ℂ) • (d (e 0) f+oscRate β h (e 0) • f)

def betaDeriv (h : ℝ) (β : X) (i : Fin 3) (f : S) : S :=
  ((h^2 : ℝ) : ℂ) • (d (e i) f+oscRate β h (e i) • f) +
    (if i=0 then (h:ℂ) • f else 0)

def lowerBeta (h : ℝ) (β : X) (a : Fin 3 → X → ℂ) (v : X → ℂ) (f : S) : S :=
  (∑ i : Fin 3, mult (a i) (betaDeriv h β i f)) + ((h^2 : ℝ) : ℂ) • mult v f

def betaSystem (h : ℝ) (β : X)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (U : Fin 4 → S) (i : Fin 4) : S :=
  Pbeta h β (U i) + ∑ j, lowerBeta h β (fun k => a k i j) (v i j) (U j)

/-- Minus the semiclassical conjugated Laplacian for the real/imaginary
parts α,β of the phase. The last term vanishes exactly for null phases. -/
def Pdir (h : ℝ) (α β : X) (f : S) : S :=
  ((-h^2 : ℝ) : ℂ) • lap f - ((2*h : ℝ) : ℂ) • d α f -
    (((2*h : ℝ) : ℂ)*Complex.I) • d β f -
    (((‖α‖^2-‖β‖^2 : ℝ) : ℂ)+2*Complex.I*(inner ℝ α β : ℂ)) • f

def dirDeriv (h : ℝ) (α β : X) (i : Fin 3) (f : S) : S :=
  ((h^2 : ℝ) : ℂ) • d (e i) f + ((h : ℂ)*((α i : ℂ)+Complex.I*(β i : ℂ))) • f

def lowerDir (h : ℝ) (α β : X) (a : Fin 3 → X → ℂ) (v : X → ℂ) (f : S) : S :=
  (∑ i : Fin 3, mult (a i) (dirDeriv h α β i f)) + ((h^2 : ℝ) : ℂ) • mult v f

def dirSystem (h : ℝ) (α β : X)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (U : Fin 4 → S) (i : Fin 4) : S :=
  Pdir h α β (U i) + ∑ j, lowerDir h α β (fun k => a k i j) (v i j) (U j)

def rotCoeff (A : X ≃ₗᵢ[ℝ] X) (a : Fin 3 → X → ℂ) (k : Fin 3) (x : X) : ℂ :=
  ∑ i : Fin 3, (A (e k) i : ℂ)*a i (A x)

end ElasticityNegativeOrder

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

/-- The actual normalized forcing generated by a physical forcing F.
Here n=1/μ, o=1/(λ+2μ), and c_i=-2(∂ᵢμ)/μ.
The scalar entry contains the conjugated divergence. -/
def augmentedForcing (h : ℝ) (α β : X) (n o : X → ℂ) (c : Fin 3 → X → ℂ)
    (F : Fin 3 → S) : Fin 4 → S :=
  Fin.cons (mult o (∑ i, (dirDeriv h α β i (F i) + ((h^2 : ℝ) : ℂ) • mult (c i) (F i))))
    (fun i => ((h^2 : ℝ) : ℂ) • mult n (F i))

end ElasticityPhysicalEstimate

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

def lapShift (z : Fin 3 → ℂ) (f : S) : S := ∑ i, shiftD z i (shiftD z i f)

def divShift (z : Fin 3 → ℂ) (u : Fin 3 → S) : S := ∑ i, shiftD z i (u i)

end ElasticityPhysicalAlgebra

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Solvability
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalDual
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityPhysicalAlgebra ElasticityPhysicalEstimate

def embed : (Fin 3 → S) →ₗ[ℂ] H where
  toFun u := WithLp.toLp 2 (fun i => L2 (u i))
  map_add' u v := by apply PiLp.ext; intro i; exact map_add L2 _ _
  map_smul' a u := by apply PiLp.ext; intro i; exact map_smul L2 _ _

/-- Supported Schwartz vectors, regarded as an actual subspace of L2. -/
def supported (R : ℝ) : Submodule ℂ (Fin 3 → S) where
  carrier := {u | ∀ i, BallSupported R (u i)}
  zero_mem' _i := BallSupported.zero R
  add_mem' hu hv i := (hu i).add (hv i)
  smul_mem' a _u hu i := (hu i).smul a

lemma physical_add (z : Fin 3 → ℂ) (lam m : X → ℂ) (u v : Fin 3 → S) :
    physical z lam m (u+v) = physical z lam m u + physical z lam m v := by
  funext i
  simp only [physical, Pi.add_apply, map_add, Finset.sum_add_distrib]
  abel

lemma physical_smul (z : Fin 3 → ℂ) (lam m : X → ℂ) (a : ℂ) (u : Fin 3 → S) :
    physical z lam m (a • u) = a • physical z lam m u := by
  funext i
  simp only [physical, Pi.smul_apply, map_smul, ← smul_add, ← Finset.smul_sum]

/-- Exact shifted stress-divergence as a linear map, for duality on its range. -/
def physicalLM (z : Fin 3 → ℂ) (lam m : X → ℂ) : (Fin 3 → S) →ₗ[ℂ] (Fin 3 → S) where
  toFun := physical z lam m
  map_add' := physical_add z lam m
  map_smul' := physical_smul z lam m

end ElasticityPhysicalDual

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open MeasureTheory TemperedDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented ElasticityRegularity

def lowerPart (z : Fin 3 → ℂ) (A : Fin 3 → Fin 4 → Fin 4 → Coeff)
    (V : Fin 4 → Fin 4 → Coeff) (U : Fin 4 → Dist) (i : Fin 4) : Dist :=
  (∑ k, ∑ j, A k i j • sd z k (U j))+(∑ j, V i j • U j)+
    (∑ k, (2*z k) • dd k (U i))+(∑ k, z k*z k) • U i

end
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Recovery
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix

/-! Finite-type uniqueness used in the last step of the elasticity proof.
All spaces and coefficient fields below are actual functions, not axioms. -/
noncomputable section
open Set Filter Module
open scoped BigOperators Topology

namespace ElasticityRecovery
open Module ElasticityFiniteType ElasticityConic

def hessian (f : X → ℝ) (x : X) (i j : Fin 3) : ℝ :=
  D (D f (basis i)) (basis j) x

def dir (θ : C3) (f : X → ℝ) (x : X) : ℂ :=
  dotProduct θ (fun i => (grad f x i : ℂ))

/-- Real matrix whose null contraction is exactly the Q block. -/
def QMatrix (m k : X → ℝ) (x : X) : RMat := fun i j =>
  (1 / 2 : ℝ) * (((m x / (k x + m x)) * grad (fun x => Real.log (k x)) x j -
    (1 / 2 : ℝ) * grad (fun x => Real.log (m x)) x j) *
    grad (fun x => Real.log (m x)) x i -
    (m x / (k x + m x)) * hessian (fun x => Real.log (m x)) x i j)

def T (m k : X → ℝ) (x : X) (θ : C3) : ℂ :=
  dir θ (fun x => Real.log (k x / (k x + m x))) x

def Q (m k : X → ℝ) (x : X) (θ : C3) : C3 :=
  (fun i j => (QMatrix m k x i j : ℂ)) *ᵥ θ

/-- This is equality of the two restricted bottom rows, not a DN hypothesis.
Deriving it from the actual DN maps is still required by the full theorem. -/
def EqualRestrictedTransports (m₁ k₁ m₂ k₂ : X → ℝ) : Prop :=
  ∀ x θ, θ ≠ 0 → null θ →
    T m₁ k₁ x θ = T m₂ k₂ x θ ∧
    ∀ p : C3, dotProduct θ p = 0 →
      dotProduct (Q m₁ k₁ x θ) p = dotProduct (Q m₂ k₂ x θ) p

end ElasticityRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transfer
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV)
open ElasticityCoeffBounds

/-- The scalar component is the actual shifted divergence. -/
def physicalAug (z : Fin 3 → ℂ) (u : Fin 3 → S) : Fin 4 → S :=
  Fin.cons (divShift z u) u

end ElasticityPhysicalEstimate

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented TemperedDistribution TrivSqZeroExt

def leadingRd (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) (i : Fin 3) : Dist :=
  (2*m) • directiond θ (u i)+direction dc θ m • u i+
    θ i • ((lam+m) • b+∑ j, dc j m • u j)
def leadingSd (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (b : Dist) : Dist :=
  (2*(lam+m+m)) • directiond θ b+(2*direction dc θ (lam+m)) • b+
    (4 : Coeff) • (∑ i, dc i m • directiond θ (u i))+
    (2 : Coeff) • (∑ i, direction dc θ (dc i m) • u i)

end
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented

def rdCLM (z : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) : AugHilbert →L[ℂ] Dist :=
  (coeffCLM m).comp ((lapdCLM z).comp (augEntry i.succ))+
  (coeffCLM (lam+m)).comp ((sdCLM z i).comp (augEntry 0))+
  (∑ j, (coeffCLM (dc j m)).comp ((sdCLM z j).comp (augEntry i.succ)+(sdCLM z i).comp (augEntry j.succ)))+
  (coeffCLM (dc i lam)).comp (augEntry 0)
def scdCLM (z : Fin 3 → ℂ) (lam m : Coeff) : AugHilbert →L[ℂ] Dist :=
  (coeffCLM (lam+m+m)).comp ((lapdCLM z).comp (augEntry 0))+
  (2 : ℂ) • (∑ i, (coeffCLM (dc i (lam+m))).comp ((sdCLM z i).comp (augEntry 0)))+
  (2 : ℂ) • (∑ i, (coeffCLM (dc i m)).comp ((lapdCLM z).comp (augEntry i.succ)))+
  (2 : ℂ) • (∑ i, ∑ j, (coeffCLM (dc i (dc j m))).comp ((sdCLM z i).comp (augEntry j.succ)))+
  (coeffCLM (∑ i, dc i (dc i lam))).comp (augEntry 0)
def leadingRCLM (θ : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) : AugHilbert →L[ℂ] Dist :=
  (coeffCLM (2*m)).comp ((directionCLM θ).comp (augEntry i.succ))+
  (coeffCLM (direction dc θ m)).comp (augEntry i.succ)+
  θ i • ((coeffCLM (lam+m)).comp (augEntry 0)+∑ j, (coeffCLM (dc j m)).comp (augEntry j.succ))
def leadingSCLM (θ : Fin 3 → ℂ) (lam m : Coeff) : AugHilbert →L[ℂ] Dist :=
  (coeffCLM (2*(lam+m+m))).comp ((directionCLM θ).comp (augEntry 0))+
  (coeffCLM (2*direction dc θ (lam+m))).comp (augEntry 0)+
  (coeffCLM 4).comp (∑ i, (coeffCLM (dc i m)).comp ((directionCLM θ).comp (augEntry i.succ)))+
  (coeffCLM 2).comp (∑ i, (coeffCLM (direction dc θ (dc i m))).comp (augEntry i.succ))
def normalCLM (θ : Fin 3 → ℂ) : AugHilbert →L[ℂ] Dist := ∑ i, θ i • augEntry i.succ
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open Set MeasureTheory TemperedDistribution

open scoped SchwartzMap LineDeriv ENNReal BigOperators
open ElasticityRegularity
variable {n P : Type*} [Fintype n]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]

def planeSchwartz (α β : X) : Test →L[ℂ] Test :=
  LineDeriv.lineDerivOpCLM ℂ Test α+Complex.I • LineDeriv.lineDerivOpCLM ℂ Test β
end ElasticityDistribution
namespace ElasticityDistribution
open Set TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented

def leadingPair (θ : Fin 3 → ℂ) (lam m n o : Coeff) (U : Fin 4 → Dist) : Fin 4 → Dist :=
  Fin.cons (o • (leadingSd θ lam m (fun j => U j.succ) (U 0)-
    (2 : ℂ) • (n • ∑ i, dc i m • leadingRd θ lam m (fun j => U j.succ) (U 0) i)))
    (fun i => n • leadingRd θ lam m (fun j => U j.succ) (U 0) i)

end ElasticityDistribution
namespace ElasticityDistribution
open Set TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented ElasticityPhysicalAlgebra ElasticityNegativeOrder

def schwartzDirection (θ : Fin 3 → ℂ) (u : Test) : Test := ∑ i,θ i • ∂_{e i} u
def schwartzLeadingR (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) (i : Fin 3) : Test :=
  mult (eval (2*m)) (schwartzDirection θ (u i))+mult (eval (direction dc θ m)) (u i)+
    θ i • (mult (eval (lam+m)) b+∑ j,mult (eval (dc j m)) (u j))
def schwartzLeadingS (θ : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Test) (b : Test) : Test :=
  mult (eval (2*(lam+m+m))) (schwartzDirection θ b)+mult (eval (2*direction dc θ (lam+m))) b+
    mult (eval (4 : Coeff)) (∑ i,mult (eval (dc i m)) (schwartzDirection θ (u i)))+
    mult (eval (2 : Coeff)) (∑ i,mult (eval (direction dc θ (dc i m))) (u i))
end ElasticityDistribution
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end


