-- Prove2me | Definitions.Def_OAIQ6El004
-- name    : OAIQ6El004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T10:23:33.366979+00:00
-- url     : https://prove2.me/theorems/49728976-bd07-4227-806b-0446b9ab52f5
-- title:
--   Definitions bundle OAIQ6El004 of the split of OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 141 declarations of OpenAI's Lean: 107 definitions, 1 inductive type or structure, 8 instances and 25 theorems. The definitions and types are `OAI.ElasticityAugmented.diagonalGauge`, `OAI.ElasticityAugmented.exponential`, `OAI.ElasticityAugmented.inverseP`, `OAI.ElasticityAugmented.inverseS`, `OAI.ElasticityAugmented.leadingRpair`, `OAI.ElasticityAugmented.localAmpLM`, `OAI.ElasticityAugmented.matrixD`, `OAI.ElasticityAugmented.matrixEval`, `OAI.ElasticityAugmented.normalPair`, `OAI.ElasticityAugmented.normalizedPair`, `OAI.ElasticityAugmented.positiveRoot`, `OAI.ElasticityAugmented.scalarSource`, `OAI.ElasticityAugmented.smoothEval`, `OAI.ElasticityAugmented.smoothLog`, `OAI.ElasticityAugmented.smoothOfReal`, `OAI.ElasticityAugmented.thetaDerivation`, `OAI.ElasticityAugmented.thetaGamma`, `OAI.ElasticityAugmented.topSource`, `OAI.ElasticityAugmented.transportQ`, `OAI.ElasticityAugmented.transportT`, `OAI.ElasticityBessel.J`, `OAI.ElasticityBessel.L2`, `OAI.ElasticityBessel.M`, `OAI.ElasticityBessel.ip`, `OAI.ElasticityBessel.norm2`, `OAI.ElasticityBoundaryChainRule.cp`, `OAI.ElasticityBoundaryChartOperator.chartLower`, `OAI.ElasticityBoundaryLeading.grad`, `OAI.ElasticityBoundaryPacket.Setup.trial`, `OAI.ElasticityBoundaryPhysicalMass.lower`, `OAI.ElasticityBoundaryPhysicalStrong.divergence`, `OAI.ElasticityBoundaryPhysicalStrong.lower`, `OAI.ElasticityBoundaryPhysicalStrong.stress`, `OAI.ElasticityBoundaryPhysicalTransfer.force`, `OAI.ElasticityBoundaryProjectedStress.realStress`, `OAI.ElasticityBoundaryPullback.directional`, `OAI.ElasticityBoundarySymbol.polynomialAdjugate`, `OAI.ElasticityBoundarySymbol.polynomialPhysical`, `OAI.ElasticityBoundaryTensorSeries.coefficient`, `OAI.ElasticityBoundaryTensorSeries.operator` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: `Elasticity_Bessel`, `Elasticity_BoundaryCalculus`, `Elasticity_BoundaryCharts`, `Elasticity_BoundaryData`, `Elasticity_BoundaryLayers`, `Elasticity_BoundaryPackets`, `Elasticity_BoundaryParametrix`, `Elasticity_BoundarySymbols`, `Elasticity_BoundaryValues`, `Elasticity_CGO`, `Elasticity_Carleman`, `Elasticity_Conic`, `Elasticity_ForcedTransport`, `Elasticity_Holomorphy`, `Elasticity_PhysicalCGO`, `Elasticity_Recovery`, `Elasticity_Regularity`, `Elasticity_Rigidity`, `Elasticity_Smoothing`, `Elasticity_Solvability`, `Elasticity_Transfer`, `Elasticity_Transport`, `Elasticity_TransportAlgebra`, `Elasticity_WeakLimits`.
--
--   **Imports.** It imports the bundles `OAIQ6El000`, `OAIQ6El001` and `OAIQ6El002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ6El006`; the statements `OAI.ElasticityAugmented.exists_real_physical_series`, `OAI.ElasticityAugmented.forced_equations_at`, `OAI.ElasticityAugmented.leading_equations_at_iff`, `OAI.ElasticityAugmented.supported_matrix_holomorphic`, `OAI.ElasticityAugmented.supported_matrix_smooth`, `OAI.ElasticityAugmented.supported_matrix_unique`, `OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude`, `OAI.ElasticityBoundaryForceSupport.transferred_force_all`, `OAI.ElasticityBoundaryPacket.Setup.energy_chart`, `OAI.ElasticityBoundaryPacket.Setup.packet`, `OAI.ElasticityBoundaryPacket.Setup.trial_residual`, `OAI.ElasticityBoundaryPacket.Setup.trial_size`, `OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound`, `OAI.ElasticityBoundarySmoothOperator.scaledOperator_order_bound`, `OAI.ElasticityCGO.cut_truncation_residual`, `OAI.ElasticityCGO.physical_cgo_from_recursion`, `OAI.ElasticityCGO.transferred_amplitude`, `OAI.ElasticityConic.chart_comparison_trivial`, `OAI.ElasticityConic.physical_conic_connections_equal`, `OAI.ElasticityDistribution.affine_cutoff_bound`, `OAI.ElasticityDistribution.augmentation_cutoff_bound`, `OAI.ElasticityDistribution.compact_transport_smoothing`, `OAI.ElasticityDistribution.normSource_cutoff_bound`, `OAI.ElasticityDistribution.normalized_quantitative_gain`, `OAI.ElasticityDistribution.physical_quantitative_H1`, `OAI.Elasticity.dn_common_normal_frame`, `OAI.Elasticity.dn_conic_comparison`, `OAI.Elasticity.dn_global_coefficients_equal`, `OAI.Elasticity.dn_smooth_transport_column`, `OAI.Elasticity.extended_dn_amplitude_transfer` and `OAI.Elasticity.physical_classical_transfer`; the proofs of `OAI.ElasticityAugmented.exists_physical_forced_transport`, `OAI.ElasticityAugmented.exists_physical_leading_frame`, `OAI.ElasticityAugmented.exists_physical_recursion_step`, `OAI.ElasticityAugmented.exists_real_physical_series`, `OAI.ElasticityAugmented.forced_equations_at`, `OAI.ElasticityAugmented.leading_equations_at_iff`, `OAI.ElasticityAugmented.supported_matrix_holomorphic`, `OAI.ElasticityAugmented.supported_matrix_smooth`, `OAI.ElasticityAugmented.supported_matrix_unique`, `OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude`, `OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer`, `OAI.ElasticityBoundaryForceSupport.transferred_force_all`, `OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass`, `OAI.ElasticityBoundaryMVTower.triangular_amplitudes`, `OAI.ElasticityBoundaryPacket.Setup.energy_chart`, `OAI.ElasticityBoundaryPacket.Setup.extract_normal`, `OAI.ElasticityBoundaryPacket.Setup.packet`, `OAI.ElasticityBoundaryPacket.Setup.trial_residual`, `OAI.ElasticityBoundaryPacket.Setup.trial_size`, `OAI.ElasticityBoundaryPacket.pair_separates`, `OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound`, `OAI.ElasticityBoundarySmoothOperator.scaledOperator_order_bound`, `OAI.ElasticityCGO.cut_truncation_residual`, `OAI.ElasticityCGO.transferred_amplitude`, `OAI.ElasticityConic.chart_comparison_trivial`, `OAI.ElasticityConic.physical_conic_connections_equal`, `OAI.ElasticityDistribution.affine_cutoff_bound`, `OAI.ElasticityDistribution.augmentation_cutoff_bound`, `OAI.ElasticityDistribution.normSource_cutoff_bound`, `OAI.ElasticityDistribution.physical_quantitative_H1`, `OAI.Elasticity.dn_common_normal_frame`, `OAI.Elasticity.dn_conic_comparison`, `OAI.Elasticity.extended_dn_amplitude_transfer` and `OAI.Elasticity.global_uniqueness`.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ6El000
import Definitions.Def_OAIQ6El001
import Definitions.Def_OAIQ6El002

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
namespace ElasticityBessel

def M (h s : ℝ) : S →L[ℂ] S :=
  SchwartzMap.smulLeftCLM ℂ (fun x => (weight h s x : ℂ))

def J (h s : ℝ) (f : S) : S := 𝓕⁻ (M h s (𝓕 f))

abbrev L2 : S →L[ℂ] Lp ℂ 2 (volume : Measure X) := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure X)

def norm2 (f : S) : ℝ := ‖L2 f‖

def ip (f g : S) : ℂ := inner ℂ (L2 f) (L2 g)

end ElasticityBessel

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap
namespace ElasticitySchwartzCarleman

def pair (f g : Test) : ℂ := ∫ z : X, star (f z) * g z

def e (i : Fin 3) : X := EuclideanSpace.single i 1

@[simp] lemma qCLM_e (i : Fin 3) : qCLM (e i) = if i = 0 then 1 else 0 := by
  simp [qCLM, e, EuclideanSpace.proj, apply_ite, eq_comm]

def Q : Test →ₗ[ℂ] Test := (SchwartzMap.smulLeftCLM ℂ qCLM).toLinearMap

@[simp] lemma Q_apply (f : Test) (x : X) : (Q f : X → ℂ) x = (x 0 : ℂ) * f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply qCLM.hasTemperateGrowth f x

/-- Affine normal derivative of the convexified linear weight. -/
def G (a b : ℝ) : Test →ₗ[ℂ] Test := (a : ℂ) • LinearMap.id + (b : ℂ) • Q

def lap : Test →ₗ[ℂ] Test := ∑ i : Fin 3, (d (e i)).comp (d (e i))

@[simp] lemma G_apply (a b : ℝ) (f : Test) (x : X) :
    (G a b f : Test) x = ((a : ℂ) + b * (x 0 : ℂ)) * f x := by
  simp only [G, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, add_apply, smul_apply, smul_eq_mul, Q_apply]
  ring

end ElasticitySchwartzCarleman

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

def mult (a : X → ℂ) : S →L[ℂ] S := SchwartzMap.smulLeftCLM ℂ a

end

section
/-- Support in a fixed closed Euclidean ball. -/
def BallSupported (R : ℝ) (f : S) : Prop :=
  ∀ x : X, f x ≠ 0 → ‖x‖ ≤ R

lemma BallSupported.add {R : ℝ} {f g : S} (hf : BallSupported R f)
    (hg : BallSupported R g) : BallSupported R (f+g) := by
  intro x hx
  by_contra hn
  have hf0 : f x = 0 := by by_contra h; exact hn (hf x h)
  have hg0 : g x = 0 := by by_contra h; exact hn (hg x h)
  exact hx (by simp [hf0, hg0])

lemma BallSupported.smul {R : ℝ} {f : S} (hf : BallSupported R f) (c : ℂ) :
    BallSupported R (c • f) := by
  intro x hx
  exact hf x (fun h => hx (by simp [h]))

def cutoff (R : ℝ) (hR : 1 ≤ R) : ContDiffBump (0 : X) where
  rIn := R+1
  rOut := R+2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

end

def osc (β : X) (h : ℝ) (x : X) : ℂ := Complex.exp (((inner ℝ β x / h : ℝ) : ℂ)*Complex.I)

def oscCut (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) (x : X) : ℂ :=
  (cutoff R hR x : ℂ)*osc β h x

def O (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) : S →L[ℂ] S := mult (oscCut R hR β h)

lemma BallSupported.zero (R : ℝ) : BallSupported R (0 : S) := by
  intro x hx; exact (hx (by simp)).elim

def oscRate (β : X) (h : ℝ) (v : X) : ℂ := ((inner ℝ β v/h : ℝ) : ℂ)*Complex.I

end ElasticityNegativeOrder

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal first and second coordinate chain rules. The maps are genuine
Frechet-smooth maps; a tensor pullback will use these identities, rather
than postulating a transformed elasticity operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChainRule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cp (f : Y → ℂ) (α : Fin 3) : Y → ℂ := dd f (Pi.single α 1)

end ElasticityBoundaryChainRule

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundarySymbols
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-!
Polynomial-amplitude inversion for the frozen physical half-space operator.
This is the arbitrary-order normal ODE used in a boundary-layer construction:
every exp(-t)-polynomial forcing has an exp(-t)-polynomial solution with
zero boundary value. No pseudodifferential solvability is assumed.
-/
noncomputable section
open Polynomial
namespace ElasticityBoundarySymbol

/-- The actual Fourier-transformed isotropic physical elasticity operator on
polynomial amplitudes, tangential covector (1,0), inward normal t. -/
def polynomialPhysical (l m : ℂ) (p : Fin 3 → P) : Fin 3 → P :=
  ![m • laplaceAmplitude (p 0) - (l+m) • p 0 +
      (Complex.I*(l+m)) • shiftedDerivative 1 (p 2),
    m • laplaceAmplitude (p 1),
    (Complex.I*(l+m)) • shiftedDerivative 1 (p 0) +
      (l+2*m) • laplaceAmplitude (p 2) + (l+m) • p 2]

/-- A polynomial differential adjugate; the middle polarization uses the same
scalar determinant, so all three components admit one uniform construction. -/
def polynomialAdjugate (l m : ℂ) (p : Fin 3 → P) : Fin 3 → P :=
  ![(l+2*m) • laplaceAmplitude (p 0) + (l+m) • p 0 -
      (Complex.I*(l+m)) • shiftedDerivative 1 (p 2),
    (l+2*m) • laplaceAmplitude (p 1),
    -(Complex.I*(l+m)) • shiftedDerivative 1 (p 0) +
      m • laplaceAmplitude (p 2) - (l+m) • p 2]

end ElasticityBoundarySymbol

end
end
section
/-! The finite-parameter differential operator of the actual Taylor-expanded
divergence tensor. No leading normal operator is stipulated. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryTensorSeries
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryProfile ElasticityBoundaryParameter ElasticityBoundaryLayerOperator

def pack : (Fin 3 → Polynomial MP) →ₗ[ℂ] Polynomial W :=
  ∑ i, (coeffMap (LinearMap.single ℂ (fun _ : Fin 3 => MP) i)).comp (LinearMap.proj i)

def operator (a : Tensor) (b : Lower) : Polynomial W →ₗ[ℂ] Polynomial W :=
  pack.comp (LinearMap.pi fun i =>
    (∑ α, ∑ j, ∑ β, (LinearMap.mulLeft ℂ (a i α j β)).comp
      ((PD α).comp ((PD β).comp (unpack j)))) +
    ((LinearMap.mulLeft ℂ (Polynomial.X^2)).comp
      (∑ j, ∑ β, (LinearMap.mulLeft ℂ (b i j β)).comp ((PD β).comp (unpack j)))))

def coefficient (a : Tensor) (b : Lower) (k : ℕ) : W →ₗ[ℂ] W :=
  ((Polynomial.lcoeff W k).restrictScalars ℂ).comp
    ((operator a b).comp (Polynomial.CAlgHom (R := ℂ) (A := W)).toLinearMap)

end ElasticityBoundaryTensorSeries

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Uniform multivariable Taylor estimates for anisotropically rescaled boundary
layers. The constants are proved for actual smooth compactly supported physical
coefficient extensions; no symbol/asymptotic identification is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityBoundaryTaylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp] lemma line_apply (z : E) (t : ℝ) : line z t = t • z := rfl

end ElasticityBoundaryTaylor

end
end
section
/-! True pullback of a second-order physical system. The coefficient Hessian
term is retained, and no equivalence of augmented and physical DN data is used. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryPullback
open ElasticityBoundaryChainRule ElasticityBoundarySmoothOperator ElasticityBoundaryStrongLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def directional (e : I → E) (a : Tensor E) (b : Lower E) (u : I → E → ℂ) (i : I) (x : E) : ℂ :=
  (∑ k, ∑ j, ∑ l, a i k j l x*dd (dd (u j) (e l)) (e k) x)+
    ∑ j, ∑ l, b i j l x*dd (u j) (e l) x

end ElasticityBoundaryPullback

end
end
section
/-! The strong expression is the divergence of the actual isotropic stress,
with every Lamé-gradient term retained. It is not an independently prescribed
system. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryPhysicalStrong
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryLayerOperator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def divergence (e : I → E) (u : I → E → ℂ) (x : E) : ℂ := ∑ j, dd (u j) (e j) x

def stress (e : I → E) (l m : E → ℂ) (u : I → E → ℂ) (i k : I) (x : E) : ℂ :=
  (if i=k then l x*divergence e u x else 0)+
    m x*(dd (u i) (e k) x+dd (u k) (e i) x)

def lower (e : I → E) (l m : E → ℂ) : Lower E := fun i j β x =>
  dd l (e i) x*(if j=β then 1 else 0)+dd m (e β) x*(if i=j then 1 else 0)+
    dd m (e j) x*(if i=β then 1 else 0)

end ElasticityBoundaryPhysicalStrong

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCharts
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The boundary-coordinate differential operator is obtained from literal
physical elasticity by the chain rule and a fixed Euclidean rotation. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChartOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
  ElasticityBoundaryFrameOperator ElasticityBoundaryPhysicalStrong
  ElasticityBoundarySmoothOperator ElasticityBoundaryLayerOperator ElasticityBoundaryStrongLayer

def chartLower (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) (ψ : X → Y)
    (l m : X → ℂ) : SmoothLower :=
  fun s r β y => lowerPull basis
    (mixedTensor (fun s i => frameMatrix Q i s) (frameMatrix Q) (coeff l m))
    (mixedLower (fun s i => frameMatrix Q i s) (frameMatrix Q) (lower basis l m)) ψ s r β (Φ y)

end ElasticityBoundaryChartOperator

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryParametrix
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Physical displacements obtained from compact chart fields. Their literal
strong Lamé force is the constructed curved-coordinate operator on the
whole trial support, rather than a formally equated auxiliary DN system. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPhysicalTransfer
open ElasticityBoundary ElasticityBoundaryChainRule ElasticityBoundaryPullback
  ElasticityBoundaryPhysicalStrong ElasticityBoundaryRotation ElasticityBoundaryFrameOperator
  ElasticityBoundaryChartOperator ElasticityBoundaryOperatorLocal ElasticityBoundaryStrongLayer

def force (l m : X → ℂ) (u : I → X → ℂ) : I → X → ℂ :=
  directional basis (coeff l m) (lower basis l m) u

end ElasticityBoundaryPhysicalTransfer

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryPackets
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The honest physical strong residual has the same quantitative L2 scale as
its fully curved coordinate expression. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPhysicalMass
open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryChartMass ElasticityBoundaryChartOperator ElasticityBoundaryRotation
  ElasticityBoundarySmoothOperator ElasticityBoundaryStrongLayer ElasticityBoundaryCutoffLayer
  ElasticityBoundaryFrameOperator

def lower (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X) (l m : X → ℂ) : SmoothLower :=
  chartLower Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m

end ElasticityBoundaryPhysicalMass

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryData
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryProjectedStress
/-! The complex quasimode's real and imaginary stresses are the literal real
physical stresses used by the DN map. -/
open Set MeasureTheory
open scoped BigOperators
open Elasticity ElasticityBoundaryChainRule ElasticityBoundaryPhysicalStrong
  ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalTransfer

def realStress (w : ℂ →L[ℝ] ℝ) (l m : X → ℝ) (u : I → X → ℂ) (i j : I) : X → ℝ :=
  fun x => w (stress basis (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) u i j x)

end ElasticityBoundaryProjectedStress
/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryTrialMass
open Elasticity ElasticityBoundaryResidualMass ElasticityBoundaryChainRule
abbrev X := EuclideanSpace ℝ I

end ElasticityBoundaryTrialMass

end
namespace ElasticityBoundaryPacket
/-! The physical quasimodes are genuine elements of the H1/trace construction
used by the real DN map, with uniform norm and arbitrary dual-residual decay. -/
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
open Elasticity ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryProjectedStress ElasticityBoundaryPhysicalStrong ElasticityBoundaryChainRule
  ElasticityBoundaryResidualMass ElasticityBoundaryTrialMass ElasticityBoundaryActualTower
  ElasticityBoundaryMVNormal ElasticityBoundaryChartOperator

variable {Ω : Set X} {x : X}

def Setup.trial (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) : ComplexTrial Ω :=
  complexFieldTrial (s.field q δ) (s.field_smooth q δ) s.image_compact (s.field_support q δ)

end ElasticityBoundaryPacket

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryValues
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Strictly positive Gaussian-normal moments, without relying on a numerical
constant or an unproved nondegeneracy of the boundary limit. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryWeights

def normalMoment (n : ℕ) : ℝ := ∫ y : Y, (y 2)^n*weight 2 y

end ElasticityBoundaryWeights

end
end
section
/-! Exact transverse and longitudinal frozen physical tests. Both are genuine
solutions of the normal isotropic elasticity equation. -/
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityBoundaryLeading
open Elasticity ElasticityBoundarySymbol ElasticityBoundaryMVNormal
  ElasticityBoundaryMVCalculus ElasticityBoundaryParameter ElasticityBoundaryLayerOperator

def grad (p : W) (y : Y) : CMatrix := fun i α => value (E₀ α (p i)) y

end ElasticityBoundaryLeading

end
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

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma temperate_fderiv (a : X → ℂ) (ha : a.HasTemperateGrowth) :
    (fderiv ℝ a).HasTemperateGrowth := by
  refine ⟨ha.1.fderiv_right (by simp), fun N => ?_⟩
  obtain ⟨k, C, h⟩ := ha.2 (N+1)
  refine ⟨k, C, fun x => ?_⟩
  simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.norm_map] using h x

lemma temperate_partial (a : X → ℂ) (ha : a.HasTemperateGrowth) (v : X) :
    (fun x => fderiv ℝ a x v).HasTemperateGrowth := by
  exact (ContinuousLinearMap.apply ℝ ℂ v).hasTemperateGrowth.comp (temperate_fderiv a ha)

/-- Constant complex phase shift, still an actual differential operator on Schwartz maps. -/
def shiftD (z : Fin 3 → ℂ) (i : Fin 3) : S →ₗ[ℂ] S := d (e i) + z i • LinearMap.id

/-- The conjugated physical stress-divergence, without treating its shifted derivatives as derivations. -/
def physical (z : Fin 3 → ℂ) (lam m : X → ℂ) (u : Fin 3 → S) (i : Fin 3) : S :=
  shiftD z i (mult lam (∑ j, shiftD z j (u j))) +
    ∑ j, shiftD z j (mult m (shiftD z j (u i) + shiftD z i (u j)))

def phase (h : ℝ) (α β : X) (i : Fin 3) : ℂ :=
  ((α i : ℂ)+Complex.I*(β i : ℂ))/(h : ℂ)

end ElasticityPhysicalAlgebra

open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A) (T : Fin 3 → A →ₗ[ℂ] A)

def normalizedPair (lam m n o : A) (u : Fin 3 → A) (b : A) : Fin 4 → A :=
  Fin.cons (o*(ST D T lam m u b-2*n*(∑ i, D i m*RT D T lam m u b i)))
    (fun i => n*RT D T lam m u b i)

end ElasticityAugmented

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityDistribution

open ElasticityAugmented ElasticityRegularity TemperedDistribution
lemma growth (a : Coeff) : (eval a).HasTemperateGrowth := a.property

instance instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist : SMul Coeff Dist := ⟨fun a u => smulLeftCLM ℂ (eval a) u⟩
lemma smul_def (a : Coeff) (u : Dist) : a • u = smulLeftCLM ℂ (eval a) u := rfl
instance instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist : Module Coeff Dist := Module.ofMinimalAxioms
  (fun a u v => (smulLeftCLM ℂ (eval a)).map_add u v)
  (fun a b u => by simp only [smul_def, eval_add, smulLeftCLM_add (growth a) (growth b),
    add_apply])
  (fun a b u => by
    simp only [smul_def, eval_mul]
    rw [smulLeftCLM_smulLeftCLM_apply (growth b) (growth a),mul_comm])
  (fun u => by simp only [smul_def,eval_one,smulLeftCLM_const,one_smul])

instance instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist : IsScalarTower ℂ Coeff Dist where
  smul_assoc c a u := by
    change smulLeftCLM ℂ (c • eval a) u = c • smulLeftCLM ℂ (eval a) u
    rw [smulLeftCLM_smul (growth a) c, smul_apply]
instance instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist : SMulCommClass ℂ Coeff Dist where
  smul_comm c a u := ((smulLeftCLM ℂ (eval a)).map_smul c u).symm

/-- The coefficient derivative and distribution derivative are genuine derivatives. -/
def dc (i : Fin 3) : Derivation ℂ Coeff Coeff := Derivation.mk' (R := ℂ) (A := Coeff) (M := Coeff)
  ({ toFun := fun (a : Coeff) => (⟨coord i a.val, ElasticityPhysicalAlgebra.temperate_partial _ (growth a) (e i)⟩ : Coeff)
     map_add' a b := by apply Subtype.ext; exact map_add (coord i) _ _
     map_smul' c a := by apply Subtype.ext; exact (coord i).toLinearMap.map_smul c a.val } : Coeff →ₗ[ℂ] Coeff)
  (by intro (a : Coeff) (b : Coeff); apply Subtype.ext; exact (coord i).leibniz a.val b.val)

def dd (i : Fin 3) : Dist →ₗ[ℂ] Dist := (LineDeriv.lineDerivOpCLM ℂ Dist (e i)).toLinearMap
lemma dd_leibniz (i : Fin 3) (a : Coeff) (u : Dist) :
    dd i (a • u) = dc i a • u+a • dd i u := by
  exact distribution_leibniz (growth a) (e i) (growth (dc i a)) u

open ElasticityAugmented TrivSqZeroExt

instance instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist : SMul Coeffᵐᵒᵖ Dist := ⟨fun a u => a.unop • u⟩
instance instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist : Module Coeffᵐᵒᵖ Dist := Module.ofMinimalAxioms
  (fun a u v => smul_add a.unop u v)
  (fun a b u => add_smul a.unop b.unop u)
  (fun a b u => by change (b.unop*a.unop) • u = a.unop • b.unop • u; rw [mul_comm,mul_smul])
  (fun u => (one_smul Coeff u))
instance instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist : IsCentralScalar Coeff Dist where
  op_smul_eq_smul _a _u := rfl
instance instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist : IsScalarTower ℂ Coeffᵐᵒᵖ Dist where
  smul_assoc c a u := by change (c • a.unop) • u = c • a.unop • u; exact smul_assoc c a.unop u

abbrev Ext := TrivSqZeroExt Coeff Dist
/-- The square-zero algebra is only an algebraic way of reusing the physical
compatibility identities: its genuine distribution component is never multiplied
by another distribution. -/
def de (i : Fin 3) : Derivation ℂ Ext Ext := Derivation.mk' (R := ℂ) (A := Ext) (M := Ext)
  ({ toFun := fun v => (dc i v.fst,dd i v.snd)
     map_add' := by
       intro v w
       apply TrivSqZeroExt.ext
       · change dc i (v.fst+w.fst) = dc i v.fst+dc i w.fst
         exact map_add (dc i) _ _
       · change dd i (v.snd+w.snd) = dd i v.snd+dd i w.snd
         exact map_add (dd i) _ _
     map_smul' := by
       intro c v
       apply TrivSqZeroExt.ext
       · change dc i (c • v.fst) = c • dc i v.fst
         exact (dc i).map_smul c v.fst
       · change dd i (c • v.snd) = c • dd i v.snd
         exact (dd i).map_smul c v.snd } : Ext →ₗ[ℂ] Ext)
  (by
    intro v w
    apply TrivSqZeroExt.ext
    · change dc i (v.fst*w.fst) = v.fst*dc i w.fst+w.fst*dc i v.fst
      exact (dc i).leibniz _ _
    · change dd i (v.fst • w.snd+w.fst • v.snd) =
        v.fst • dd i w.snd+dc i w.fst • v.snd +
        (w.fst • dd i v.snd+dc i v.fst • w.snd)
      rw [map_add,dd_leibniz,dd_leibniz]
      abel)

def sd (z : Fin 3 → ℂ) (i : Fin 3) : Dist →ₗ[ℂ] Dist := dd i+z i • LinearMap.id

def lapd (z : Fin 3 → ℂ) (u : Dist) : Dist := ∑ i, sd z i (sd z i u)
def divd (z : Fin 3 → ℂ) (u : Fin 3 → Dist) : Dist := ∑ i, sd z i (u i)
def rd (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) (i : Fin 3) : Dist :=
  m • lapd z (u i)+(lam+m) • sd z i d+
    (∑ j, dc j m • (sd z j (u i)+sd z i (u j)))+dc i lam • d

def scd (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) : Dist :=
  (lam+m+m) • lapd z d + (2 : ℂ) • (∑ i, dc i (lam+m) • sd z i d) +
  (2 : ℂ) • (∑ i, dc i m • lapd z (u i))+
  (2 : ℂ) • (∑ i, ∑ j, dc i (dc j m) • sd z i (u j))+
  (∑ i, dc i (dc i lam)) • d

def phys (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (i : Fin 3) : Dist :=
  sd z i (lam • divd z u)+ ∑ j, sd z j (m • (sd z j (u i)+sd z i (u j)))

def normPair (z : Fin 3 → ℂ) (lam m n o : Coeff) (u : Fin 3 → Dist) (d : Dist) : Fin 4 → Dist :=
  Fin.cons (o • (scd z lam m u d-(2 : ℂ) • (n • (∑ i, dc i m • rd z lam m u d i))))
    (fun i => n • rd z lam m u d i)
end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators
namespace ElasticityDistribution
open ElasticityAugmented TemperedDistribution
abbrev Test := 𝓢(X,ℂ)

/-- Equality of actual distributions tested strictly within the open domain. -/
def LocalEq (Ω : Set X) (u v : Dist) : Prop :=
  ∀ φ : Test, HasCompactSupport (φ : X → ℂ) → tsupport (φ : X → ℂ) ⊆ Ω → u φ=v φ

def normSource (z : Fin 3 → ℂ) (m n o : Coeff) (F : Fin 3 → Dist) : Fin 4 → Dist :=
  Fin.cons (o • (divd z F-(2 : ℂ) • (n • ∑ i, dc i m • F i))) (fun i => n • F i)

end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal

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

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators
namespace ElasticityCoeffBounds
open ElasticityAugmented
abbrev X := ElasticityAugmented.X

def ExteriorConstant (f : Smooth) : Prop :=
  ∃ c : ℂ, HasCompactSupport (fun x => (f : X → ℂ) x - c)

lemma ExteriorConstant.growth {f : Smooth} (hf : ExteriorConstant f) :
    (f : X → ℂ).HasTemperateGrowth := by
  obtain ⟨c, hc⟩ := hf
  have hg := hc.hasTemperateGrowth ((smooth_coe f).sub contDiff_const)
  convert hg.add (Function.HasTemperateGrowth.const c) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp

/-- The reciprocal is the pointwise reciprocal, not an abstract inverse assumption. -/
def reciprocal (f : Smooth) (hf : ∀ x, (f : X → ℂ) x ≠ 0) : Smooth :=
  ⟨fun x => ((f : X → ℂ) x)⁻¹, (smooth_coe f).inv hf⟩

lemma ExteriorConstant.reciprocal {f : Smooth} (hf : ExteriorConstant f)
    (hn : ∀ x, (f : X → ℂ) x ≠ 0) : ExteriorConstant (reciprocal f hn) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c⁻¹, hc.mono' ?_⟩
  intro x hx
  change ((f : X → ℂ) x)⁻¹-c⁻¹ ≠ 0 at hx
  apply subset_tsupport (fun x => (f : X → ℂ) x-c)
  change (f : X → ℂ) x-c ≠ 0
  intro h
  apply hx
  exact sub_eq_zero.mpr (congrArg Inv.inv (sub_eq_zero.mp h))

open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityPhysicalAlgebra (physical phase)

end ElasticityCoeffBounds

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds
open ElasticityPhysicalAlgebra (phase)
open ElasticityPhysicalDual

/-- Real physical coefficients and pointwise inverses are the actual smooth
coefficients in the distribution formulation. -/
def exteriorCoeff (f : Smooth) (hf : ExteriorConstant f) : Coeff := ⟨f,hf.growth⟩
def inverseCoeff (f : Smooth) (hf : ExteriorConstant f) (hn : ∀ x, (f : X → ℂ) x ≠ 0) : Coeff :=
  exteriorCoeff (reciprocal f hn) (hf.reciprocal hn)
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_TransportAlgebra
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section PhysicalRecursion
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)

def leadingRpair (θ : Fin 3 → ℂ) (lam m : A) : Amplitude A →ₗ[ℂ] (Fin 3 → A) where
  toFun a := leadingR D θ lam m a.1 a.2
  map_add' a b := by
    funext i
    simp only [leadingR,direction,Prod.fst_add,Prod.snd_add,Pi.add_apply,map_add,smul_add,
      Finset.sum_add_distrib,mul_add,add_mul]
    ring
  map_smul' c a := by
    funext i
    simp only [leadingR,direction,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Derivation.map_smul]
    simp only [Algebra.smul_def,Fin.sum_univ_three,RingHom.id_apply]
    ring

def normalPair (θ : Fin 3 → ℂ) : Amplitude A →ₗ[ℂ] A where
  toFun a := normal θ a.1
  map_add' a b := by
    simp only [normal,Prod.fst_add,Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [normal,Prod.smul_fst,Pi.smul_apply,smul_comm (θ _) c,Finset.smul_sum,RingHom.id_apply]

end PhysicalRecursion
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented
open scoped BigOperators

def thetaDerivation (θ : Fin 3 → ℂ) : Derivation ℂ Smooth Smooth := ∑ i, θ i • coord i

def thetaGamma (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0) : Smooth :=
  ∑ i, θ i • logarithmicGrad r hr i


def transportT (θ : Fin 3 → ℂ) (k r : Smooth) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) : Smooth :=
  smoothInv k hk*direction (A := Smooth) coord θ k-
    smoothInv (k+r*r) hl*direction (A := Smooth) coord θ (k+r*r)
def transportQ (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) : Fin 3 → Smooth := fun i =>
  (1/2 : ℂ) • ((r*r*smoothInv (k+r*r) hl*smoothInv k hk*direction (A := Smooth) coord θ k-
    (1/2 : ℂ) • thetaGamma θ r hr)*logarithmicGrad r hr i-
    r*r*smoothInv (k+r*r) hl*direction (A := Smooth) coord θ (logarithmicGrad r hr i))

def inverseP (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (p : Fin 3 → Smooth) : Fin 3 → Smooth :=
  fun i => smoothInv r hr*p i
def inverseS (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (p : Fin 3 → Smooth) (s : Smooth) : Smooth :=
  -r*smoothInv k hk*(2*s+∑ i,logarithmicGrad r hr i*p i)

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_ForcedTransport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

def topSource (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (H : Fin 3 → Smooth) : Fin 3 → Smooth :=
  fun i => (1/2 : ℂ) • (smoothInv r hr*H i)
def scalarSource (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (H : Fin 3 → Smooth) (K : Smooth) : Smooth :=
  -(1/4 : ℂ) • (k*smoothInv r hr*smoothInv (k+r*r) hl*K)+
    (1/4 : ℂ) • ((k-r*r)*smoothInv r hr*smoothInv (k+r*r) hl*
      ∑ i,logarithmicGrad r hr i*H i)

end ElasticityAugmented

end
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

namespace ElasticityAugmented
open Set
open scoped BigOperators

def localAmpLM (U : Set X) : Amplitude Smooth →ₗ[ℂ] Amplitude (LocalSmooth U) where
  toFun := localAmp U
  map_add' a b := by ext i <;> simp [localAmp,map_add]
  map_smul' c a := by ext i <;> simp [localAmp,map_smul]
end ElasticityAugmented
namespace ElasticityDistribution
open MeasureTheory TemperedDistribution

section
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityAugmented ElasticityRegularity
abbrev H := Lp ℂ 2 (volume : Measure X)
abbrev HV := Fin 4 → H

end
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
open ElasticityAugmented ElasticityRegularity
abbrev H3 := Fin 3 → ElasticityDistribution.H

def lpProj (i : Fin 3) : H3 →L[ℂ] Dist :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure X) 2).comp (ContinuousLinearMap.proj i)
def divZeroCLM : H3 →L[ℂ] Dist :=
  ∑ i, (LineDeriv.lineDerivOpCLM ℂ Dist (e i)).comp (lpProj i)
end ElasticityDistribution

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
open Set MeasureTheory
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply physical phase)

/-- A compact cutoff acts on every smooth amplitude, without any temperate
assumption on the amplitude itself. -/
def cut (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) : Smooth →ₗ[ℂ] S where
  toFun f := (hc.mul_right : HasCompactSupport ((χ : X → ℂ)*(f : X → ℂ))).toSchwartzMap
    ((smooth_coe χ).mul (smooth_coe f))
  map_add' f g := by
    ext x
    change (χ : X → ℂ) x*((f : X → ℂ) x+(g : X → ℂ) x)=_
    exact mul_add _ _ _
  map_smul' c f := by
    ext x
    change (χ : X → ℂ) x*(c*(f : X → ℂ) x)=c*((χ : X → ℂ) x*(f : X → ℂ) x)
    ring
@[simp] lemma cut_apply (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (f : Smooth) (x : X) :
    cut χ hc f x=(χ : X → ℂ) x*(f : X → ℂ) x := rfl

def residual0 (lam m : Smooth) (a : Amplitude Smooth) (i : Fin 3) : Smooth :=
  R coord lam m a.1 a.2 i+(lam+m)*coord i (div coord a.1-a.2)+
    coord i lam*(div coord a.1-a.2)
def residual1 (θ : Fin 3 → ℂ) (lam m : Smooth) (a : Amplitude Smooth) (i : Fin 3) : Smooth :=
  θ i • ((lam+m)*(div coord a.1-a.2))

end ElasticityCGO

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

/-- An arbitrary complex linear frequency gives a genuine global smooth
exponential on the physical real space. -/
def exponential (L : X →L[ℝ] ℂ) : Smooth := ⟨fun x => Complex.exp (L x),by
  exact (show ContDiff ℝ (⊤ : ℕ∞) (fun x => Complex.exp (L x)) from L.contDiff.cexp)⟩
end ElasticityAugmented

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform

namespace ElasticityCarleman

def e (i : Fin 3) : X := EuclideanSpace.single i 1

end ElasticityCarleman

end
end
section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply physical)
open ElasticityCarleman (phaseCLM )

/-- Actual Schwartz representatives of the exponential physical fields on a
bounded region. No temperate behavior of the exponential is assumed. -/
def expCut (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (z : Fin 3 → ℂ) (f : S) : S :=
  cut χ hc (exponential (phaseCLM z)*toSmooth f)
@[simp] lemma expCut_apply (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (z : Fin 3 → ℂ) (f : S) (x : X) :
    expCut χ hc z f x=(χ : X → ℂ) x*Complex.exp (phaseCLM z x)*f x := by
  change (χ : X → ℂ) x*(Complex.exp (phaseCLM z x)*f x)=_
  ring
end ElasticityCGO

end
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

def basis : Basis (Fin 3) ℝ X := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

def grad (f : X → ℝ) (x : X) (i : Fin 3) : ℝ := D f (basis i) x

end ElasticityRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_PhysicalCGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented

section
open scoped BigOperators

def smoothOfReal (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Smooth :=
  ⟨fun x => (f x : ℂ),Complex.ofRealCLM.contDiff.comp hf⟩
lemma smoothOfReal_apply (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    (smoothOfReal f hf : X → ℂ) x=(f x : ℂ) := rfl

def positiveRoot (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hp : ∀ x,0 < m x) : Smooth :=
  smoothOfReal (fun x => Real.sqrt (m x)) (hm.sqrt (fun x => (hp x).ne'))
lemma positiveRoot_nonzero (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hp : ∀ x,0 < m x) (x : X) :
    (positiveRoot m hm hp : X → ℂ) x≠0 := by
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp x)).ne'
lemma positiveRoot_square (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hp : ∀ x,0 < m x) :
    positiveRoot m hm hp*positiveRoot m hm hp=smoothOfReal m hm := by
  apply Subtype.ext
  funext x
  change (Real.sqrt (m x) : ℂ)*(Real.sqrt (m x) : ℂ)=(m x : ℂ)
  norm_cast
  exact Real.mul_self_sqrt (hp x).le

def smoothLog (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ x,0 < f x) : Smooth :=
  smoothOfReal (fun x => Real.log (f x)) (hf.log (fun x => (hp x).ne'))

lemma smoothOfReal_add (f g : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    smoothOfReal f hf+smoothOfReal g hg=smoothOfReal (fun x => f x+g x) (hf.add hg) := by
  apply Subtype.ext
  funext x
  exact (Complex.ofReal_add _ _).symm
lemma real_sum_nonzero (m k : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hmp : ∀ x,0 < m x) (hkp : ∀ x,0 < k x) (x : X) :
    ((smoothOfReal k hk+positiveRoot m hm hmp*positiveRoot m hm hmp : Smooth) : X → ℂ) x≠0 := by
  rw [positiveRoot_square,smoothOfReal_add,smoothOfReal_apply]
  exact Complex.ofReal_ne_zero.mpr (add_pos (hkp x) (hmp x)).ne'

lemma grad_contDiff (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ElasticityRecovery.grad f x i) :=
  ElasticityFiniteType.contDiff_D hf _
end
open Set
open scoped BigOperators
end ElasticityAugmented
namespace ElasticityCGO

open Set
open ElasticityAugmented
open ElasticityNegativeOrder (cutoff)

def fiveCutoff (R : ℝ) (hR : 1≤R) (i : Fin 5) (x : X) : ℂ :=
  (cutoff (R+(i.val : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith) x : ℂ)
lemma fiveCutoff_smooth (R : ℝ) (hR : 1≤R) (i : Fin 5) :
    ContDiff ℝ (⊤ : ℕ∞) (fiveCutoff R hR i) :=
  Complex.ofRealCLM.contDiff.comp (cutoff _ _).contDiff
lemma fiveCutoff_compact (R : ℝ) (hR : 1≤R) (i : Fin 5) :
    HasCompactSupport (fiveCutoff R hR i) :=
  (cutoff _ _).hasCompactSupport.comp_left Complex.ofReal_zero
end ElasticityCGO
namespace ElasticityCGO
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityRegularity (sobolevInjection)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityDistribution (HV Dist divd)

/-- Quantified actual physical CGO corrections on the ball, with the full
physical divergence in H1. This is a conclusion, never an input assumption. -/
def PhysicalColumn (R : ℝ) (hR : 1≤R) (α β : X) (lam m : Smooth)
    (a : ℕ → Amplitude Smooth) : Prop :=
  ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
    ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
      (∀ i,∀ᵐ x ∂(volume : Measure X),x∈Metric.ball 0 R → w i x=v i x) ∧
      (∀ i,EqOn (physical (phase h α β) lam m
        ((fun j => cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
          ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 (Metric.ball 0 R)) ∧
      (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (fiveCutoff R hR 0)
        ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
          (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
      ‖w‖≤C*h^7 ∧ ‖q‖≤C*h

end ElasticityCGO

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

def directiond (θ : Fin 3 → ℂ) (u : Dist) : Dist := ∑ i, θ i • dd i u
end
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented
abbrev AugHilbert := WithLp 2 (Fin 4 → Lp ℂ 2 (volume : Measure X))
def augEntry (i : Fin 4) : AugHilbert →L[ℂ] Dist :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure X) 2).comp
    ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => Lp ℂ 2 (volume : Measure X))).toContinuousLinearMap)

def coeffCLM (a : Coeff) : Dist →L[ℂ] Dist := smulLeftCLM ℂ (eval a)
def ddCLM (i : Fin 3) : Dist →L[ℂ] Dist := LineDeriv.lineDerivOpCLM ℂ Dist (e i)
def sdCLM (z : Fin 3 → ℂ) (i : Fin 3) : Dist →L[ℂ] Dist :=
  ddCLM i+z i • ContinuousLinearMap.id ℂ Dist
def lapdCLM (z : Fin 3 → ℂ) : Dist →L[ℂ] Dist := ∑ i, (sdCLM z i).comp (sdCLM z i)
def directionCLM (θ : Fin 3 → ℂ) : Dist →L[ℂ] Dist := ∑ i, θ i • ddCLM i
def divergenceCLM (z : Fin 3 → ℂ) : AugHilbert →L[ℂ] Dist := ∑ i, (sdCLM z i).comp (augEntry i.succ)
end ElasticityDistribution
namespace ElasticityCGO

section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology BigOperators ENNReal
open ElasticityAugmented
open ElasticityBessel (L2 norm2 J)
open ElasticityNegativeOrder (mult )
open ElasticityDistribution (AugHilbert)

def augEmbed : (Fin 4 → S) →ₗ[ℂ] AugHilbert where
  toFun u := WithLp.toLp 2 (fun i => L2 (u i))
  map_add' u v := by apply PiLp.ext; intro i; exact map_add L2 _ _
  map_smul' c u := by apply PiLp.ext; intro i; exact map_smul L2 _ _

end
open Set MeasureTheory Filter
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityBessel (L2 norm2)
open ElasticityNegativeOrder (mult )
open ElasticityPhysicalAlgebra (phase physical)

def localizedFormal (R : ℝ) (hR : 1≤R) (h : ℂ) (a : ℕ → Amplitude Smooth)
    (g : _root_.OAI.ElasticityAugmented.X → ℂ) : Fin 3 → S := fun i => mult g
  (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
    ((truncation h 8 a).1 i))

def localizedLeading (R : ℝ) (hR : 1≤R) (a : ℕ → Amplitude Smooth)
    (g : _root_.OAI.ElasticityAugmented.X → ℂ) : Fin 4 → S := Fin.cons
  (mult g (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0) (a 0).2)+
    ∑ j,mult (fun x => fderiv ℝ g x (e j))
      (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0) ((a 0).1 j)))
  (fun j => mult g (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩
    (fiveCutoff_compact R hR 0) ((a 0).1 j)))

end ElasticityCGO

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

section
open scoped SchwartzMap LineDeriv ENNReal
open ElasticityRegularity

abbrev L2Space := Lp ℂ 2 (volume : Measure X)

def compactLpMul (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (u : L2Space) : L2Space :=
  (compact_bounded_multiplier hg hc).toLp g • u

end
open scoped SchwartzMap LineDeriv ENNReal BigOperators
open ElasticityRegularity
end ElasticityDistribution
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Conic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]
def smoothEval (x : X) : Smooth →+* ℂ :=
  (Pi.evalRingHom (fun _ : X => ℂ) x).comp Smooth.val.toRingHom
/-- Entrywise evaluation is an honest matrix ring homomorphism. -/
def matrixEval (x : X) : Matrix n n Smooth →+* Matrix n n ℂ :=
  (smoothEval x).mapMatrix
@[simp] lemma matrixEval_apply (x : X) (A : Matrix n n Smooth) (i j : n) :
    matrixEval x A i j=(A i j : X → ℂ) x := rfl

def matrixD (θ : Fin 3 → ℂ) (A : Matrix n n Smooth) : Matrix n n Smooth :=
  fun i j => thetaDerivation θ (A i j)
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

def chartMatrix (b : Bool) (z : ℂ) (T : Smooth) (Q : Fin 3 → Smooth) : Matrix (Fin 3) (Fin 3) Smooth :=
  !![0,0,(chartZ₀ b z) • 1; 0,0,(chartZ₁ b z) • 1;
    (∑ i,h₁ (chartZ₀ b z) (chartZ₁ b z) i • Q i),
    (∑ i,h₂ (chartZ₀ b z) (chartZ₁ b z) i • Q i),T]
end ElasticityConic

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Holomorphy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

structure JointHolomorphic (f : X × ℂ → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  holo : ∀ x,Differentiable ℂ (fun z => f (x,z))
end ElasticityConic

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

def diagonalGauge (d : n → ℂ) (A : Matrix n n Smooth) : Matrix n n Smooth :=
  fun i j => ((d i)⁻¹*d j) • A i j
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

def physicalChartMatrix (b : Bool) (z : ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) : Matrix (Fin 3) (Fin 3) Smooth :=
  chartMatrix b z (transportT (chartTheta b z) k r hk hl)
    (transportQ (chartTheta b z) k r hr hk hl)

end ElasticityConic

end
end

end OAI
end


