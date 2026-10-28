-- Prove2me | Definitions.Def_OAIQ6El001
-- name    : OAIQ6El001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T10:18:13.116464+00:00
-- url     : https://prove2.me/theorems/7f98216b-8362-411b-8d68-0d0d8114102e
-- title:
--   Definitions bundle OAIQ6El001 of the split of OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 230 declarations of OpenAI's Lean: 177 definitions, 1 inductive type or structure and 52 theorems. The definitions and types are `OAI.ElasticityAugmented.shifted`, `OAI.ElasticityAugmented.truncation`, `OAI.ElasticityBoundary.chartTransfer`, `OAI.ElasticityBoundaryActualTower.amplitude`, `OAI.ElasticityBoundaryChainRule.Y`, `OAI.ElasticityBoundaryChainRule.hess`, `OAI.ElasticityBoundaryChainRule.jac`, `OAI.ElasticityBoundaryChartMass.I`, `OAI.ElasticityBoundaryChartMass.X`, `OAI.ElasticityBoundaryChartMass.inverseMix`, `OAI.ElasticityBoundaryChartOperator.I`, `OAI.ElasticityBoundaryChartOperator.X`, `OAI.ElasticityBoundaryChartOperator.Y`, `OAI.ElasticityBoundaryChartOperator.basis`, `OAI.ElasticityBoundaryChartOperator.chartPrincipal`, `OAI.ElasticityBoundaryCompactMatrix.I`, `OAI.ElasticityBoundaryCompactMatrix.X`, `OAI.ElasticityBoundaryCompactMatrix.row`, `OAI.ElasticityBoundaryCutoffBound.Y`, `OAI.ElasticityBoundaryCutoffLayer.Y`, `OAI.ElasticityBoundaryCutoffLayer.cutoffCorrection`, `OAI.ElasticityBoundaryCutoffLayer.cutoffLayer`, `OAI.ElasticityBoundaryCutoffLayer.cutoffScaled`, `OAI.ElasticityBoundaryCutoffParametrix.Y`, `OAI.ElasticityBoundaryCutoffParametrix.firstScaled`, `OAI.ElasticityBoundaryDensityPull.I`, `OAI.ElasticityBoundaryDensityPull.X`, `OAI.ElasticityBoundaryDensityPull.Y`, `OAI.ElasticityBoundaryDensityPull.pullMatrix`, `OAI.ElasticityBoundaryDensityPull.pullTensor`, `OAI.ElasticityBoundaryEnergyLimit.Y`, `OAI.ElasticityBoundaryEnergyLimit.mixedScaled`, `OAI.ElasticityBoundaryForceSupport.I`, `OAI.ElasticityBoundaryForceSupport.X`, `OAI.ElasticityBoundaryForceSupport.Y`, `OAI.ElasticityBoundaryFrameInverse.I`, `OAI.ElasticityBoundaryFrameInverse.X`, `OAI.ElasticityBoundaryFrameOperator.I`, `OAI.ElasticityBoundaryFrameOperator.mix`, `OAI.ElasticityBoundaryFrameOperator.mixedLower` and 138 more.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: `Elasticity_Augmented`, `Elasticity_Bessel`, `Elasticity_BoundaryCalculus`, `Elasticity_BoundaryCharts`, `Elasticity_BoundaryData`, `Elasticity_BoundaryEnergy`, `Elasticity_BoundaryJets`, `Elasticity_BoundaryLayers`, `Elasticity_BoundaryPackets`, `Elasticity_BoundaryParametrix`, `Elasticity_BoundarySymbols`, `Elasticity_BoundaryValues`, `Elasticity_Recovery`, `Elasticity_TransportAlgebra`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ6El004` and `OAIQ6El005`; the statements `OAI_ElasticityBoundaryChartMass_chart_frame_mass_bound`, `OAI.ElasticityBoundaryCutoffLayer.correction_order_bound`, `OAI.ElasticityBoundaryCutoffLayer.strong_cutoff_scale`, `OAI.ElasticityBoundaryCutoffParametrix.finite_cutoff_layer`, `OAI.ElasticityBoundaryCutoffParametrix.first_scaled_identity`, `OAI.ElasticityBoundaryEnergyLimit.mixed_scaled_limit`, `OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass`, `OAI.ElasticityBoundaryMVTower.triangular_amplitudes`, `OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit`, `OAI_ElasticityBoundaryOrderBound_OrderBound_square_mass`, `OAI.ElasticityBoundaryPacketMass.cutoff_value_bound`, `OAI.ElasticityBoundaryPacket.Setup.boundary_normal_step`, `OAI_ElasticityBoundaryPacket_Setup_chart_full_step`, `OAI.ElasticityBoundaryPacket.Setup.extract_normal`, `OAI.ElasticityBoundaryPacket.Setup.field_gradient_mass`, `OAI.ElasticityBoundaryPacket.boundary_jets_global`, `OAI.ElasticityBoundaryPacket.boundary_values_global` and `OAI.ElasticityBoundaryPacket.pair_separates`; the proofs of `OAI_ElasticityBoundaryChartMass_chart_frame_mass_bound`, `OAI.ElasticityBoundaryCutoffLayer.correction_order_bound`, `OAI.ElasticityBoundaryCutoffLayer.strong_cutoff_scale`, `OAI.ElasticityBoundaryCutoffParametrix.first_scaled_identity`, `OAI.ElasticityBoundaryEnergyLimit.mixed_scaled_limit`, `OAI.ElasticityBoundaryMixedScaling.mixedEnergy_limit`, `OAI_ElasticityBoundaryOrderBound_OrderBound_square_mass`, `OAI.ElasticityBoundaryPacketMass.cutoff_value_bound`, `OAI.ElasticityBoundaryPacket.Setup.boundary_normal_step`, `OAI_ElasticityBoundaryPacket_Setup_chart_full_step`, `OAI.ElasticityBoundaryPacket.Setup.field_gradient_mass`, `OAI.ElasticityBoundaryPacket.boundary_jets_global` and `OAI.ElasticityBoundaryPacket.boundary_values_global`.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact differential-algebra identities of the physical and normalized
augmented elasticity systems. Smooth derivatives are constructed below;
commutation and Leibniz are proved, not postulated for the physical operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

/-- A complex constant phase shifts an actual coordinate derivative. -/
def shifted (z : ι → ℂ) (i : ι) : A →ₗ[ℂ] A :=
  (D i).toLinearMap + z i • LinearMap.id

end CovariantAlgebra

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Bessel
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
abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev Test := SchwartzMap X ℂ

def d (v : X) : Test →ₗ[ℂ] Test := (lineDerivOpCLM ℂ Test v).toLinearMap

@[simp] lemma d_apply (v : X) (f : Test) (z : X) :
    (d v f : X → ℂ) z = fderiv ℝ (f : X → ℂ) z v := rfl

def qCLM : X →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj 0)

@[simp] lemma qCLM_apply (x : X) : qCLM x = (x 0 : ℂ) := rfl

end ElasticitySchwartzCarleman

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
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
abbrev Y := Fin 3 → ℝ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jac (ψ : E → Y) (v : E) (α : Fin 3) (x : E) : ℝ := fderiv ℝ ψ x v α

def hess (ψ : E → Y) (v w : E) (α : Fin 3) (x : E) : ℝ :=
  fderiv ℝ (jac ψ w α) x v

end ElasticityBoundaryChainRule

end
end
section
/-! Literal smooth polynomial amplitudes in boundary coordinates, including
actual Frechet derivatives and polynomial growth. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace ElasticityBoundaryMVCalculus
abbrev Y := Fin 3 → ℝ
abbrev MP := MvPolynomial (Fin 3) ℂ

def complexCoord (i : Fin 3) : Y →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp] lemma complexCoord_apply (i : Fin 3) (y : Y) : complexCoord i y=(y i : ℂ) := rfl

def value (p : MP) (y : Y) : ℂ := eval (fun i => (y i : ℂ)) p

@[simp] lemma value_C (c : ℂ) (y : Y) : value (C c) y=c := by simp [value]
@[simp] lemma value_X (i : Fin 3) (y : Y) : value (X i) y=(y i : ℂ) := by simp [value]
@[simp] lemma value_zero (y : Y) : value 0 y=0 := by simp [value]
@[simp] lemma value_one (y : Y) : value 1 y=1 := by simp [value]
@[simp] lemma value_add (p q : MP) (y : Y) : value (p+q) y=value p y+value q y := by simp [value]
@[simp] lemma value_sub (p q : MP) (y : Y) : value (p-q) y=value p y-value q y := by simp [value]
@[simp] lemma value_mul (p q : MP) (y : Y) : value (p*q) y=value p y*value q y := by simp [value]
@[simp] lemma value_smul (c : ℂ) (p : MP) (y : Y) : value (c • p) y=c*value p y := by
  simp [value, smul_eq_C_mul]

lemma value_C_fn (c : ℂ) : value (C c) = (fun _ => c) := funext (value_C c)
lemma value_add_fn (p q : MP) : value (p+q)=value p+value q := funext (value_add p q)
lemma value_mul_fn (p q : MP) : value (p*q)=value p*value q := funext (value_mul p q)
lemma value_X_fn (i : Fin 3) : value (X i)=complexCoord i := funext (value_X i)

lemma smooth_value (p : MP) : ContDiff ℝ (⊤ : ℕ∞) (value p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [value_C_fn]; exact contDiff_const
  | add p q hp hq => rw [value_add_fn]; exact hp.add hq
  | mul_X p i hp => rw [value_mul_fn, value_X_fn]; exact hp.mul (complexCoord i).contDiff

def differential (p : MP) (y : Y) : Y →L[ℝ] ℂ :=
  ∑ i, value (pderiv i p) y • complexCoord i

@[simp] lemma differential_C (c : ℂ) (y : Y) : differential (C c) y=0 := by
  apply ContinuousLinearMap.ext
  intro z
  simp [differential, sum_apply, smul_apply]

@[simp] lemma differential_add (p q : MP) (y : Y) :
    differential (p+q) y=differential p y+differential q y := by
  apply ContinuousLinearMap.ext
  intro z
  simp [differential, sum_apply, smul_apply, add_mul, Finset.sum_add_distrib]

end ElasticityBoundaryMVCalculus

end
end
section
/-! Exact anisotropic boundary scaling, retaining the physical dimension-three
Jacobian δ⁴. No asymptotic change-of-variable formula is postulated. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryScaling
abbrev Y := Fin 3 → ℝ

def scaleFactor (δ : ℝ) (i : Fin 3) : ℝ := if i=2 then δ^2 else δ

def scale (δ : ℝ) : Y →L[ℝ] Y :=
  ContinuousLinearMap.pi (fun i =>
    (scaleFactor δ i • ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.proj i))

@[simp] lemma scale_apply (δ : ℝ) (y : Y) (i : Fin 3) :
    scale δ y i = scaleFactor δ i * y i := rfl

@[simp] lemma scale_one (y : Y) : scale 1 y = y := by
  ext i
  simp [scaleFactor]

end ElasticityBoundaryScaling

end
end
section
/-! Integrable polynomial majorants for the physical anisotropic boundary-layer
profiles. The decay and all moments are proved, not assumed symbol bounds. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryWeights
abbrev Y := Fin 3 → ℝ

def factor (b : ℝ) (i : Fin 3) (t : ℝ) : ℝ :=
  if i = 2 then (Ioi (0 : ℝ)).indicator (fun s => Real.exp (-b*s)) t
  else Real.exp (-b*t^2)

def weight (b : ℝ) (y : Y) : ℝ := ∏ i, factor b i (y i)

end ElasticityBoundaryWeights

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundarySymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal anisotropic oscillatory Gaussian boundary profiles, with actual
Frechet derivatives.  The small parameter is never assigned a symbolic DN map. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryProfile
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights
-- All coordinate spaces here carry the standard finite-product Euclidean topology.
abbrev Y := Fin 3 → ℝ

def phase (δ : ℝ) : MP := C (Complex.I / (δ : ℂ))*X 0-X 2-((X 0)^2+(X 1)^2)
def envelope (δ : ℝ) (y : Y) : ℂ := Complex.exp (value (phase δ) y)
def profile (δ : ℝ) (p : MP) (y : Y) : ℂ := envelope δ y*value p y

def conjugateDerivative (δ : ℝ) (j : Fin 3) : MP →ₗ[ℂ] MP :=
  (pderiv j).toLinearMap + LinearMap.mulLeft ℂ (pderiv j (phase δ))

lemma smooth_profile (δ : ℝ) (p : MP) : ContDiff ℝ (⊤ : ℕ∞) (profile δ p) :=
  ((smooth_value (phase δ)).cexp).mul (smooth_value p)

/-- Polynomial dependence on the concentration parameter after multiplying the
physical derivative by delta squared. -/
def D (δ : ℝ) (j : Fin 3) : MP →ₗ[ℂ] MP :=
  if j=0 then Complex.I • LinearMap.id + (δ:ℂ) •
    ((pderiv 0).toLinearMap-(2:ℂ) • LinearMap.mulLeft ℂ (X 0))
  else if j=1 then (δ:ℂ) • ((pderiv 1).toLinearMap-(2:ℂ) • LinearMap.mulLeft ℂ (X 1))
  else (pderiv 2).toLinearMap-LinearMap.id

def physicalProfile (δ : ℝ) (p : MP) (z : Y) : ℂ := profile δ p (scale δ⁻¹ z)

lemma smooth_physicalProfile (δ : ℝ) (p : MP) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalProfile δ p) :=
  (smooth_profile δ p).comp (scale δ⁻¹).contDiff

end ElasticityBoundaryProfile

end
end
section
/-! Coefficientwise linear differential operators in a genuine finite
parameter polynomial. Used to construct, not postulate, Taylor transport
coefficients of the physical boundary layer. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryParameter
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

def coeffMap (T : A →ₗ[ℂ] B) : Polynomial A →ₗ[ℂ] Polynomial B :=
  (PolynomialModule.equivPolynomial (R := ℂ)).toLinearMap.comp
    ((PolynomialModule.map ℂ T).comp
      (PolynomialModule.equivPolynomial (R := ℂ)).symm.toLinearMap)

@[simp] lemma coeffMap_monomial (T : A →ₗ[ℂ] B) (n : ℕ) (a : A) :
    coeffMap T (Polynomial.monomial n a)=Polynomial.monomial n (T a) := by
  simp [coeffMap]

@[simp] lemma coeffMap_coeff (T : A →ₗ[ℂ] B) (q : Polynomial A) (n : ℕ) :
    (coeffMap T q).coeff n=T (q.coeff n) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial k a =>
      rw [coeffMap_monomial]
      simp only [Polynomial.coeff_monomial]
      split_ifs <;> simp

/-- The parameter-independent and linear parts of the actual scaled derivative. -/
def E₀ (j : Fin 3) : MP →ₗ[ℂ] MP :=
  if j=0 then Complex.I • LinearMap.id else if j=1 then 0
  else (pderiv 2).toLinearMap-LinearMap.id

def E₁ (j : Fin 3) : MP →ₗ[ℂ] MP :=
  if j=0 then (pderiv 0).toLinearMap-(2:ℂ) • LinearMap.mulLeft ℂ (X 0)
  else if j=1 then (pderiv 1).toLinearMap-(2:ℂ) • LinearMap.mulLeft ℂ (X 1) else 0

def PD (j : Fin 3) : Polynomial MP →ₗ[ℂ] Polynomial MP :=
  coeffMap (E₀ j) + (LinearMap.mulLeft ℂ Polynomial.X).comp (coeffMap (E₁ j))

end ElasticityBoundaryParameter

end
end
section
/-! Flat-boundary calculation for the missing DN-to-all-jets step.
This is ONLY the constant-coefficient principal boundary symbol, not the
boundary localization theorem. Frequency is the unit first tangential
covector, the domain is t>0, and the outward normal is -e₃.
-/
noncomputable section
open scoped Matrix
namespace ElasticityBoundarySymbol
abbrev F := Fin 3 → ℂ

def slope (l m : ℂ) (f : F) : F :=
  ![-((l+m)/(l+3*m))*(f 0+Complex.I*f 2),0,
    ((l+m)/(l+3*m))*(f 2-Complex.I*f 0)]

end ElasticityBoundarySymbol

end
end
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
abbrev P := Polynomial ℂ

/-- Differentiation of the polynomial amplitude after factoring out exp(-t). -/
def shiftedDerivative (c : ℂ) : P →ₗ[ℂ] P :=
  Polynomial.derivative - c • LinearMap.id

@[simp] lemma shiftedDerivative_apply (c : ℂ) (p : P) :
    shiftedDerivative c p = derivative p - c • p := rfl

/-- The amplitude operator for d²/dt²-1 on exp(-t) times a polynomial. -/
def laplaceAmplitude : P →ₗ[ℂ] P :=
  Polynomial.derivative.comp (shiftedDerivative 2)

end ElasticityBoundarySymbol

end
end
section
/-! Zero-Dirichlet inversion, with a literal exponential-polynomial ODE
interpretation. This is the normal component of the boundary quasimode
recursion, not a replacement for variable-coefficient boundary localization. -/
noncomputable section
open Polynomial
namespace ElasticityBoundarySymbol

def homogeneousPolynomial (l m : ℂ) (f : F) (i : Fin 3) : P :=
  C (f i) + X * C (slope l m f i)

@[simp] lemma homogeneousPolynomial_boundary (l m : ℂ) (f : F) (i : Fin 3) :
    (homogeneousPolynomial l m f i).eval 0 = f i := by
  simp [homogeneousPolynomial]

end ElasticityBoundarySymbol

end
end
section
/-! The normal inverse on literal multivariable polynomial amplitudes.  No
identification of formal symbols with physical derivatives is assumed: the
normal operator here consists of the actual formal partial derivatives, whose
evaluations agree with the corresponding Fréchet derivatives. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryMVNormal
open MvPolynomial ElasticityBoundarySymbol ElasticityBoundaryMVCalculus
abbrev W := Fin 3 → MP

def d : MP →ₗ[ℂ] MP := (pderiv 2).toLinearMap
def shift : MP →ₗ[ℂ] MP := d - LinearMap.id
def lap : MP →ₗ[ℂ] MP := d.comp (d - (2:ℂ) • LinearMap.id)

@[simp] lemma d_apply (p : MP) : d p=pderiv 2 p := rfl
@[simp] lemma shift_apply (p : MP) : shift p=pderiv 2 p-p := rfl

def normal (l m : ℂ) : W →ₗ[ℂ] W :=
  LinearMap.pi
    ![m • lap.comp (LinearMap.proj 0) - (l+m) • LinearMap.proj 0 +
        (Complex.I*(l+m)) • shift.comp (LinearMap.proj 2),
      m • lap.comp (LinearMap.proj 1),
      (Complex.I*(l+m)) • shift.comp (LinearMap.proj 0) +
        (l+2*m) • lap.comp (LinearMap.proj 2) + (l+m) • LinearMap.proj 2]

def lift : P →ₐ[ℂ] MP := Polynomial.aeval (X 2)

@[simp] lemma lift_C (c : ℂ) : lift (Polynomial.C c)=C c := by simp [lift]
@[simp] lemma lift_X : lift Polynomial.X=X 2 := by simp [lift]

/-- The actual restriction of a polynomial to the flat boundary. -/
def boundaryRing : MP →ₐ[ℂ] MP := MvPolynomial.aeval (fun i => if i=2 then 0 else X i)
def boundary : W →ₗ[ℂ] W := LinearMap.pi (fun i => boundaryRing.toLinearMap.comp (LinearMap.proj i))
@[simp] lemma boundary_apply (p : W) (i : Fin 3) : boundary p i=boundaryRing (p i) := rfl

end ElasticityBoundaryMVNormal

end
end
section
/-! Actual second derivatives and the literal frozen elasticity operator on
boundary profiles. The coefficients below act on physical tensor indices. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryLayerOperator
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile ElasticityBoundaryMVNormal
abbrev Y := Fin 3 → ℝ

/-- The isotropic elasticity tensor in fixed (orthonormal) coordinates. -/
def elasticityTensor (l m : ℂ) (i α j β : Fin 3) : ℂ :=
  l*(if i=α then 1 else 0)*(if j=β then 1 else 0) +
  m*((if i=j then 1 else 0)*(if α=β then 1 else 0) +
    (if i=β then 1 else 0)*(if α=j then 1 else 0))

/-- A principal tensor acts on actual polynomial conjugated derivatives. -/
def principal (a : Fin 3 → Fin 3 → Fin 3 → Fin 3 → MP) (δ : ℝ) : W →ₗ[ℂ] W :=
  LinearMap.pi (fun i => ∑ α, ∑ j, ∑ β,
    (LinearMap.mulLeft ℂ (a i α j β)).comp ((D δ α).comp ((D δ β).comp (LinearMap.proj j))))

end ElasticityBoundaryLayerOperator

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

abbrev Tensor := Fin 3 → Fin 3 → Fin 3 → Fin 3 → Polynomial MP
abbrev Lower := Fin 3 → Fin 3 → Fin 3 → Polynomial MP

def unpack (i : Fin 3) : Polynomial W →ₗ[ℂ] Polynomial MP := coeffMap (LinearMap.proj i)

end ElasticityBoundaryTensorSeries

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
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

def line (z : E) : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight z

end ElasticityBoundaryTaylor

end
end
section
/-! Literal polynomial representations of the actual Frechet Taylor jets and
of their anisotropic parameter dependence. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryTaylorPolynomial
open MvPolynomial ElasticityBoundaryTaylor ElasticityBoundaryMVCalculus ElasticityBoundaryScaling
abbrev Y := Fin 3 → ℝ

/-- The diagonal of a real multilinear map, expanded in the fixed coordinates. -/
def diagonal {n : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Y) ℂ) : MP :=
  ∑ j : Fin n → Fin 3, C (T (fun k => Pi.single (j k) 1)) * ∏ k, X (j k)

def taylor (f : Y → ℂ) (n : ℕ) : MP :=
  ∑ k ∈ Finset.range (n+1), ((k.factorial : ℂ)⁻¹) • diagonal (iteratedFDeriv ℝ k f 0)

def weightOrder (i : Fin 3) : ℕ := if i=2 then 2 else 1

def parameterize : MP →ₐ[ℂ] Polynomial MP :=
  MvPolynomial.aeval (fun i => Polynomial.C (X i) * Polynomial.X^(weightOrder i))

end ElasticityBoundaryTaylorPolynomial

end
end
section
/-! Corrected amplitudes for the literal Taylor tensor differential operator.
The operator coefficients are computed, rather than a formal sequence assumed. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryActualTower
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryTensorSeries ElasticityBoundaryTaylorPolynomial

def amplitude (p : ℕ → W) (N : ℕ) : Polynomial W :=
  ∑ n ∈ Finset.range (N+1), Polynomial.monomial n (p n)

end ElasticityBoundaryActualTower

end
end
section
/-! Honest L2 bounds and exact change of variables for physical boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryProfileBounds
open ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights
  ElasticityBoundaryProfile
abbrev Y := Fin 3 → ℝ

def halfspace : Set Y := {y | 0<y 2}

end ElasticityBoundaryProfileBounds

end
end
section
/-! Uniform true L2/H1 estimates for finite corrected boundary amplitudes. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryParameterBounds
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryWeights ElasticityBoundaryParameter
abbrev Y := Fin 3 → ℝ

def atParameter (q : Polynomial MP) (δ : ℝ) : MP := q.eval (C (δ:ℂ))

end ElasticityBoundaryParameterBounds

end
end
section
/-! Uniform polynomial-growth estimates for the actual smooth coefficient
Taylor errors, multiplied by a finite amplitude family. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryOrderBound
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryParameterBounds
  ElasticityBoundaryTaylorPolynomial ElasticityBoundaryTaylor ElasticityBoundaryScaling
  ElasticityBoundaryProfileBounds ElasticityBoundaryWeights
abbrev Y := Fin 3 → ℝ

/-- A quantitative bound, with constants independent of concentration and
of the half-space point. The polynomial spatial weight is integrable against
our Gaussian/normal exponential. -/
def OrderBound (f : ℝ → Y → ℂ) (k : ℕ) : Prop :=
  ∃ A : ℝ, 0≤A ∧ ∃ n : ℕ, ∀ δ : ℝ, 0<δ → δ≤1 → ∀ y : Y,
    ‖f δ y‖ ≤ A*δ^k*(1+‖y‖)^n

end ElasticityBoundaryOrderBound

end
end
section
/-! The genuine smooth variable-coefficient operator applied to constructed
finite boundary amplitudes. The remaining error is estimated, not discarded. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundarySmoothOperator
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryTaylorPolynomial ElasticityBoundaryOrderBound
  ElasticityBoundaryScaling ElasticityBoundaryLayerOperator ElasticityBoundaryWeights
abbrev Y := Fin 3 → ℝ
abbrev SmoothTensor := Fin 3 → Fin 3 → Fin 3 → Fin 3 → Y → ℂ
abbrev SmoothLower := Fin 3 → Fin 3 → Fin 3 → Y → ℂ

def tensorTaylor (a : SmoothTensor) (N : ℕ) : Tensor :=
  fun i α j β => parameterize (taylor (a i α j β) N)
def lowerTaylor (b : SmoothLower) (N : ℕ) : Lower :=
  fun i j β => parameterize (taylor (b i j β) N)

/-- The scaled amplitude of the literal differential expression; the PD
operators are already identified with true scaled first/second derivatives. -/
def scaledOperator (a : SmoothTensor) (b : SmoothLower) (q : Polynomial W)
    (δ : ℝ) (i : Fin 3) (y : Y) : ℂ :=
  (∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
    value (atParameter (PD α (PD β (unpack j q))) δ) y) +
  (δ:ℂ)^2 * ∑ j, ∑ β, b i j β (scale δ y) *
    value (atParameter (PD β (unpack j q)) δ) y

def scaledError (a : SmoothTensor) (b : SmoothLower) (q : Polynomial W)
    (N : ℕ) (δ : ℝ) (i : Fin 3) (y : Y) : ℂ :=
  (∑ α, ∑ j, ∑ β, (a i α j β (scale δ y)-
    value (atParameter (tensorTaylor a N i α j β) δ) y) *
    value (atParameter (PD α (PD β (unpack j q))) δ) y) +
  (δ:ℂ)^2 * ∑ j, ∑ β, (b i j β (scale δ y)-
    value (atParameter (lowerTaylor b N i j β) δ) y) *
    value (atParameter (PD β (unpack j q)) δ) y

end ElasticityBoundarySmoothOperator

end
end
section
/-! Literal unscaled differential residuals of the constructed boundary fields.
The estimates are in the actual half-space L2 norm, not a formal series norm. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryStrongLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights
abbrev Y := Fin 3 → ℝ

def dpart (f : Y → ℂ) (j : Fin 3) (z : Y) : ℂ :=
  fderiv ℝ f z (Pi.single j 1)

def strong (a : SmoothTensor) (b : SmoothLower) (u : Fin 3 → Y → ℂ) (i : Fin 3) (z : Y) : ℂ :=
  (∑ α, ∑ j, ∑ β, a i α j β z * dpart (dpart (u j) β) α z) +
    ∑ j, ∑ β, b i j β z * dpart (u j) β z

def layer (q : Polynomial W) (δ : ℝ) (j : Fin 3) : Y → ℂ :=
  physicalProfile δ (atParameter (unpack j q) δ)

end ElasticityBoundaryStrongLayer

end
end
section
/-! True pullback of a second-order physical system. The coefficient Hessian
term is retained, and no equivalence of augmented and physical DN data is used. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryPullback
open ElasticityBoundaryChainRule ElasticityBoundarySmoothOperator ElasticityBoundaryStrongLayer
abbrev I := Fin 3
abbrev Y := Fin 3 → ℝ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev Tensor (E : Type*) := I → I → I → I → E → ℂ
abbrev Lower (E : Type*) := I → I → I → E → ℂ

def principalPull (e : I → E) (a : Tensor E) (ψ : E → Y) : Tensor E :=
  fun i α j β x => ∑ k, ∑ l, a i k j l x*(jac ψ (e k) α x:ℂ)*(jac ψ (e l) β x:ℂ)

def lowerPull (e : I → E) (a : Tensor E) (b : Lower E) (ψ : E → Y) : Lower E :=
  fun i j β x => (∑ k, ∑ l, a i k j l x*(hess ψ (e k) (e l) β x:ℂ))+
    ∑ l, b i j l x*(jac ψ (e l) β x:ℂ)

end ElasticityBoundaryPullback

end
end
section
/-! Orthogonal covariance of the literal isotropic tensor in physical
coordinates. The frame is an actual Euclidean isometry, not a gauge freedom. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryRotation
open ElasticityBoundaryLayerOperator
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

def frameMatrix (Q : X ≃ₗᵢ[ℝ] X) (i j : I) : ℂ := (Q (EuclideanSpace.single j 1) i : ℂ)

def rotateTensor (Q : I → I → ℂ) (a : I → I → I → I → ℂ) (s α r β : I) : ℂ :=
  ∑ i, ∑ k, ∑ j, ∑ l, Q i s*Q k α*a i k j l*Q j r*Q l β

def columnDot (Q : I → I → ℂ) (i j : I) : ℂ := ∑ k, Q k i*Q k j

end ElasticityBoundaryRotation

end
end
section
/-! Exact constant-frame transformation of the strong differential operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryFrameOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
abbrev I := Fin 3
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def mix (Q : I → I → ℂ) (u : I → E → ℂ) (i : I) (x : E) : ℂ := ∑ j, Q i j*u j x

def mixedTensor (R S : I → I → ℂ) (a : Tensor E) : Tensor E :=
  fun s k r l x => ∑ i, ∑ j, R s i*a i k j l x*S j r

def mixedLower (R S : I → I → ℂ) (b : Lower E) : Lower E :=
  fun s r l x => ∑ i, ∑ j, R s i*b i j l x*S j r

lemma smooth_mix (Q : I → I → ℂ) (u : I → E → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (mix Q u i) := by
  exact ContDiff.sum (fun j _ => contDiff_const.mul (hu j))

end ElasticityBoundaryFrameOperator

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
abbrev I := Fin 3
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coeff (l m : E → ℂ) : Tensor E := fun i k j r x => elasticityTensor (l x) (m x) i k j r

end ElasticityBoundaryPhysicalStrong

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCharts
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
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

def basis (i : I) : X := EuclideanSpace.single i 1

def chartPrincipal (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) (ψ : X → Y)
    (l m : X → ℂ) : SmoothTensor :=
  fun s α r β y => principalPull basis
    (mixedTensor (fun s i => frameMatrix Q i s) (frameMatrix Q) (coeff l m)) ψ s α r β (Φ y)

end ElasticityBoundaryChartOperator

end
end
section
/-! Smooth compact extensions of genuine local maps, in arbitrary finite
 dimensional physical and coordinate spaces. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ElasticityBoundary
variable {E : Type} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
lemma contDiff_cutoff_smul {U : Set E} (hU : IsOpen U) (f : E → F) (χ : E → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hs : tsupport χ⊆U) : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈U
  · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
  · have hn : x∉tsupport χ := fun hh => hx (hs hh)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

end ElasticityBoundary

end
end
section
/-! Transferring a trial supported in an honest chart produces an actual
 globally smooth compact physical field, without imposing artificial boundary
 data. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def chartTransfer (e : OpenPartialHomeomorph E E) (η : E → ℝ) (u : E → F) (x : E) : F :=
  η x • u (e.symm x)

omit [FiniteDimensional ℝ E] in
lemma smooth_chartTransfer (e : OpenPartialHomeomorph E E)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : tsupport η⊆e.target)
    {u : E → F} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (chartTransfer e η u) := by
  apply contDiff_cutoff_smul e.open_target _ η _ hη hs
  exact hu.comp_contDiffOn hi

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma chartTransfer_zero (e : OpenPartialHomeomorph E E) {η : E → ℝ}
    (hs : tsupport η⊆e.target) (u : E → F) {x : E} (hx : x∉e.target) :
    chartTransfer e η u x=0 := by
  have hn : x∉tsupport η := fun h => hx (hs h)
  simp [chartTransfer, image_eq_zero_of_notMem_tsupport hn]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma chartTransfer_support (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hs : tsupport η⊆e.target)
    {u : E → F} (hu : Function.support u⊆K) :
    Function.support (chartTransfer e η u)⊆e '' K := by
  intro x hx
  have ht : x∈e.target := by
    by_contra hn
    exact hx (chartTransfer_zero e hs u hn)
  have hn : u (e.symm x)≠0 := by
    intro hz
    exact hx (by simp [chartTransfer,hz])
  exact ⟨e.symm x,hu hn,e.right_inv ht⟩

end ElasticityBoundary

end
end
section
/-! Locality and true support control for the physical differential operator
and the compact chart transfer. These use germs, not formal coefficients. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryOperatorLocal
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryPhysicalStrong
  ElasticityBoundary
abbrev I := Fin 3

end ElasticityBoundaryOperatorLocal

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryParametrix
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
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

def lifted (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ) (i : I) (z : X) : ℂ :=
  mix (frameMatrix Q) u i z.ofLp

def transferred (e : OpenPartialHomeomorph X X) (η : X → ℝ)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ) (i : I) : X → ℂ :=
  chartTransfer e η (lifted Q u i)

lemma smooth_lifted (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (lifted Q u i) :=
  (smooth_mix (frameMatrix Q) u hu i).comp PiLp.contDiff_ofLp

lemma smooth_transferred (e : OpenPartialHomeomorph X X)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {η : X → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : tsupport η⊆e.target)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (transferred e η Q u i) :=
  smooth_chartTransfer e hi hη hs (smooth_lifted Q u hu i)

lemma support_lifted (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ) {K : Set X}
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (i : I) :
    Function.support (lifted Q u i)⊆K := by
  intro x hx
  by_contra hn
  apply hx
  change (∑ j, frameMatrix Q i j*u j x.ofLp)=0
  apply Finset.sum_eq_zero
  intro j _
  have hz : u j x.ofLp=0 := Function.notMem_support.mp (fun hh => hn (hu j hh))
  rw [hz,mul_zero]

lemma support_transferred (e : OpenPartialHomeomorph X X) {η : X → ℝ}
    (hs : tsupport η⊆e.target) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ) {K : Set X}
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (i : I) :
    Function.support (transferred e η Q u i)⊆e '' K :=
  chartTransfer_support e hs (support_lifted Q u hu i)

end ElasticityBoundaryPhysicalTransfer

end
end
section
/-! Pointwise all-order cutoff bounds. These bounds feed exactly the same
weighted-mass estimate used for the smooth coefficient Taylor error. -/
noncomputable section
open Set
namespace ElasticityBoundaryCutoffBound
open ElasticityBoundaryOrderBound ElasticityBoundaryScaling
abbrev Y := Fin 3 → ℝ

end ElasticityBoundaryCutoffBound

end
end
section
/-! Cut off actual boundary fields. The complete product-rule residual is
retained; its derivatives are flat at the concentration point. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound
abbrev Y := Fin 3 → ℝ

/-- All cutoff product terms, before taking an absolute value or norm. -/
def cutoffCorrection (a : SmoothTensor) (b : SmoothLower) (χ : Y → ℂ)
    (q : Polynomial W) (δ : ℝ) (i : Fin 3) (y : Y) : ℂ :=
  (δ:ℂ)^2 * (∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
    (dpart χ β (scale δ y)*value (atParameter (PD α (unpack j q)) δ) y+
     dpart χ α (scale δ y)*value (atParameter (PD β (unpack j q)) δ) y)) +
  (δ:ℂ)^4 * ((∑ α, ∑ j, ∑ β, a i α j β (scale δ y) *
    dpart (dpart χ β) α (scale δ y)*value (atParameter (unpack j q) δ) y)+
    ∑ j, ∑ β, b i j β (scale δ y)*dpart χ β (scale δ y)*
      value (atParameter (unpack j q) δ) y)

def cutoffScaled (a : SmoothTensor) (b : SmoothLower) (χ : Y → ℂ)
    (q : Polynomial W) (δ : ℝ) (i : Fin 3) (y : Y) : ℂ :=
  χ (scale δ y)*scaledOperator a b q δ i y+cutoffCorrection a b χ q δ i y

def cutoffLayer (χ : Y → ℂ) (q : Polynomial W) (δ : ℝ) (j : Fin 3) (z : Y) : ℂ :=
  χ z*layer q δ j z

lemma smooth_cutoffLayer {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (q : Polynomial W) (δ : ℝ) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffLayer χ q δ j) :=
  hχ.mul (smooth_physicalProfile δ _)

end ElasticityBoundaryCutoffLayer

end
end
section
/-! Compactly supported actual half-space quasimodes with arbitrary strong
residual order and uniform H1 bounds. All scalings are those of the physical
boundary layer, not a formal symbol expansion. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffParametrix
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound ElasticityBoundaryCutoffLayer
abbrev Y := Fin 3 → ℝ

/-- Amplitude of a genuine first derivative, including the cutoff derivative. -/
def firstScaled (χ : Y → ℂ) (q : Polynomial W) (δ : ℝ) (j β : Fin 3) (y : Y) : ℂ :=
  χ (scale δ y)*value (atParameter (PD β (unpack j q)) δ) y+
    (δ:ℂ)^2*dpart χ β (scale δ y)*value (atParameter (unpack j q) δ) y

end ElasticityBoundaryCutoffParametrix

end
end
section
/-! Local boundary layers for arbitrary smooth coefficients. Auxiliary compact
coefficient extensions are removed on the actual trial support; thus no
artificial compactness or global geometry assumption is imposed on a chart. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryLocalParametrix
open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer
  ElasticityBoundaryStrongLayer ElasticityBoundarySmoothOperator
  ElasticityBoundaryMVNormal ElasticityBoundaryActualTower ElasticityBoundaryLayerOperator ElasticityBoundaryProfile ElasticityBoundaryOperatorLocal
  ElasticityBoundary ElasticityBoundaryProfileBounds
abbrev I := Fin 3
abbrev Y := I → ℝ

end ElasticityBoundaryLocalParametrix

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The exact inverse derivative at normalized physical boundary charts. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryInverseGeometry
open ElasticityBoundaryChainRule ElasticityBoundaryRotation
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

end ElasticityBoundaryInverseGeometry

end
end
section
/-! Exact inversion of the fixed physical orthogonal frame, including
quantitative component control needed for the genuine residual norm. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryFrameInverse
open ElasticityBoundaryRotation ElasticityBoundaryInverseGeometry ElasticityBoundaryFrameOperator
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

end ElasticityBoundaryFrameInverse

end
end
section
/-! Support-complete physical force identification. The coordinate expression
is valid on the entire chart source, including all zero regions, and the
physical force is supported in the genuine compact image. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryForceSupport
open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryOperatorLocal
  ElasticityBoundaryLocalParametrix ElasticityBoundaryStrongLayer
  ElasticityBoundaryChartOperator ElasticityBoundaryFrameOperator
  ElasticityBoundaryFrameInverse ElasticityBoundaryRotation
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

lemma compact_image (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) : IsCompact (e '' K) :=
  hK.image_of_continuousOn (e.continuousOn.mono hs)

end ElasticityBoundaryForceSupport

end
end
section
/-! A quantitative physical L2 transfer through an honest boundary chart.
The constants are independent of trial fields and concentration parameters. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryChartMass
open ElasticityBoundaryFrameInverse
  ElasticityBoundaryFrameOperator ElasticityBoundaryRotation
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

def inverseMix (Q : X ≃ₗᵢ[ℝ] X) (g : I → X → ℂ) (i : I) (y : X) : ℂ :=
  ∑ j, frameMatrix Q i j*g j y

end ElasticityBoundaryChartMass

end
end
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
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

def principal (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X) (l m : X → ℂ) : SmoothTensor :=
  chartPrincipal Q (fun z => Φ (WithLp.toLp 2 z)) (fun z => (Ψ z).ofLp) l m

end ElasticityBoundaryPhysicalMass

end
end
section
/-! Uniform compactly supported matrix-multiplier mass estimates, for the
true coordinate Jacobian acting on first derivatives of boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryCompactMatrix
open ElasticityBoundaryChartMass ElasticityBoundaryFrameInverse
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

def row (a : I → I → X → ℂ) (r : I) (v : I → X → ℂ) (y : X) : ℂ := ∑ j, a r j y*v j y

end ElasticityBoundaryCompactMatrix

end
end
section
/-! Literal first derivatives of the compact physical trial and their exact
rotated chart expression. No trace reconstruction is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryGradientTransfer
open ElasticityBoundaryPhysicalMass ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryChartMass ElasticityBoundaryChartOperator ElasticityBoundaryFrameOperator
  ElasticityBoundaryRotation ElasticityBoundaryFrameInverse ElasticityBoundaryOperatorLocal
  ElasticityBoundaryChainRule ElasticityBoundaryStrongLayer ElasticityBoundaryCompactMatrix
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

def jacobian (Φ Ψ : X → X) (d α : I) (y : X) : ℂ :=
  (jac (fun z => (Ψ z).ofLp) (basis d) α (Φ y):ℂ)

end ElasticityBoundaryGradientTransfer

end
end
section
/-! Uniform physical H1 control through the honest chart. Both the coordinate
Jacobian and the orthogonal output frame are accounted for. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryGradientMass
open ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChartMass ElasticityBoundaryCompactMatrix ElasticityBoundaryForceSupport
  ElasticityBoundaryFrameOperator ElasticityBoundaryRotation ElasticityBoundaryChainRule
  ElasticityBoundaryStrongLayer ElasticityBoundaryChartOperator
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

end ElasticityBoundaryGradientMass

end
end
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open ElasticityBoundary
  ElasticityBoundaryInverseGeometry ElasticityBoundaryGradientTransfer
  ElasticityBoundaryPhysicalMass ElasticityBoundaryChartOperator
  ElasticityBoundaryLayerOperator ElasticityBoundaryPhysicalTransfer
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

structure Setup (Ω : Set X) (x : X) where
  e : OpenPartialHomeomorph X X
  Q : X ≃ₗᵢ[ℝ] X
  at_zero : (0:X)∈e.source
  center : e 0=x
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) e e.source
  inverse_smooth : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target
  deriv : HasFDerivAt e Q.toContinuousLinearEquiv.toContinuousLinearMap 0
  inside : ∀ y∈e.source, e y∈Ω ↔ 0<y 2
  K : Set X
  compact : IsCompact K
  source : K⊆e.source
  cutoff : Y → ℂ
  cutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_one : cutoff =ᶠ[𝓝 (0:Y)] fun _ => 1
  cutoff_support : Function.support (fun z : X => cutoff z.ofLp)⊆K
  η : X → ℝ
  η_smooth : ContDiff ℝ (⊤ : ℕ∞) η
  η_compact : HasCompactSupport η
  η_support : tsupport η⊆e.target
  η_one : ∀ z∈e '' K, η z=1
  Φ : X → X
  Ψ : X → X
  Φ_smooth : ContDiff ℝ (⊤ : ℕ∞) Φ
  Ψ_smooth : ContDiff ℝ (⊤ : ℕ∞) Ψ
  Φ_germ : ∀ y∈K, Φ =ᶠ[𝓝 y] e
  Ψ_germ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm

end ElasticityBoundaryPacket

end
end
section
/-! Value mass and the exact identification of Euclidean and product Lebesgue
measure used by the physical boundary packets. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryPacketMass
open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer
  ElasticityBoundaryProfile ElasticityBoundaryParameter ElasticityBoundaryParameterBounds
  ElasticityBoundaryOrderBound ElasticityBoundaryCutoffBound ElasticityBoundaryScaling
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryMVCalculus
  ElasticityBoundaryTensorSeries ElasticityBoundaryProfileBounds ElasticityBoundaryMVNormal ElasticityBoundaryActualTower
abbrev I := Fin 3
abbrev Y := I → ℝ
abbrev X := EuclideanSpace ℝ I

def H : Set X := {y | 0<y 2}

end ElasticityBoundaryPacketMass

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryData
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
open ElasticityBoundaryChainRule ElasticityBoundaryPhysicalStrong
  ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalTransfer
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

end ElasticityBoundaryProjectedStress
/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryResidualMass
open ElasticityBoundaryProjectedStress ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalStrong ElasticityBoundaryChainRule
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I

end ElasticityBoundaryResidualMass

end
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryTrialMass
open ElasticityBoundaryResidualMass ElasticityBoundaryChainRule
abbrev I := Fin 3

end ElasticityBoundaryTrialMass

end
namespace ElasticityBoundaryPacket
/-! Actual smooth compact physical fields selected from the curved boundary
parametrix, on an arbitrary honest smooth domain. -/
open Set MeasureTheory Filter
open scoped Topology BigOperators
open ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryCutoffLayer ElasticityBoundaryCutoffParametrix ElasticityBoundaryPacketMass
  ElasticityBoundaryGradientMass ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryStrongLayer
  ElasticityBoundaryLocalParametrix ElasticityBoundaryMVNormal ElasticityBoundaryActualTower
  ElasticityBoundaryProfileBounds ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

def Setup.field (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) : I → X → ℂ :=
  transferred s.e s.η s.Q (cutoffLayer s.cutoff q δ)

lemma Setup.cutoff_layer_support (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) (j : I) :
    Function.support (fun y : X => cutoffLayer s.cutoff q δ j y.ofLp)⊆s.K := by
  intro y hy
  apply s.cutoff_support
  intro hz
  exact hy (by simp [cutoffLayer,hz])

lemma Setup.field_smooth (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (s.field q δ i) :=
  smooth_transferred s.e s.inverse_smooth s.η_smooth s.η_support s.Q _
    (smooth_cutoffLayer s.cutoff_smooth q δ) i

lemma Setup.field_support (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) (i : I) :
    Function.support (s.field q δ i)⊆s.e '' s.K :=
  support_transferred s.e s.η_support s.Q _ (s.cutoff_layer_support q δ) i

lemma Setup.image_compact (s : Setup Ω x) : IsCompact (s.e '' s.K) :=
  compact_image s.e s.compact s.source

end ElasticityBoundaryPacket

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryDensityPull
open Set Filter
open scoped Topology BigOperators

section
/-! The exact physical elastic density under the honest boundary chart. -/
open ElasticityBoundaryRotation
  ElasticityBoundaryGradientTransfer ElasticityBoundaryFrameInverse
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalMass
  ElasticityBoundaryPhysicalTransfer ElasticityBoundaryPullback ElasticityBoundaryFrameOperator
  ElasticityBoundaryPhysicalStrong ElasticityBoundaryStrongLayer ElasticityBoundaryCompactMatrix
  ElasticityBoundaryLayerOperator
abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Y := I → ℝ

def pullMatrix (Q J U : I → I → ℂ) (i k : I) : ℂ :=
  ∑ s, ∑ α, (Q i s*J k α)*U s α

def pullTensor (Q J : I → I → ℂ) (a : I → I → I → I → ℂ)
    (s α r β : I) : ℂ :=
  ∑ i, ∑ k, ∑ j, ∑ v, (Q i s*J k α)*a i k j v*(Q j r*J v β)

end
/-! The exact tensor-density identity extends over the whole honest chart;
all derivatives vanish outside the actual compact packet support. -/
open ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalMass
  ElasticityBoundaryStrongLayer ElasticityBoundaryForceSupport

end ElasticityBoundaryDensityPull
namespace ElasticityBoundaryPacket
/-! Smooth compact localization of the literal pulled physical energy tensor.
The true chart Jacobian is retained, including its nonzero value at the center. -/
open Set Filter
open scoped Topology BigOperators
open ElasticityBoundary ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChartOperator ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

def Setup.jacobian (s : Setup Ω x) (y : Y) : ℝ :=
  |(fderiv ℝ s.Φ (WithLp.toLp 2 y)).det|

def Setup.rawCoeff (s : Setup Ω x) (l m : X → ℂ) (i α j β : I) (y : Y) : ℂ :=
  (s.jacobian y:ℂ)*principal s.Q s.Φ s.Ψ l m i α j β y

end ElasticityBoundaryPacket
namespace ElasticityBoundaryLimit
/-! Genuine Gaussian boundary scaling limits for the finite corrected
amplitudes. Dominated convergence is proved from the uniform polynomial
majorants and the actual half-space weight. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer
abbrev Y := Fin 3 → ℝ

end ElasticityBoundaryLimit
namespace ElasticityBoundaryEnergyLimit
/-! Actual normalized mixed energy limits of the corrected, cut-off boundary
layers. The coefficient has its genuine normal factor and arbitrary compact
smooth remainder; all Jacobian and physical-derivative powers are exact. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix ElasticityBoundaryLimit
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer ElasticityBoundaryProfile
  ElasticityBoundaryCutoffBound
abbrev Y := Fin 3 → ℝ

def mixedScaled (n : ℕ) (H χ : Y → ℂ) (p q : Polynomial W)
    (i α j β : Fin 3) (δ : ℝ) (y : Y) : ℂ :=
  (y 2:ℂ)^n*H (scale δ y)*firstScaled χ p δ i α y*star (firstScaled χ q δ j β y)

end ElasticityBoundaryEnergyLimit
namespace ElasticityBoundaryMixedScaling
/-! Exact physical mixed-energy Jacobian cancellation, followed by the actual
boundary limit. These integrals contain literal Frechet derivatives of the
cut-off corrected fields. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryScaling ElasticityBoundaryWeights ElasticityBoundaryOrderBound
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundaryCutoffParametrix ElasticityBoundaryLimit
  ElasticityBoundaryProfileBounds ElasticityBoundaryCutoffLayer ElasticityBoundaryProfile
  ElasticityBoundaryCutoffBound ElasticityBoundaryEnergyLimit ElasticityBoundaryStrongLayer
abbrev Y := Fin 3 → ℝ

def mixedEnergy (n : ℕ) (H χ : Y → ℂ) (p q : Polynomial W)
    (i α j β : Fin 3) (δ : ℝ) : ℂ :=
  ∫ z in halfspace, (z 2:ℂ)^n*H z*dpart (cutoffLayer χ p δ i) α z*
    star (dpart (cutoffLayer χ q δ j) β z)

end ElasticityBoundaryMixedScaling
namespace ElasticityBoundaryPacket
/-! Direct extraction of every factored normal coefficient by the real physical
DN map and the genuine physical localized asymptotic tests. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open ElasticityBoundaryMVNormal ElasticityBoundaryMixedScaling
  ElasticityBoundaryLimit ElasticityBoundaryMVCalculus ElasticityBoundaryWeights
  ElasticityBoundaryTensorSeries ElasticityBoundaryParameter
variable {Ω : Set X} {x : X}

def frozenPair (n : ℕ) (a : I → I → I → I → ℂ) (p q : W) : ℂ :=
  ∑ i, ∑ α, ∑ j, ∑ β, ∫ y : Y, weight 2 y • ((y 2:ℂ)^n*a i α j β*
    value (E₀ α (p i)) y*star (value (E₀ β (q j)) y))

end ElasticityBoundaryPacket

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Exact transverse and longitudinal frozen physical tests. Both are genuine
solutions of the normal isotropic elasticity equation. -/
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityBoundaryLeading
open ElasticityBoundarySymbol ElasticityBoundaryMVNormal
  ElasticityBoundaryMVCalculus ElasticityBoundaryParameter ElasticityBoundaryLayerOperator
abbrev I := Fin 3
abbrev Y := I → ℝ

def leading (l m : ℂ) (f : F) : W := fun i => lift (homogeneousPolynomial l m f i)

end ElasticityBoundaryLeading

end
end
section
/-! Honest continuous normal Taylor quotients, obtained from the integral
remainder. These are actual functions of the coefficients, not assumed jets. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryNormalTaylor
abbrev Y := Fin 3 → ℝ

def en : Y := Pi.single 2 1

def projection (y : Y) : Y := y-(y 2) • en

def travel (y : Y) (t : ℝ) : Y := projection y+t • ((y 2) • en)

@[simp] lemma en_apply_two : en 2=1 := by simp [en]
@[simp] lemma projection_two (y : Y) : projection y 2=0 := by simp [projection]
@[simp] lemma projection_zero : projection 0=0 := by simp [projection]
@[simp] lemma travel_zero (t : ℝ) : travel 0 t=0 := by simp [travel]
@[simp] lemma travel_one (y : Y) : travel y 1=y := by simp [travel,projection]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def normalJet (n : ℕ) (f : Y → F) (y : Y) : F :=
  iteratedFDeriv ℝ n f y (fun _ => en)

def quotient (n : ℕ) (f : Y → F) (y : Y) : F :=
  (n.factorial:ℝ)⁻¹ • ∫ t in (0:ℝ)..1, (1-t)^n • normalJet (n+1) f (travel y t)

end ElasticityBoundaryNormalTaylor

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_TransportAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section FiniteExpansion
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def truncation (h : ℂ) (N : ℕ) (a : ℕ → V) : V := ∑ j ∈ Finset.range (N+1), h^j • a j
end FiniteExpansion
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The flattened zero plane consists of actual boundary points; lower
physical jets give actual normal Taylor remainders on a ball packet support. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open ElasticityBoundaryNormalTaylor
variable {Ω : Set X} {x : X}

def Setup.chartFunction (s : Setup Ω x) (f : X → ℝ) : Y → ℝ :=
  fun y => f (s.Φ (WithLp.toLp 2 y))

end ElasticityBoundaryPacket

end
end
section
/-! Pointwise linearity of the literal pulled energy tensor in the two
scalar Lamé values. Geometric coefficients are not frozen off-center. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryPacket
open ElasticityBoundaryPhysicalMass ElasticityBoundaryChartOperator
  ElasticityBoundaryPullback ElasticityBoundaryFrameOperator ElasticityBoundaryPhysicalStrong
  ElasticityBoundaryLayerOperator
variable {Ω : Set X} {x : X}

def Setup.linearCoeff (s : Setup Ω x) (l m : Y → ℂ) (i α j β : I) (y : Y) : ℂ :=
  l y*s.rawCoeff (fun _ => 1) (fun _ => 0) i α j β y+
  m y*s.rawCoeff (fun _ => 0) (fun _ => 1) i α j β y

end ElasticityBoundaryPacket

end
end
section
/-! Schwarz symmetry at every finite order for real C-infinity functions.
The analytic-only generic-field theorem is not used. -/
noncomputable section
namespace ElasticityBoundaryJetSymmetry
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dir (v : E) (f : E → F) : E → F := fun x => fderiv ℝ f x v

def word : List E → (E → F) → E → F
  | [], f => f
  | v::vs, f => dir v (word vs f)

end ElasticityBoundaryJetSymmetry

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Recovery
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

namespace ElasticityFiniteType

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Constant-direction differentiation. All directions are real; the values may
be real or complex, as in the source lemma. -/
def D (f : E → F) (v : E) : E → F := fun x => fderiv ℝ f x v

lemma contDiff_D {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (D f v) := by
  exact (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

end ElasticityFiniteType

end
end
end

end OAI
end


