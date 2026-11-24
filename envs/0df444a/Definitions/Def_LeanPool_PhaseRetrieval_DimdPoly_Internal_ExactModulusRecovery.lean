-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:15:52.601038+00:00
-- url     : https://prove2.me/theorems/b9022dac-8c2c-4dc7-a1e0-0cc16930cb12
-- title:
--   Exact Modulus Recovery
-- statement:
--   Definitions and structural lemmas for Exact Modulus Recovery, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ExactModulusRecovery.lean

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
noncomputable def realHermiteGenerating (t : ℝ) (u : ℂ) : ℂ :=
  ((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
    Complex.exp
      (-(((t : ℂ) ^ 2) / 2) + (Real.sqrt 2 : ℂ) * (t : ℂ) * u - u ^ 2 / 2)
noncomputable def shiftedGeneratingRightDerivBoundConstant
    (u w0 : ℂ) (x R : ℝ) : ℝ :=
  Real.pi ^ (-(1 / 2 : ℝ)) *
    Real.exp
      (((Real.sqrt 2 * (‖u‖ + (‖w0‖ + R))) ^ 2) / 2 +
        (Real.sqrt 2 * (|x| / 2) * (‖u‖ + (‖w0‖ + R)) +
          ((‖u‖ ^ 2 + (‖w0‖ + R) ^ 2) / 2)))
noncomputable def shiftedGeneratingRightDerivBound
    (u w0 : ℂ) (x R : ℝ) (t : ℝ) : ℝ :=
  shiftedGeneratingRightDerivBoundConstant u w0 x R *
    (1 + (Real.sqrt 2 * |t| +
      (Real.sqrt 2 * (|x| / 2) + (‖w0‖ + R)))) *
    Real.exp (-(t ^ 2) / 2)
noncomputable def realHermite1D (n : ℕ) (t : ℝ) : ℂ :=
  ((Real.sqrt (Nat.factorial n : ℝ) : ℂ) / (Nat.factorial n : ℂ)) *
    iteratedDeriv n (realHermiteGenerating t) 0
noncomputable def complexMonomialGaussian (k : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ k * Complex.exp (-(((t : ℂ) ^ 2) / 2))
noncomputable def realHermiteGeneratingExpansionCoeff (n k : ℕ) : ℂ :=
  (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
    ((Nat.choose n k : ℂ) * (Real.sqrt 2 : ℂ) ^ k *
      iteratedDeriv (n - k)
        (fun u : ℂ => Complex.exp (-(u ^ (2 : ℕ)) / 2)) 0))
noncomputable def standardGaussianMoment (r : ℕ) : ℂ :=
  if Even r then ((r - 1)‼ : ℂ) else 0
noncomputable def realHermiteCoeffScale : ℂ :=
  (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))
noncomputable def gaussianMomentFunctional (p : Polynomial ℤ) : ℂ :=
  p.sum fun k a => (a : ℂ) * standardGaussianMoment k
noncomputable def gaussianMomentBilinear
    (p q : Polynomial ℤ) : ℂ :=
  p.sum fun k a =>
    q.sum fun l b => (a : ℂ) * (b : ℂ) * standardGaussianMoment (k + l)
noncomputable def hermiteStandardInner (n m : ℕ) : ℂ :=
  gaussianMomentFunctional (Polynomial.hermite n * Polynomial.hermite m)
noncomputable def realHermiteTensorRep {d : Nat} (alpha : Idx d) :
    RealVec d -> ℂ :=
  fun x => Finset.prod Finset.univ fun q : Fin d => realHermite1D (alpha q) (x q)
noncomputable def varphiKappa {d : Nat} (kappa : MultiIndex d) : L2Real d := by
  classical
  exact
    if h : MemLp (realHermiteTensorRep kappa) 2
        (volume : Measure (RealVec d)) then
      h.toLp (realHermiteTensorRep kappa)
    else 0
noncomputable def realHermiteTensorL2 {d : Nat} (alpha : Idx d) : L2Real d :=
  varphiKappa alpha
noncomputable def bKappaSeriesRep {d : Nat} (kappa : MultiIndex d)
    (U : Skappa d kappa) : RealVec d -> ℂ :=
  fun x => ∑' alpha : Idx d, coeffSkappa U alpha * realHermiteTensorRep alpha x
noncomputable def bKappa {d : Nat} (kappa : MultiIndex d)
    (U : Skappa d kappa) : L2Real d :=
  ∑' alpha : Idx d, coeffSkappa U alpha • realHermiteTensorL2 alpha
noncomputable def bKappaRep {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) :
    RealVec d -> ℂ :=
  (bKappa kappa U : L2Real d)
noncomputable def TKappa {d : Nat} :
    PhaseSpace d -> Cd d :=
  fun ξ q =>
    ((ξ.1 q : ℂ) - (2 * Real.pi : ℂ) * Complex.I * (ξ.2 q : ℂ)) /
      (Real.sqrt 2 : ℂ)
noncomputable def QKappa {d : Nat} :
    PhaseSpace d -> ℝ :=
  fun ξ => (‖ξ.1‖ ^ 2 + (2 * Real.pi) ^ 2 * ‖ξ.2‖ ^ 2) / 4
noncomputable def WKappa {d : Nat} :
    PhaseSpace d -> ℝ :=
  fun ξ => Real.exp (-(QKappa ξ))
noncomputable def phaseSpacePolyEval {d : Nat}
    (ξ : PhaseSpace d) : (Fin d ⊕ Fin d) -> ℂ
  | Sum.inl q => (ξ.1 q : ℂ)
  | Sum.inr q => (ξ.2 q : ℂ)
def IsPhaseSpacePolynomial {d : Nat} (P : PhaseSpace d -> ℂ) : Prop :=
  ∃ p : MvPolynomial (Fin d ⊕ Fin d) ℂ,
    ∀ ξ : PhaseSpace d, P ξ = MvPolynomial.eval (phaseSpacePolyEval ξ) p
noncomputable def tKappaCoordPoly {d : Nat} (q : Fin d) :
    MvPolynomial (Fin d ⊕ Fin d) ℂ :=
  MvPolynomial.C ((Real.sqrt 2 : ℂ)⁻¹) *
    (MvPolynomial.X (Sum.inl q) -
      MvPolynomial.C ((2 * Real.pi : ℂ) * Complex.I) * MvPolynomial.X (Sum.inr q))
noncomputable def tKappaConjCoordPoly {d : Nat} (q : Fin d) :
    MvPolynomial (Fin d ⊕ Fin d) ℂ :=
  MvPolynomial.C ((Real.sqrt 2 : ℂ)⁻¹) *
    (MvPolynomial.X (Sum.inl q) +
      MvPolynomial.C ((2 * Real.pi : ℂ) * Complex.I) * MvPolynomial.X (Sum.inr q))
noncomputable def complexHermiteMvPolynomial {σ : Type*}
    (m n : Nat) (Z Zstar : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  Finset.sum (Finset.range (min m n + 1)) fun j =>
    MvPolynomial.C (((-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) *
      (Nat.choose m j : ℂ) * (Nat.choose n j : ℂ)) *
      Z ^ (m - j) * Zstar ^ (n - j)
noncomputable def phi1DMvPolynomial {σ : Type*}
    (k n : Nat) (Z Zstar : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  MvPolynomial.C
      (((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ)⁻¹) *
    complexHermiteMvPolynomial n k Z Zstar
noncomputable def PhiTKappaMvPolynomial {d : Nat}
    (kappa alpha : MultiIndex d) : MvPolynomial (Fin d ⊕ Fin d) ℂ :=
  Finset.prod Finset.univ fun q : Fin d =>
    phi1DMvPolynomial (kappa q) (alpha q)
      (tKappaCoordPoly q) (tKappaConjCoordPoly q)
noncomputable def PKappa {d : Nat} (kappa : MultiIndex d) :
    PhaseSpace d -> ℂ :=
  fun ξ =>
    (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun q => kappa q) *
      Phi kappa kappa (TKappa ξ)
noncomputable def stftModelPhase {d : Nat} (kappa : MultiIndex d) :
    PhaseSpace d -> ℂ :=
  fun ξ =>
    (-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun q => kappa q) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.1 ξ.2 : ℝ) : ℂ))
noncomputable def oneDWindowAmbiguityFactor
    (k : Nat) (x ω : ℝ) : ℂ :=
  ∫ t : ℝ,
    realHermite1D k (t + (1 / 2 : ℝ) * x) *
      star (realHermite1D k (t - (1 / 2 : ℝ) * x)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))
noncomputable def oneDWindowAmbiguityMonomialKernel
    (k l : ℕ) (x ω t : ℝ) : ℂ :=
  complexMonomialGaussian k (t + (1 / 2 : ℝ) * x) *
    star (complexMonomialGaussian l (t - (1 / 2 : ℝ) * x)) *
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))
noncomputable def oneDWindowAmbiguityShiftedModulatedGaussian
    (x ω t : ℝ) : ℂ :=
  Complex.exp (-((t : ℂ) ^ 2 + (x : ℂ) ^ 2 / 4)) *
    Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((ω : ℂ) * (t : ℂ)))
noncomputable def centerToEndpointsLinearEquiv (d : Nat) :
    PhaseSpace d ≃ₗ[ℝ] PhaseSpace d where
  toFun p := (p.2 + ((1 / 2 : ℝ) • p.1), p.2 - ((1 / 2 : ℝ) • p.1))
  invFun p := (p.1 - p.2, ((1 / 2 : ℝ) • (p.1 + p.2)))
  left_inv := by
    intro p
    ext q <;> simp
    · ring
    · ring
  right_inv := by
    intro p
    ext q <;> simp
    · ring
    · ring
  map_add' := by
    intro p q
    ext r <;> simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
  map_smul' := by
    intro c p
    ext r <;> simp [smul_add, smul_sub, mul_left_comm]
end DimdPolyLEAN


