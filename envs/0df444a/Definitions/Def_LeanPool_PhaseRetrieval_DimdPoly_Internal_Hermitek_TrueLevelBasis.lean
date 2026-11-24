-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:09.270073+00:00
-- url     : https://prove2.me/theorems/8e0a97cd-83ef-4c60-9f16-250a74bbf248
-- title:
--   True Level Basis
-- statement:
--   Definitions and structural lemmas for True Level Basis, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermitek/TrueLevelBasis.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
abbrev T : ℝ := HermiteLEAN.T
abbrev Circle := HermiteLEAN.Circle
abbrev posPart := HermiteLEAN.posPart
abbrev rhoh : ℂ → ℝ := HermiteLEAN.rho
abbrev weightedInner := HermiteLEAN.weightedInner
abbrev weightedNormSq := HermiteLEAN.weightedNormSq
abbrev weightedNorm := HermiteLEAN.weightedNorm
abbrev modulusDefect := HermiteLEAN.modulusDefect
abbrev weightedDefectNormSq := HermiteLEAN.weightedDefectNormSq
abbrev weightedDefectNorm := HermiteLEAN.weightedDefectNorm
abbrev positiveTrigonometricPolynomial := HermiteLEAN.positiveTrigonometricPolynomial
abbrev frequencyBand := HermiteLEAN.frequencyBand
abbrev circleL2Sq := HermiteLEAN.circleL2Sq
abbrev circleRhoNormSq := HermiteLEAN.circleRhoNormSq
abbrev circleModulusDefect := HermiteLEAN.circleModulusDefect
abbrev circleDefectNormSq := HermiteLEAN.circleDefectNormSq
abbrev annulus := HermiteLEAN.annulus
abbrev annulusIntegralSq := HermiteLEAN.annulusIntegralSq
abbrev squareBlock := HermiteLEAN.squareBlock
abbrev circlePoint := HermiteLEAN.circlePoint
def eBasis (n : ℕ) (z : ℂ) : ℂ :=
  z ^ n / Real.sqrt ((Nat.factorial n : ℕ) : ℝ)
noncomputable def Phi : ℕ → ℕ → ℂ → ℂ := fun k n z =>
  ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
    Finset.sum (Finset.range (min k n + 1)) (fun j =>
      ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
        z ^ (n - j) * (star z) ^ (k - j))
def phi0 (k : ℕ) : ℂ → ℂ := Phi k 0
def Hk (k : ℕ) : Set (ℂ → ℂ) :=
  {G | Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) ∧
      ∀ z, HasSum (fun n => weightedInner G (Phi k n) * Phi k n z) (G z)}
def finiteHermiteSum (k : ℕ) {D : ℕ} (a : Fin D → ℂ) : ℂ → ℂ :=
  fun z => ∑ n : Fin D, a n * Phi k n.1 z
def topCoeff {d : ℕ} (a : Fin (d + 1) → ℂ) : ℂ :=
  a ⟨d, Nat.lt_succ_self d⟩
def hermiteCoeff (k : ℕ) (G : ℂ → ℂ) (n : ℕ) : ℂ :=
  weightedInner G (Phi k n)
def truncate (k J : ℕ) (G : ℂ → ℂ) : ℂ → ℂ :=
  finiteHermiteSum k (fun n : Fin (J + 1) => hermiteCoeff k G n.1)
noncomputable def qkn : ℕ → ℕ → ℝ → ℝ := fun k n r =>
  (1 / Real.sqrt (Nat.factorial n : ℝ)) *
    Finset.sum (Finset.range (min k n + 1)) (fun j =>
      ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
        r ^ ((n : ℤ) - 2 * (j : ℤ)))
def circleLeadingFactor (k : ℕ) (r : ℝ) : ℂ :=
  ((((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) : ℝ) : ℂ)
def finiteCircleCoeff (k : ℕ) (r : ℝ) {D : ℕ} (a : Fin D → ℂ) : ℕ → ℂ :=
  fun n => if h : n < D then a ⟨n, h⟩ * (qkn k n r : ℂ) else 0
def finiteCirclePoly (k : ℕ) (r : ℝ) {D : ℕ} (a : Fin D → ℂ) : Circle → ℂ :=
  positiveTrigonometricPolynomial (frequencyBand 0 D) (finiteCircleCoeff k r a)
def truncCirclePoly (k : ℕ) (r : ℝ) (J : ℕ) (G : ℂ → ℂ) : Circle → ℂ :=
  finiteCirclePoly k r (fun n : Fin (J + 1) => hermiteCoeff k G n.1)
def tailAnnulusMass (F : ℂ → ℂ) (j0 : ℕ) : ℝ :=
  ∑' j : ℕ, if j0 ≤ j then annulusIntegralSq F j else 0
def hermiteSeries (k : ℕ) (g : ℕ → ℂ) : ℂ → ℂ :=
  fun z => ∑' n : ℕ, g n * Phi k n z
def circleSeries (k : ℕ) (g : ℕ → ℂ) (r : ℝ) : Circle → ℂ :=
  fun t => ∑' n : ℕ, g n * (qkn k n r : ℂ) * fourier (n : ℤ) t
def gaussianWeight (z : ℂ) : ℝ :=
  Real.exp (-(‖z‖ ^ 2) / 2) / Real.sqrt Real.pi
def gaussianScale (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ((gaussianWeight z : ℝ) : ℂ) * F z
end HermitekLEAN


