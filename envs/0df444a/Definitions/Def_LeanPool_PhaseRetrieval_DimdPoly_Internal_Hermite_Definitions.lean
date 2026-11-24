-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:58:45.028868+00:00
-- url     : https://prove2.me/theorems/6c783e9e-cc13-4980-a517-a146f42d8eee
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite/Definitions.lean

module
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Data.Nat.Dist
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate Topology
noncomputable section
namespace HermiteLEAN
def T : ℝ := 2 * Real.pi
lemma T_pos : 0 < T := by
  dsimp [T]
  positivity
instance : Fact (0 < T) := ⟨T_pos⟩
abbrev Circle := AddCircle T
def posPart (x : ℝ) : ℝ := max x 0
def rho (w : ℂ) : ℝ := |‖(1 : ℂ) + w‖ - 1|
def phi0 (z : ℂ) : ℂ := conj z
def phi : ℕ → ℂ → ℂ
  | 0 => phi0
  | n + 1 =>
      fun z =>
        z ^ n *
          (((‖z‖ ^ 2 - (Nat.succ n : ℝ)) /
              Real.sqrt ((Nat.factorial (Nat.succ n) : ℕ) : ℝ)) : ℂ)
def weightedInner (F G : ℂ → ℂ) : ℂ :=
  (1 / Real.pi : ℂ) *
    ∫ z, F z * conj (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ)
def weightedNormSq (F : ℂ → ℂ) : ℝ :=
  (1 / Real.pi) * ∫ z, ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)
def weightedNorm (F : ℂ → ℂ) : ℝ := Real.sqrt (weightedNormSq F)
def modulusDefect (F0 G : ℂ → ℂ) (z : ℂ) : ℝ := |‖F0 z + G z‖ - ‖F0 z‖|
def weightedDefectNormSq (F0 G : ℂ → ℂ) : ℝ :=
  (1 / Real.pi) *
    ∫ z, (modulusDefect F0 G z) ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)
def weightedDefectNorm (F0 G : ℂ → ℂ) : ℝ := Real.sqrt (weightedDefectNormSq F0 G)
def Phi0Perp : Set (ℂ → ℂ) := {F | weightedInner F phi0 = 0}
def hermiteSum {D : ℕ} (a : Fin D → ℂ) (z : ℂ) : ℂ :=
  ∑ n : Fin D, a n * phi (n.1 + 1) z
def hermiteCoeffNormSq {D : ℕ} (a : Fin D → ℂ) : ℝ :=
  ∑ n : Fin D, ‖a n‖ ^ 2
def circlePoint (r : ℝ) (t : Circle) : ℂ := (r : ℂ) * (fourier (1 : ℤ) t : ℂ)
def circleCoeff {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (n : Fin D) : ℂ :=
  a n *
    ((((r ^ n.1) * (r ^ 2 - ((n.1 + 1 : ℕ) : ℝ))) /
        (r * Real.sqrt ((Nat.factorial (n.1 + 1) : ℕ) : ℝ)) : ℝ) : ℂ)
def circlePolynomial {D : ℕ} (a : Fin D → ℂ) (r : ℝ) : Circle → ℂ :=
  fun t => ∑ n : Fin D, circleCoeff a r n * fourier ((n.1 + 1 : ℕ) : ℤ) t
def positiveTrigonometricPolynomial (E : Finset ℕ) (c : ℕ → ℂ) : Circle → ℂ :=
  fun t => Finset.sum E (fun n => c n * fourier (n : ℤ) t)
def frequencyBand (N L : ℕ) : Finset ℕ := Finset.Icc N (N + L - 1)
def circleL2Sq (f : Circle → ℂ) : ℝ :=
  ∫ t, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle
def circleRhoNormSq (f : Circle → ℂ) : ℝ :=
  ∫ t, (rho (f t)) ^ 2 ∂AddCircle.haarAddCircle
def circleModulusDefect (F0 G : Circle → ℂ) (t : Circle) : ℝ :=
  |‖F0 t + G t‖ - ‖F0 t‖|
def circleDefectNormSq (F0 G : Circle → ℂ) : ℝ :=
  ∫ t, (circleModulusDefect F0 G t) ^ 2 ∂AddCircle.haarAddCircle
def annulus (j : ℕ) : Set ℂ := {z | (j : ℝ) ≤ ‖z‖ ∧ ‖z‖ < ((j + 1 : ℕ) : ℝ)}
def annulusIntegralSq (F : ℂ → ℂ) (j : ℕ) : ℝ :=
  (1 / Real.pi) *
    ∫ z in annulus j, ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)
def squareBlock (ℓ : ℕ) : Finset ℕ := Finset.Ico (ℓ ^ 2) ((ℓ + 1) ^ 2)
def blockIndex (n : ℕ) : ℕ := Nat.sqrt n
def blockPiece {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) : ℂ → ℂ :=
  fun z => ∑ n : Fin D, if blockIndex (n.1 + 1) = ℓ then a n * phi (n.1 + 1) z else 0
def localPiece {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) : ℂ → ℂ :=
  fun z =>
    ∑ n : Fin D,
      if Nat.dist (blockIndex (n.1 + 1)) j ≤ M then a n * phi (n.1 + 1) z else 0
def remainderPiece {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) : ℂ → ℂ :=
  fun z => hermiteSum a z - localPiece a M j z
def blockCoeffNormSq {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) : ℝ :=
  ∑ n : Fin D, if blockIndex (n.1 + 1) = ℓ then ‖a n‖ ^ 2 else 0
def h1Series (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, a n * phi n z
def H1 : Set (ℂ → ℂ) :=
  ((Submodule.span ℂ (Set.range phi)).topologicalClosure : Set (ℂ → ℂ))
def H1Orthogonal : Set (ℂ → ℂ) :=
  ((Submodule.span ℂ (Set.range fun n : ℕ => phi (n + 1))).topologicalClosure :
    Set (ℂ → ℂ))
def gaussianTail (c : ℝ) (M : ℕ) : ℝ :=
  ∑' m : ℕ, Real.exp (-c * (posPart ((((m + M + 1 : ℕ) : ℝ) - 4))) ^ 2)
def etaCoeff (Cblk cblk : ℝ) (M : ℕ) : ℝ := 2 * Cblk * gaussianTail cblk M
end HermiteLEAN


