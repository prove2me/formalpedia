-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:58:44.129623+00:00
-- url     : https://prove2.me/theorems/b006e771-03ee-4533-9035-c705a4dd9ab5
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Definitions.lean

module
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
abbrev Cd (d : Nat) := Fin d -> ℂ
abbrev MultiIndex (d : Nat) := Fin d -> Nat
abbrev Idx (d : Nat) := MultiIndex d
abbrev CircleFreq := Int
abbrev CircleTrigPoly := Finsupp CircleFreq ℂ
abbrev Pkappa (d : Nat) (kappa : MultiIndex d) : Type :=
  (fun _ : MultiIndex d => Finsupp (Idx d) ℂ) kappa
namespace Pkappa
@[ext] theorem ext {d : Nat} {kappa : MultiIndex d} {F G : Pkappa d kappa}
    (h : ∀ a, F a = G a) : F = G := Finsupp.ext h
end Pkappa
structure Skappa (d : Nat) (kappa : MultiIndex d) where
  /-- The coefficient of each multi-index. -/
  coeff : Idx d -> ℂ
  /-- The coefficients are square-summable. -/
  summable_norm_sq : Summable (fun alpha : Idx d => ‖coeff alpha‖ ^ 2)
instance instFactLtRealOfNatHMulPi_leanPool : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩
def gaussianDensity (d : Nat) (z : Cd d) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-Finset.sum Finset.univ (fun q : Fin d => ‖z q‖ ^ 2))
def gammaD (d : Nat) : MeasureTheory.Measure (Cd d) :=
  MeasureTheory.volume.withDensity fun z => ENNReal.ofReal (gaussianDensity d z)
abbrev L2Tensor (d : Nat) := MeasureTheory.Lp ℂ 2 (gammaD d)
def complexHermite (m n : Nat) (z : ℂ) : ℂ :=
  Finset.sum (Finset.range (min m n + 1)) fun j =>
    ((-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) *
      (Nat.choose m j : ℂ) * (Nat.choose n j : ℂ) *
      z ^ (m - j) * (star z) ^ (n - j)
def phi1D (k n : Nat) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ)⁻¹) *
    complexHermite n k z
def Phi {d : Nat} (kappa : MultiIndex d) (alpha : Idx d) (z : Cd d) : ℂ :=
  Finset.prod Finset.univ fun q : Fin d => phi1D (kappa q) (alpha q) (z q)
def box {d : Nat} (J : MultiIndex d) : Finset (Idx d) :=
  Fintype.piFinset fun q : Fin d => Finset.range (J q + 1)
noncomputable instance instNormCircleTrigPoly : Norm CircleTrigPoly :=
  ⟨fun p => Real.sqrt (Finset.sum p.support fun n => ‖p n‖ ^ 2)⟩
noncomputable instance instNormPkappa {d : Nat} {kappa : MultiIndex d} : Norm (Pkappa d kappa) :=
  ⟨fun F => Real.sqrt (Finset.sum F.support fun alpha => ‖F alpha‖ ^ 2)⟩
instance {d : Nat} {kappa : MultiIndex d} : Zero (Skappa d kappa) :=
  ⟨{ coeff := fun _ => 0
     summable_norm_sq := by simp }⟩
instance {d : Nat} {kappa : MultiIndex d} : SMul ℂ (Skappa d kappa) where
  smul c u :=
    { coeff := fun alpha => c * u.coeff alpha
      summable_norm_sq := by
        have hEq :
            (fun alpha : Idx d => ‖c * u.coeff alpha‖ ^ 2) =
              fun alpha => (‖c‖ ^ 2) * (‖u.coeff alpha‖ ^ 2) := by
          funext alpha
          rw [norm_mul, mul_pow]
        rw [hEq]
        exact u.summable_norm_sq.mul_left (‖c‖ ^ 2) }
def coeffPkappa {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) (alpha : Idx d) : ℂ := F alpha
def coeffSkappa {d : Nat} {kappa : MultiIndex d} (F : Skappa d kappa) (alpha : Idx d) : ℂ :=
  F.coeff alpha
def evalPkappa {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) : Cd d -> ℂ :=
  fun z => F.sum fun alpha c => c * Phi kappa alpha z
def toFun {d : Nat} (kappa : MultiIndex d) (F : Skappa d kappa) : Cd d -> ℂ :=
  fun z => ∑' alpha : Idx d, coeffSkappa F alpha * Phi kappa alpha z
noncomputable def toL2 {d : Nat} (kappa : MultiIndex d) (F : Skappa d kappa) : L2Tensor d := by
  classical
  exact if h : MeasureTheory.MemLp (toFun kappa F) 2 (gammaD d) then h.toLp (toFun kappa F) else 0
def ofPkappa {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) : Skappa d kappa :=
  { coeff := fun alpha => F alpha
    summable_norm_sq := by
      classical
      refine summable_of_hasFiniteSupport ?_
      refine Set.Finite.subset F.support.finite_toSet ?_
      simp_all }
def projFinset {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d)) (F : Pkappa d kappa) :
    Pkappa d kappa :=
  F.filter fun alpha => alpha ∈ E
def truncateFinset {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d)) (F : Skappa d kappa) :
    Pkappa d kappa :=
  Finset.sum E fun alpha => Finsupp.single alpha (coeffSkappa F alpha)
def rotateCoord {d : Nat} (q : Fin d) (t : ℝ) (z : Cd d) : Cd d :=
  Function.update z q (Complex.exp (t * Complex.I) * z q)
def pkappaInner {d : Nat} {kappa : MultiIndex d} (F G : Pkappa d kappa) : ℂ :=
  F.sum fun alpha c => c * star (G alpha)
def basePointNormalized {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : Prop :=
  F ≠ 0 ∧ ‖F‖ = 1
def orthogonalToPk {d : Nat} {kappa : MultiIndex d} (F G : Pkappa d kappa) : Prop :=
  pkappaInner G F = 0
def positivePhaseGauge {d : Nat} {kappa : MultiIndex d}
    (F Q : Pkappa d kappa) : Prop :=
  (pkappaInner Q F).im = 0 ∧ 0 ≤ (pkappaInner Q F).re
def defect {d : Nat} {kappa : MultiIndex d} (F G : Pkappa d kappa) : ℝ :=
  Real.sqrt <| ∫ z, (‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖) ^ 2 ∂ gammaD d
def productAnnulus {d : Nat} (j : Idx d) : Set (Cd d) :=
  { z | ∀ q : Fin d, (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1 }
def annulusMass {d : Nat} {kappa : MultiIndex d} (j : Idx d) (F : Skappa d kappa) : ℝ :=
  ∫ z, Set.indicator (productAnnulus j) (fun w => ‖toFun kappa F w‖ ^ 2) z ∂ gammaD d
def lowAnnuli (d J : Nat) : Finset (Idx d) :=
  Fintype.piFinset fun _ : Fin d => Finset.range J
def lowAnnulusMass {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Skappa d kappa) : ℝ :=
  Finset.sum (lowAnnuli d J) fun j => annulusMass j F
def highAnnulusMass {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Skappa d kappa) : ℝ :=
  (∫ z, ‖toFun kappa F z‖ ^ 2 ∂ gammaD d) - lowAnnulusMass J F
def coefficientRadius {d : Nat} (alpha : Idx d) : Nat :=
  Finset.sup Finset.univ alpha
def highAnnulusEnergy {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Pkappa d kappa) : ℝ :=
  highAnnulusMass J (ofPkappa kappa F)
def lowBlockLeakage {d : Nat} {kappa : MultiIndex d} (J : Nat) (F : Pkappa d kappa) : ℝ :=
  lowAnnulusMass J (ofPkappa kappa F)
def supportRadius {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : Nat :=
  Finset.sup F.support coefficientRadius
def Jann {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : Nat :=
  supportRadius F + 1
def Cann {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : ℝ :=
  ‖F‖ ^ 2 + (Jann F : ℝ) + 1
def Cleak {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : ℝ :=
  ‖F‖ + (F.support.card : ℝ) + 1
def deltaRig {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (E : Finset (Idx d)) (rho : ℝ) : ℝ :=
  rho / ((Jann F + E.card + 1 : Nat) : ℝ)
def Cperp {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : ℝ :=
  Cann F + Cleak F
noncomputable def evalCircle (p : CircleTrigPoly) : AddCircle (2 * Real.pi) -> ℂ :=
  fun t => Finset.sum p.support fun n => p n * (AddCircle.toCircle (n • t) : ℂ)
def oneSidedLowFreq (p : CircleTrigPoly) (D : Nat) : Prop :=
  ∀ n ∈ p.support, 0 ≤ n ∧ n ≤ D
def highBandSupport (q : CircleTrigPoly) (N B : Nat) : Prop :=
  ∀ n ∈ q.support, (N : Int) ≤ n ∧ n < ((N + B) : Int)
def gapCircle (D : Nat) : Nat := D + 1
def defectCircle (p q : CircleTrigPoly) : ℝ :=
  Real.sqrt <| ∫ t, (‖evalCircle (p + q) t‖ - ‖evalCircle p t‖) ^ 2 ∂ AddCircle.haarAddCircle
def Ccircle (p : CircleTrigPoly) (D N B : Nat) : ℝ :=
  ‖p‖ + ((D + N + B + 1 : Nat) : ℝ)
end DimdPolyLEAN


