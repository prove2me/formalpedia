-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseCircleEstimate
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseCircleEstimate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:00:45.19708+00:00
-- url     : https://prove2.me/theorems/d1b9bfa2-7273-4462-988c-7b402f2427fb
-- title:
--   Finite Base Circle Estimate
-- statement:
--   Definitions and structural lemmas for Finite Base Circle Estimate, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseCircleEstimate.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_SafeSquare
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MissingMathlib_Poincare
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Order.Interval.Set.Union
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
noncomputable def lowPoly {D : Nat} (q : Fin (D + 1) -> ℂ) :
    AddCircle (2 * Real.pi) -> ℂ :=
  fun t => ∑ n : Fin (D + 1), q n * circleChar n.1 t
noncomputable def bandPoly (N : Nat) {L : Nat} (p : Fin L -> ℂ) :
    AddCircle (2 * Real.pi) -> ℂ :=
  fun t => ∑ m : Fin L, p m * circleChar (N + m.1) t
noncomputable def slowBandPoly {L : Nat} (p : Fin L -> ℂ) :
    AddCircle (2 * Real.pi) -> ℂ :=
  fun t => ∑ m : Fin L, p m * circleChar m.1 t
noncomputable def slowBandPolyDerivCircle {L : Nat}
    (p : Fin L -> ℂ) : Circle -> ℂ :=
  fun x => ∑ m : Fin L,
    p m * ((2 * Real.pi * Complex.I * (m.1 : ℤ) /
      ((2 * Real.pi : ℝ) : ℂ)) *
        fourier (m.1 : ℤ) x)
noncomputable def slowBandPolyDeriv {L : Nat} (p : Fin L -> ℂ) :
    ℝ -> ℂ :=
  fun t => slowBandPolyDerivCircle p (QuotientAddGroup.mk t : Circle)
noncomputable def circleL2Sq (f : AddCircle (2 * Real.pi) -> ℂ) : ℝ :=
  ∫ t, ‖f t‖ ^ 2 ∂ AddCircle.haarAddCircle
noncomputable def defectSq
    (Q P : AddCircle (2 * Real.pi) -> ℂ) : ℝ :=
  ∫ t, (‖Q t + P t‖ - ‖Q t‖) ^ 2 ∂ AddCircle.haarAddCircle
def circleBadConst (D : Nat) : Nat :=
  max 1 (max (82 * D) (2 ^ D - 1))
def circleGoodBudget (D : Nat) : Nat :=
  64 * circleBadConst D
def circleGap (D : Nat) : Nat :=
  max 37 (2 * circleBadConst D * circleGoodBudget D)
def circleConst (D : Nat) : ℝ := 64 * ((circleGap D : Nat) : ℝ) ^ 2
noncomputable def polyOfCoeff {D : Nat} (q : Fin (D + 1) -> ℂ) :
    Polynomial ℂ :=
  ∑ n : Fin (D + 1), Polynomial.C (q n) * Polynomial.X ^ n.1
noncomputable def badCarrierIndices
    (N : Nat) (roots : Multiset ℂ) (delta : ℝ) : Finset (Fin N) :=
  by
    classical
    exact Finset.univ.filter fun k : Fin N =>
      ∃ ζ : ℂ, ζ ∈ roots ∧
        ∃ x : Circle, x ∈ arcSet (carrierArc N k) ∧ ‖zeta x - ζ‖ < delta
noncomputable def badCarrierIndicesForRoot
    (N : Nat) (ζ : ℂ) (delta : ℝ) : Finset (Fin N) :=
  by
    classical
    exact Finset.univ.filter fun k : Fin N =>
      ∃ x : Circle, x ∈ arcSet (carrierArc N k) ∧ ‖zeta x - ζ‖ < delta
noncomputable def goodCarrierIndices
    (N : Nat) (roots : Multiset ℂ) (delta : ℝ) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)) \ badCarrierIndices N roots delta
def carrierBase {N : Nat} (k : Fin N) : Circle :=
  arcParam (carrierArc N k) 0
def carrierIocImage {N : Nat} (k : Fin N) : Set Circle :=
  QuotientAddGroup.mk ''
    Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
end DimdPolyLEAN


