-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:49.000271+00:00
-- url     : https://prove2.me/theorems/31516f0e-6f89-4276-a81b-09c10c9c3bda
-- title:
--   HPoly Add Two
-- statement:
--   Definitions and structural lemmas for HPoly Add Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HPolyAddTwo.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
namespace GlobalTheory.FibLine
def fsDens (x : ℂ) : ℝ := 1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)
def lineVec (x : ℂ) : Fin 2 → ℂ := ![1, x]
def qCoef (x : ℂ) (ab : Fin 2 × Fin 2) : ℂ :=
  lineVec x ab.2 * starRingEnd ℂ (lineVec x ab.1) / ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)
def entries {R : Type} (H : Matrix (Fin 2) (Fin 2) R) : Fin 2 × Fin 2 → R := fun ab => H ab.1 ab.2
def qMat {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (x : ℂ) : R :=
  ∑ ab : Fin 2 × Fin 2, qCoef x ab • entries H ab
def fibPow (k : ℕ) : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  ∑ f : Fin k → Fin 2 × Fin 2, C (∫ x : ℂ, (∏ i, qCoef x (f i)) * (fsDens x : ℂ)) * ∏ i, X (f i)
def hPoly (k : ℕ) : MvPolynomial (Fin 2) ℂ :=
  (Nat.rec (motive := fun _ => MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ) (1, X 0)
    (fun _ p => (p.2, X 0 * p.2 - X 1 * p.1)) k).1
def trDet : Fin 2 → MvPolynomial (Fin 2 × Fin 2) ℂ :=
  ![X (0, 0) + X (1, 1), X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)]
end GlobalTheory.FibLine


