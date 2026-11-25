-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:23.675187+00:00
-- url     : https://prove2.me/theorems/a8f40015-0079-4a95-8cef-4a59c4102ac1
-- title:
--   Twist At Of Ne
-- statement:
--   Definitions and structural lemmas for Twist At Of Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistAtOfNe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
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
open Polynomial
namespace GlobalTheory.Nef
def symMat {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun a i => ((C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a
def twistAt {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) : Place k F → Matrix (Fin n) (Fin n) F := by
  classical
  exact fun v => if v = v₀ then c • h v else h v
end GlobalTheory.Nef


