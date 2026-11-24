-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:33.702049+00:00
-- url     : https://prove2.me/theorems/946748d2-2c2d-468c-9c4a-c2b5a8e24f32
-- title:
--   Gelf A
-- statement:
--   Definitions and structural lemmas for Gelf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/GelfA.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mem.Gelf
open MvPolynomial
def rowE (R : Type) [CommRing R] (r n : ℕ) :
    Matrix (Fin r) (Fin r) (Module.End R (MvPolynomial (Fin r × Fin n) R)) :=
  Matrix.of fun a b => ∑ s : Fin n,
    (LinearMap.mulLeft R (X (a, s) : MvPolynomial (Fin r × Fin n) R)).comp (pderiv (R := R) (b, s)).toLinearMap
def GlRel {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)
def gelfA {R : Type} [CommRing R] {N : ℕ} (μ : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun a b => if a = b then μ a + ((N - 1 - a.val : ℕ) : R) else if a < b then -1 else 0
def gelfC {R : Type} [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) : R :=
  ∑ a, ∑ b, (gelfA μ ^ k) a b
end GlobalTheory.Mem.Gelf


