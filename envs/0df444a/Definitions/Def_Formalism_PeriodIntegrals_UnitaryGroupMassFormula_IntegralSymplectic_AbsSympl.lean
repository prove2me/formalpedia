-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSymplectic_AbsSympl
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSymplectic_AbsSympl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:06.599823+00:00
-- url     : https://prove2.me/theorems/fba9b8bc-a9cc-4f7e-9c65-385e77535200
-- title:
--   Abs Sympl
-- statement:
--   Definitions and structural lemmas for Abs Sympl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralSymplectic/AbsSympl.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SymplZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.SymplZW
open Matrix
abbrev J (k : ℕ) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℤ :=
  Matrix.fromBlocks 0 1 (-1) 0
def AbsSympl : Prop :=
  ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] (_ : Module.Basis (Fin n) ℤ M)
    (B : M →ₗ[ℤ] M →ₗ[ℤ] ℤ), (∀ x, B x x = 0) → Function.Injective B →
      Function.Surjective B →
      ∃ (k : ℕ) (c : Module.Basis (Fin k ⊕ Fin k) ℤ M), ∀ i j, B (c i) (c j) = J k i j
def MatStep : Prop := AbsSympl → PI.SymplZ
end PI.SymplZW


