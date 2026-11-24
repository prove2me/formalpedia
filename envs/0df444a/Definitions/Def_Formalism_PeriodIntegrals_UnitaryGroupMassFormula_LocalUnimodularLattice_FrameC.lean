-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:41:34.167379+00:00
-- url     : https://prove2.me/theorems/b252a98e-7ad2-4e65-a596-8d8c118d1f4e
-- title:
--   Frame C
-- statement:
--   Definitions and structural lemmas for Frame C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnimodularLattice/FrameC.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW Formalism.REAL
variable {k r : ℕ}
def fcol (k r : ℕ) (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ)
    (z0 : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h1 : i.val < r then e ⟨i.val, h1⟩
  else if h2 : i.val < r + k then wf ⟨i.val - r, by omega⟩
  else if h3 : i.val = r + k then z0
  else f ⟨2 * r + k - i.val, by have := i.isLt; omega⟩
def Pm (k r : ℕ) (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (wf : Fin k → Fin (2 * r + k + 1) → ℂ)
    (z0 : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.of fun a j => fcol k r e f wf z0 j a
section Frame
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}
variable (hF : IsFrameJ ε e f wf z0)
include hF
def Qm (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Hpk k r * (Pm k r e f wf z0)ᴴ * Jm ε
end Frame
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC


