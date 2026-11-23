-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:17.76953+00:00
-- url     : https://prove2.me/theorems/908b22e2-5519-4b6e-bcd3-a3a92e3fc507
-- title:
--   Smat Unitary
-- statement:
--   Definitions and structural lemmas for Smat Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/SmatUnitary.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.L2.SG.Pf.UkEmb
variable {n k : ℕ}
def Wm (wf : Fin k → Fin n → ℂ) : Matrix (Fin n) (Fin k) ℂ := Matrix.of fun i a => wf a i
def smat (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ) (G : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 + Wm wf * (G - 1) * (Wm wf)ᴴ * J
variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)
end Formalism.L2.SG.Pf.UkEmb


