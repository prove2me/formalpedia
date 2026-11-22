-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SymDist
-- name    : Formalism_PeriodIntegrals_SymDist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:23.538867+00:00
-- url     : https://prove2.me/theorems/497fbdb1-11fb-4032-b02d-a4a3cad9ef5c
-- title:
--   Sym Dist
-- statement:
--   Definitions and structural lemmas for Sym Dist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SymDist.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
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
namespace PI
def symD {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : ℝ :=
  sInf {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
    ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
    t = Real.sqrt (Formalism.REAL.hs X)}
def SymDist : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g k : Formalism.REAL.UJ ε), symD ε (g * k) ≤ symD ε g + symD ε k
end PI
end


