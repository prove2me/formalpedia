-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:29:11.360851+00:00
-- url     : https://prove2.me/theorems/c51f0f72-4704-4b61-8426-0025f7494f32
-- title:
--   Res Into
-- statement:
--   Definitions and structural lemmas for Res Into, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section Res
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end Res
section Last
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
noncomputable def FreeLast (p : ℕ) [Fact p.Prime] (K r : ℕ) :
    Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  restrictSupport ℚ_[p] {m | ∀ c, m (Fin.last K, c) = 0}
end Last
end Formalism.InvariantFactorPaths.L4


