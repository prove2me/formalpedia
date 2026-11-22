-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:39.999848+00:00
-- url     : https://prove2.me/theorems/18097993-c81a-4390-a602-6293fd0ade0d
-- title:
--   Highest Vector Projection
-- statement:
--   Definitions and structural lemmas for Highest Vector Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
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
section Abs
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
end Abs
section EC
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def lowIm' (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (j : ℕ) (ρ : Fin r) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c),
    Submodule.map (glAct p LL j c d) ⊤
end EC
end Formalism.InvariantFactorPaths.L4


