-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
-- name    : Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:38.694138+00:00
-- url     : https://prove2.me/theorems/bc9b42d8-7417-49b5-b071-6439064ffd50
-- title:
--   Scal Sum
-- statement:
--   Definitions and structural lemmas for Scal Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ScalSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.KP.LL
open Finset
variable {K : Type} [Field K] [CharZero K]
noncomputable def tU (k A l : ℕ) : K :=
  (-1 : K) ^ l * ((k - 1).choose l : K) * ((A - k - l).factorial : K) / ((A - l).factorial : K)
noncomputable def tV (k A l : ℕ) : K := if l = 0 then 0 else tU k A (l - 1)
noncomputable def tT (k A l : ℕ) : K :=
  (((l.factorial : ℕ) : K) ^ 2 * (((A + 1 - l).choose l : ℕ) : K))⁻¹ *
    ((-1 : K) ^ (k - l) / ((((k - l).factorial : ℕ) : K) ^ 2 * (((A - 2 * l).choose (k - l) : ℕ) : K)))
end Formalism.InvariantFactorPaths.KP.LL


