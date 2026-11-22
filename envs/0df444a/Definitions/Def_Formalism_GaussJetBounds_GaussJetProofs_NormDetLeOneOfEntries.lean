-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
-- name    : Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:17.782522+00:00
-- url     : https://prove2.me/theorems/1d6419fa-0a7c-45ff-a101-95a9f10c1209
-- title:
--   Norm Det Le One Of Entries
-- statement:
--   Definitions and structural lemmas for Norm Det Le One Of Entries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormDetLeOneOfEntries.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
section DegProdSec
variable {σ κ : Type} [DecidableEq κ] (blk : σ → Option κ)
def bdeg (k : κ) (mono : σ →₀ ℕ) : ℕ := (mono.support.filter (fun v => blk v = some k)).sum mono
end DegProdSec
section BasisSec
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end BasisSec
end Formalism.DworkPowerSeriesWeights


