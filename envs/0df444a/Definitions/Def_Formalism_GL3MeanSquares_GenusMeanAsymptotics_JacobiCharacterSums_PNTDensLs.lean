-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLs
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T07:03:23.574198+00:00
-- url     : https://prove2.me/theorems/c47ef829-acc7-5121-b27b-2b746eaa912e
-- title:
--   PNTDens Ls
-- statement:
--   Definitions and structural lemmas for PNTDens Ls, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensLs.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
def Φe (j : ZMod 2) : ℂ := if j = 0 then -1 else 1
def eps (n : ℕ) : ℂ := Φe (n : ZMod 2)
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet EtaPartialSums
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens


