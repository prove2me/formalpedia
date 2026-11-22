-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftUnimod
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftUnimod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:58.813224+00:00
-- url     : https://prove2.me/theorems/f568fe58-60b1-451b-9894-6c41d45be29a
-- title:
--   Card Lift Unimod
-- statement:
--   Definitions and structural lemmas for Card Lift Unimod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftUnimod.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
open Matrix
section Lift
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]
end Lift
end Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame


