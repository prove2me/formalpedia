-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:34.510147+00:00
-- url     : https://prove2.me/theorems/8e04958d-3f19-4bc5-ab9a-67371b48953e
-- title:
--   Stabstd
-- statement:
--   Definitions and structural lemmas for Stabstd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabstd.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.UG.P
open Matrix
variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]
end Formalism.UG.P


