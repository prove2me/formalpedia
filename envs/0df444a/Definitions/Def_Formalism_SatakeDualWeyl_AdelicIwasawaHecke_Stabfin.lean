-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:22.262239+00:00
-- url     : https://prove2.me/theorems/ed8e3256-e4e8-4c17-9efa-0ac16928d2e3
-- title:
--   Stabfin
-- statement:
--   Definitions and structural lemmas for Stabfin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField ComplexConjugate
namespace Formalism.UG.P
section Den
variable {E : Type} [Field E] [NumberField E]
end Den
section CS
variable {n : Type} [Fintype n] [DecidableEq n]
end CS
section B
variable {n : Type} [Fintype n] [DecidableEq n]
end B
end Formalism.UG.P


