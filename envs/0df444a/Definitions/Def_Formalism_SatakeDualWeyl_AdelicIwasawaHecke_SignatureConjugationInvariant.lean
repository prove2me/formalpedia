-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:14:16.069814+00:00
-- url     : https://prove2.me/theorems/6edc3528-c93d-4847-806c-55510eedb5bb
-- title:
--   Signature Conjugation Invariant
-- statement:
--   Definitions and structural lemmas for Signature Conjugation Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SignatureConjugationInvariant.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace Formalism.UG.P
open Formalism.UG
section Sig
variable {n : Type} [Fintype n] [DecidableEq n]
end Sig
end Formalism.UG.P


