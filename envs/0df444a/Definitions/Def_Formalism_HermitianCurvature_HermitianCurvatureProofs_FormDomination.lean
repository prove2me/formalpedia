-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:53.000517+00:00
-- url     : https://prove2.me/theorems/5b65c33e-0081-4453-b6b3-b240f2b6ccc9
-- title:
--   Form Domination
-- statement:
--   Definitions and structural lemmas for Form Domination, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FormDomination.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.FormDomination
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
variable {E W : Type} [Field E] (D : Data E W)
end Formalism.FourierDecayAlt.P.FormDomination
namespace Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.FormDomination
open Classical
end Formalism.FourierDecayAlt.P


