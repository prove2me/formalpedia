-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:38.131561+00:00
-- url     : https://prove2.me/theorems/5debb92f-f3ad-4040-b670-65ba0429c9da
-- title:
--   LHwrow Lemmas
-- statement:
--   Definitions and structural lemmas for LHwrow Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwrowLemmas.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GradedWeylDivisibility
open MvPolynomial
def idPoint (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → R :=
  fun v => if v.1.val = v.2.val then 1 else 0
end Formalism.GradedWeylDivisibility


