-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:56:39.614135+00:00
-- url     : https://prove2.me/theorems/dc8f868a-0d69-43eb-8040-f2932ef48236
-- title:
--   Dual Weyl Non Dom
-- statement:
--   Definitions and structural lemmas for Dual Weyl Non Dom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
section NonDomMain
variable {R : Type*} [CommRing R] {r n : ℕ}
def ndEv (R : Type*) [CommRing R] (r n : ℕ) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun o => o.elim 0 X
end NonDomMain
end Formalism.GradedWeylDivisibility


