-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:15:14.375023+00:00
-- url     : https://prove2.me/theorems/2c8964d4-99a3-499c-be2b-0f8416dc5882
-- title:
--   Closed Eq Nabla
-- statement:
--   Definitions and structural lemmas for Closed Eq Nabla, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/ClosedEqNabla.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
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
def lclosedeq_B {σ : Type} (h2 : FockQPos) (h3 : FockQBilin) :
    LinearMap.BilinForm ℚ (MvPolynomial σ ℚ) :=
  LinearMap.mk₂ ℚ fockQ (fun f f' g => (h3 σ f f' g 1).1)
    (fun c f g => by rw [(h3 σ f f g c).2, smul_eq_mul])
    (fun f g g' => by rw [(h2 σ f _).1, (h3 σ g g' f 1).1, (h2 σ g f).1, (h2 σ g' f).1])
    (fun c f g => by rw [(h2 σ f _).1, (h3 σ g g f c).2, (h2 σ g f).1, smul_eq_mul])
end Formalism.GradedWeylDivisibility


