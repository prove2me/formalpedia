-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:17.646862+00:00
-- url     : https://prove2.me/theorems/67f6659d-5bea-4440-9b0b-f20f783ba103
-- title:
--   Dom Pow
-- statement:
--   Definitions and structural lemmas for Dom Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DomPow.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.GradedWeylDivisibility
def ldiagExt {α : Type*} [Zero α] {r : ℕ} (f : Fin r → α) (a : ℕ) : α :=
  if h : a < r then f ⟨a, h⟩ else 0
end Formalism.GradedWeylDivisibility


