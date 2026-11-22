-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:56:51.97589+00:00
-- url     : https://prove2.me/theorems/ad80fc65-cd24-4b54-9cbb-96c22ff057ba
-- title:
--   LCcomp Lemmas
-- statement:
--   Definitions and structural lemmas for LCcomp Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
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
def lccompW {r n : ℕ} (l j : Fin n) : Option (Fin r × Fin n) → (Fin r × Fin n →₀ ℕ) :=
  fun o => match o with
    | none => 0
    | some v => pairW l j v
end Formalism.GradedWeylDivisibility


