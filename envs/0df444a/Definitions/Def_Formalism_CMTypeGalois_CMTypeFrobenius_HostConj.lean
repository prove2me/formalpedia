-- Prove2me | Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
-- name    : Formalism_CMTypeGalois_CMTypeFrobenius_HostConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:54.905064+00:00
-- url     : https://prove2.me/theorems/575f30b2-3b9e-4579-b753-840877776b72
-- title:
--   Host Conj
-- statement:
--   Definitions and structural lemmas for Host Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostConj.lean

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.Q3
namespace CMConjugation
variable {q : Fin 3 → ℕ} {E : Type} [Field E] [NumberField E] {α : Fin 3 → E}
end CMConjugation
open CMConjugation
end Formalism.Q3


