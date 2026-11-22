-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:18:31.291254+00:00
-- url     : https://prove2.me/theorems/3e29872b-2cff-46ef-8f25-9634170509a5
-- title:
--   Type IIUp
-- statement:
--   Definitions and structural lemmas for Type IIUp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.G0
namespace TypeIIUpP
def qint (q n : ℕ) : ℕ := ∑ i ∈ Finset.range n, q ^ i
def qfact (q n : ℕ) : ℕ := ∏ i ∈ Finset.range n, qint q (i + 1)
section LA
variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
theorem finite_quot (A : Submodule F W) : Finite (W ⧸ A) := Finite.of_surjective A.mkQ (Submodule.mkQ_surjective A)
attribute [local instance] finite_quot
end LA
end TypeIIUpP
end Formalism.G0


