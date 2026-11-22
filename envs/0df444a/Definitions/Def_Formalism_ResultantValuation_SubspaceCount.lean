-- Prove2me | Definitions.Def_Formalism_ResultantValuation_SubspaceCount
-- name    : Formalism_ResultantValuation_SubspaceCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:04.446004+00:00
-- url     : https://prove2.me/theorems/31a44205-42c3-44ca-bf97-b78a46b65dd8
-- title:
--   Subspace Count
-- statement:
--   Definitions and structural lemmas for Subspace Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/SubspaceCount.lean

import Definitions.Def_Formalism_ResultantValuation_KoszulSecondDifferential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ResultantValuation
def SubspaceCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (j : ℕ),
    (Nat.card {W : Submodule F V // Module.finrank F W = j} : ℤ) *
        ∏ i ∈ Finset.range j, ((Fintype.card F : ℤ) ^ j - (Fintype.card F : ℤ) ^ i) =
      ∏ i ∈ Finset.range j,
        ((Fintype.card F : ℤ) ^ Module.finrank F V - (Fintype.card F : ℤ) ^ i)
end Formalism.ResultantValuation


