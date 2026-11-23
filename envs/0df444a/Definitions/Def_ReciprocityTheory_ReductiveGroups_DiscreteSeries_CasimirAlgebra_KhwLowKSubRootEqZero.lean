-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:20.929078+00:00
-- url     : https://prove2.me/theorems/27f17305-1663-420c-b438-d1be96565009
-- title:
--   Khw Low KSub Root Eq Zero
-- statement:
--   Definitions and structural lemmas for Khw Low KSub Root Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def wdP (ε : Fin n → Bool) (a b : Fin n) : Prop := (a < b ∧ ε a = ε b) ∨ (b < a ∧ ε a ≠ ε b)
instance signedOrder_decidable (ε : Fin n → Bool) : DecidableRel (wdP ε) := fun a b => by
  unfold wdP; infer_instance
section Unitary
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
end Unitary
end ReciprocityTheory.ChartRestriction.DS


