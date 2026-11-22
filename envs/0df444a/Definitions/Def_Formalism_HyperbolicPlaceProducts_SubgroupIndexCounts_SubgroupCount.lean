-- Prove2me | Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
-- name    : Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:10.325417+00:00
-- url     : https://prove2.me/theorems/02cad44d-5420-43b1-92e6-3a3768fb2ac0
-- title:
--   Subgroup Count
-- statement:
--   Definitions and structural lemmas for Subgroup Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SubgroupCount.lean

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SLP.P
open AddSubgroup
def consEquiv (n : ℕ) : (Fin (n + 1) → ℤ) ≃+ ℤ × (Fin n → ℤ) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_add' f g := rfl
end Formalism.SLP.P


