-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
-- name    : ReciprocityTheory_Chebotarev_EulerSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:06.257995+00:00
-- url     : https://prove2.me/theorems/b7d8bc53-b903-455d-81af-320847dd3f3c
-- title:
--   Euler Sum
-- statement:
--   Definitions and structural lemmas for Euler Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
namespace ReciprocityTheory.Cheb
noncomputable def idealZetaR (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)
end ReciprocityTheory.Cheb


