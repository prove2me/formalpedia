-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:12.4468+00:00
-- url     : https://prove2.me/theorems/09de42bc-9741-4dcb-8946-c3e126cb163f
-- title:
--   Isogeny Expansion
-- statement:
--   Definitions and structural lemmas for Isogeny Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IsogenyExpansion.lean

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace Formalism.ELL.QuadraticDifferenceHypotheses
universe u
section Exact
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]
structure BiHyp (bar : O → O) (ψ : M → Q) : Prop where
  add1 : ∀ a a' b : M, quadDiff ψ (a + a') b = quadDiff ψ a b + quadDiff ψ a' b
  zero : ψ 0 = 0
  adj : ∀ (α : O) (a b : M), quadDiff ψ (α • a) b = quadDiff ψ a (bar α • b)
end Exact
section Quot
variable {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T]
end Quot
end Formalism.ELL.QuadraticDifferenceHypotheses
namespace Formalism.ELL
open Formalism.ELL.QuadraticDifferenceHypotheses
universe u
end Formalism.ELL


