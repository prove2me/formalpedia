-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_CutCapacity
-- name    : DiscreteConvex_NetworkFlows_CutCapacity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:16:13.103135+00:00
-- url     : https://prove2.me/theorems/0657825f-614b-4e9f-95e7-3d746a0ec168
-- title:
--   Cut capacity function $\kappa$ (Eq. 9.16)
-- statement:
--   The **cut capacity function** $\kappa(X) = \bar c(\Delta^+X) - \underline c(\Delta^-X)$ (Eq. (9.16)), landing in $\mathbb R \cup \{+\infty\}$: both `UpperCapOf` on $\Delta^+X$ and `NegLowerCapOf` on $\Delta^-X$ are individually in $\mathbb R \cup \{+\infty\}$ (never $-\infty$), so their sum is a safe, unambiguous addition rather than a genuine extended-real subtraction; see `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.16).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.16)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaPlus
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaMinus
import Definitions.Def_DiscreteConvex_NetworkFlows_UpperCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerCapOf

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.247, Eq. (9.16): the cut capacity function,
in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- The **cut capacity function** `κ(X) = c̄(Δ⁺X) - c(Δ⁻X)` (Eq. (9.16)). -/
noncomputable def CutCapacity {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (X : Finset V) :
    WithTop ℝ :=
  UpperCapOf cUpper (DeltaPlus tail head X) + NegLowerCapOf cLower (DeltaMinus tail head X)

end DiscreteConvex.NetworkFlows


