-- Prove2me | Definitions.Def_ResetInventory_HDerivLipschitz
-- name    : ResetInventory_HDerivLipschitz
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:38.848438+00:00
-- url     : https://prove2.me/theorems/7fa623e3-1209-4457-9a6b-a7aa690a6ecb
-- title:
--   $\partial_xH(\cdot,t)$ is Lipschitz on $[0,c_{\max}]$
-- statement:
--   The first derivative of the stage-cost function $H(\cdot,t)$ of Assumption 2 is **Lipschitz on $[0,c_{\max}]$**: $H(\cdot,t)$ has a derivative $H'$ within $[0,c_{\max}]$, and for some constant $C$
--   $$
--   |H'(z)-H'(z')|\le C\,|z-z'|\qquad (z,z'\in[0,c_{\max}]).
--   $$
--   This is not an assumption of the paper. It is the extra condition under which the corrected Proposition 6 and Theorem 1 assert that the third piece of the value function, $H(x,t)+\gamma\,\mathbb E\,J((x-w)^+,t+1)$, has a Lipschitz derivative; the other pieces have one unconditionally. It holds in the paper's examples, where $\partial_{xx}H=(p\pm q)f$ is bounded.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Assumption 2, p.15; proof of Proposition 6, p.35; Propositions 7–8, pp.22–23

import Mathlib
import Definitions.Def_ResetInventory_ResetModel

namespace ResetInventory

/-- The first derivative `∂ₓH(·, t)` of the stage-cost function of Assumption 2 (Lee, Mintz,
Aswani, Shen, Yang, arXiv:2209.03571v1, p.15) is Lipschitz on `[0, c_max]`: there are a
derivative `H'` of `H(·, t)` within `[0, c_max]` and a constant `C` with
`|H'(z) − H'(z')| ≤ C |z − z'|` for `z, z' ∈ [0, c_max]`.

**Formalization Note** This is not an assumption of the paper. It is the extra condition under
which the corrected Proposition 6 and Theorem 1 assert that the third piece of the value function,
`H(x, t) + γ E J((x − w)⁺, t + 1)`, has a Lipschitz derivative (see `PieceDerivBound`); the other
pieces have one unconditionally. It holds in the paper's examples, where
`∂ₓₓH = (p ± q) f` is bounded. -/
def HDerivLipschitz (mdl : ResetModel) (t : ℕ) : Prop :=
  ∃ (H' : ℝ → ℝ) (C : ℝ), ∀ z ∈ Set.Icc 0 mdl.cmax,
    HasDerivWithinAt (fun y => mdl.H y t) (H' z) (Set.Icc 0 mdl.cmax) z ∧
    ∀ z' ∈ Set.Icc 0 mdl.cmax, |H' z - H' z'| ≤ C * |z - z'|

end ResetInventory


