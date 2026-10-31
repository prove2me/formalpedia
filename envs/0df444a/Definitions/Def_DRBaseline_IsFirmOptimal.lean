-- Prove2me | Definitions.Def_DRBaseline_IsFirmOptimal
-- name    : DRBaseline_IsFirmOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:18.476042+00:00
-- url     : https://prove2.me/theorems/87e8ce31-d88b-407c-b624-0abcb06041d2
-- title:
--   Firm-optimal baseline and rebate $(b^*,r^*)\in\arg\max C$
-- statement:
--   A pair $(b,r)$ is **firm-optimal** if $b\ge0$, $r\ge0$ and $C(b',r')\le C(b,r)$ for all $b'\ge0$, $r'\ge0$: it maximizes the net cost savings, equivalently minimizes the total cost $C_u=\bar C-C$.
--
--   **Formalization Note** The domain is the closed quadrant; a negative rebate would be a charge, outside the model. For $\Delta c\ge4\Omega c_s$ the maximizer is not unique.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §5.2, p.15

import Mathlib
import Definitions.Def_DRBaseline_netSavings

namespace DRBaseline

/-- **`(b, r)` maximizes the firm's net savings, `(b∗, r∗) = arg max_{b,r} C(b, r)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §5.2, p.15: "The utility firm's problem is then given by max_{b,r} C(b,r). Let
(b∗,r∗) .= arg max_{b,r} C(b,r)." By §3.4, p.10, this is the same as minimizing `C_u`.

`IsFirmOptimal Ω ρ Δc s b r`: `b ≥ 0`, `r ≥ 0` and `C(b', r') ≤ C(b, r)` for every
`b' ≥ 0`, `r' ≥ 0`.

**Formalization Note** The firm's domain is the closed quadrant `b ≥ 0`, `r ≥ 0` (a negative
rebate is a charge, outside the model). The maximizer is not unique when `Δc ≥ 4Ωc_s`, so this
is a predicate. -/
def IsFirmOptimal (Ω ρ Δc : ℝ) (s : ℝ → ℝ → ℝ → ℝ) (b r : ℝ) : Prop :=
  0 ≤ b ∧ 0 ≤ r ∧
    ∀ b' r' : ℝ, 0 ≤ b' → 0 ≤ r' → netSavings Ω ρ Δc s b' r' ≤ netSavings Ω ρ Δc s b r

end DRBaseline


