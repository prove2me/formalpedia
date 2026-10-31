-- Prove2me | Definitions.Def_DRBaseline_IsNormalUseOptimal
-- name    : DRBaseline_IsNormalUseOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:22.908899+00:00
-- url     : https://prove2.me/theorems/51af0cc2-c493-46c4-a336-3c0f32b88870
-- title:
--   Optimal rebate $r_0$ at the normal-use baseline $b=\Lambda$
-- statement:
--   When the baseline is fixed at the customer's average non-event demand $b=\Lambda$, a rebate $r_0$ is **optimal** if $r_0\ge0$ and $C(\Lambda,r')\le C(\Lambda,r_0)$ for every $r'\ge0$. The paper writes $r_0=\arg\max_r C(\Lambda,r)$.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §5.1, p.15

import Mathlib
import Definitions.Def_DRBaseline_netSavings

namespace DRBaseline

/-- **`r₀` is an optimal rebate when the baseline is the normal-use demand `b = Λ`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §5.1, p.15: "the utility firm's problem is then given by max_r C(b,r), where the firm
sets b = Λ … Let r0 .= arg max_r C(Λ,r)."

`IsNormalUseOptimal Ω Λ ρ Δc s r₀`: `r₀ ≥ 0` and `C(Λ, r') ≤ C(Λ, r₀)` for every `r' ≥ 0`.

**Formalization Note** Rebates range over `r ≥ 0`. -/
def IsNormalUseOptimal (Ω Λ ρ Δc : ℝ) (s : ℝ → ℝ → ℝ → ℝ) (r₀ : ℝ) : Prop :=
  0 ≤ r₀ ∧ ∀ r' : ℝ, 0 ≤ r' → netSavings Ω ρ Δc s Λ r' ≤ netSavings Ω ρ Δc s Λ r₀

end DRBaseline


