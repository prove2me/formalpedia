-- Prove2me | Definitions.Def_AdaDiscRL_Assumption1
-- name    : AdaDiscRL_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:33.622577+00:00
-- url     : https://prove2.me/theorems/a773193a-730c-414e-8b2e-8228c8063724
-- title:
--   Assumption 1 (model-free Lipschitz): $Q^\star_h$, $V^\star_h$ are $L_V$-Lipschitz
-- statement:
--   **Assumption 1 (Model-Free Lipschitz).** For every $x,x',a,a'$ and $h$,
--   $$
--   |Q^\star_h(x,a)-Q^\star_h(x',a')|\le L_V\,\mathcal D((x,a),(x',a')),\qquad |V^\star_h(x)-V^\star_h(x')|\le L_V\,\mathcal D_{\mathcal S}(x,x').
--   $$
--   AdaQL is analysed under this assumption, and both algorithms use $L_V$ in their bonuses.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Assumption 1, p.10

import Mathlib
import Definitions.Def_AdaDiscRL_optValue

namespace AdaDiscRL

/-- **Assumption 1 (Model-Free Lipschitz)** (arXiv:2110.15843v3, p.10): `Q⋆_h` and `V⋆_h` are
Lipschitz with respect to `D` and `D_S` with constant `L_V`: for every `x, x′, a, a′, h`,
`|Q⋆_h(x,a) − Q⋆_h(x′,a′)| ≤ L_V D((x,a),(x′,a′))` and `|V⋆_h(x) − V⋆_h(x′)| ≤ L_V D_S(x,x′)`. -/
def Assumption1 {S A : Type*} [MetricSpace S] [MeasurableSpace S] [MeasurableSpace A] {H : ℕ}
    (M : EpisodicMDP S A H) (D : S × A → S × A → ℝ) (LV : ℝ) : Prop :=
  (∀ h p q, |optQ M h p - optQ M h q| ≤ LV * D p q) ∧
  (∀ h x x', |optV M h x - optV M h x'| ≤ LV * dist x x')

end AdaDiscRL


