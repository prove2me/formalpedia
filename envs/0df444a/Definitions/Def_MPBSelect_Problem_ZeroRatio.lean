-- Prove2me | Definitions.Def_MPBSelect_Problem_ZeroRatio
-- name    : MPBSelect_Problem_ZeroRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:26:28.399522+00:00
-- url     : https://prove2.me/theorems/0d1c089e-3576-4f52-b389-834729baa5f2
-- title:
--   The zero asymptotic sampling ratio condition of Theorem 3
-- statement:
--   An allocation $\boldsymbol\alpha$ satisfies the **zero sampling ratio condition** if
--   $$
--   \alpha_{i^*}(\theta_b)=0\qquad\text{for all }\theta_b\in\Theta_{i^*}^c ,
--   $$
--   i.e. the MPB receives no budget at any parameter where it is not the conditional optimum. Equivalently, $\boldsymbol\alpha$ vanishes on $\Xi^{\mathrm{adv}}=\{(i^*,\theta_b):\theta_b\in\Theta^c_{i^*}\}$.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 3, p.17, third bullet; Ξ^adv, p.14

import Mathlib
import Definitions.Def_MPBSelect_Problem

namespace MPBSelect

/-- **Zero asymptotic sampling ratio** of Theorem 3.
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 3, p.17:
"(Zero asymptotic sampling ratio) αi∗(θb) = 0 for all θb ∈ Θc_{i∗}."

The MPB `i*` receives no budget at any parameter `θ_b` outside its favorable set
`Θ_{i*} = {θ_b : i* = i^b}` (3), i.e. at every `θ_b` with `i^b ≠ i*`. Equivalently,
`α` vanishes on `Ξ^adv = {(i*, θ_b) : θ_b ∈ Θ^c_{i*}}` (p.14). -/
def Problem.ZeroRatio {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) : Prop :=
  ∀ b : Fin B, P.ib b ≠ P.istar → α P.istar b = 0

end MPBSelect


