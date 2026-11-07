-- Prove2me | Definitions.Def_ShortBroadcastDom_HasSlack
-- name    : ShortBroadcastDom_HasSlack
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:34.863632+00:00
-- url     : https://prove2.me/theorems/81c9e319-3c48-477e-bf9a-1a1ef70b08fa
-- title:
--   Slack of a rounding rule: $\mathcal C(x)\ge(1+\delta)|D(x)|$ for every feasible $x$
-- statement:
--   Consider a covering program and a **rounding rule** that maps every feasible fractional solution $x$ to a vertex set $D(x)$. Write $\mathcal C(x)=\sum_v c_vx_v$ for the cost of $x$. The rule **has slack** $\delta$ if $\delta>0$ and
--
--   $$
--   \mathcal C(x)\ge(1+\delta)\,|D(x)|\qquad\text{for every feasible }x.
--   $$
--
--   The saving is proportional to the output size and holds for every feasible input, which is what lets an approximately optimal fractional solution be rounded with an exact coefficient (Proposition 5.1).
--
--   **Formalization Note** The feasible solutions form an abstract type $X$; $\mathcal C$ is a map $X\to\mathbb R$ and $|D(\cdot)|$ a map $X\to\mathbb N$.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.1, p.2 (PDF p.5); §5.3, p.16 (PDF p.19)

import Mathlib

namespace ShortBroadcastDom

/-- **Slack of a rounding rule.** A rounding rule maps every feasible fractional solution `x` (an
element of `X`) to a set `D(x)`; with cost `𝒞(x)`, the rule *has slack* `δ` if `δ > 0` and
`𝒞(x) ≥ (1 + δ)|D(x)|` for every feasible `x`.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §1.1, p.2 (PDF 5), and §5.3, p.16 (PDF 19): "the rule has slack δ > 0 if
C(x) ≥ (1 + δ)|D(x)| for every feasible x".

**Formalization Note** `X` is the type of feasible fractional solutions of the covering program,
`Cx x = 𝒞(x)` and `Dx x = |D(x)|`. -/
def HasSlack {X : Type} (Cx : X → ℝ) (Dx : X → ℕ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ x, (1 + δ) * (Dx x : ℝ) ≤ Cx x

end ShortBroadcastDom


