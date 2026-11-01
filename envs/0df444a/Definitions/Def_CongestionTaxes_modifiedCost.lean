-- Prove2me | Definitions.Def_CongestionTaxes_modifiedCost
-- name    : CongestionTaxes_modifiedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:45.628022+00:00
-- url     : https://prove2.me/theorems/472c0a54-d0da-44a0-86fa-6f290dcb0499
-- title:
--   Modified resource cost $f(x,v)$ of Definition 4
-- statement:
--   Given a resource cost $\ell$ and a parameter $v\ge0$, the **modified resource cost** is $f(x,0)=\ell(x)$, $f(0,v)=0$, and for $x\ge1$, $v>0$,
--
--   $$
--   f(x,v)=\frac{(x-1)!}{v^x}\sum_{i=0}^{x-1}\frac{p(v)-i\ell(i)}{i!}\,v^i ,
--   $$
--
--   with $p$ the Poisson expected cost (10). When the tax of Definition 4 is added, a user of a resource with $x$ users perceives the cost $\ell(x)+\tau(x,v)=f(x,v)$.
--
--   **Formalization Note** The case $v=0$ is tested first; at $(0,0)$ both printed cases give $0$ since $\ell(0)=0$. Formula (11) is printed for $x\in\mathbb N_0$, but $(x-1)!$ is undefined at $x=0$, where the case $f(0,v)=0$ applies.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, Definition 4 and display (11), p.18

import Mathlib
import Definitions.Def_CongestionTaxes_poissonValue

namespace CongestionTaxes

/-- The **modified resource cost** `f(x, v)` of Definition 4 (Paccagnan, Gairing,
arXiv:2105.07480v2, Definition 4 and display (11), p.18): for a cost `ℓ` and a parameter `v ≥ 0`,
`f(x, 0) = ℓ(x)`, `f(0, v) = 0`, and for `x ≥ 1`, `v > 0`,
`f(x, v) = ((x − 1)! / v^x) ∑_{i=0}^{x−1} ((p(v) − i ℓ(i)) / i!) vⁱ`, with `p` from (10).
It is the cost a user of the resource perceives once the tax is added: `ℓ(x) + τ(x, v) = f(x, v)`.

**Formalization Note** The case `v = 0` is tested first; at `(0, 0)` both printed cases give `0`
because `ℓ(0) = 0` (Assumption 1). Formula (11) is printed for `x ∈ ℕ₀`, but `(x − 1)!` is
undefined at `x = 0`, where the case `f(0, v) = 0` applies; the match on `x = n + 1` writes
`(x − 1)! = n!` without natural-number subtraction. Values at `v < 0` are never used. -/
noncomputable def modifiedCost (ℓ : ℕ → ℝ) (x : ℕ) (v : ℝ) : ℝ :=
  if v = 0 then ℓ x else
    match x with
    | 0 => 0
    | n + 1 => (n.factorial : ℝ) / v ^ (n + 1) *
        ∑ i ∈ Finset.range (n + 1), (poissonValue ℓ v - (i : ℝ) * ℓ i) / (i.factorial : ℝ) * v ^ i

end CongestionTaxes


