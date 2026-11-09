-- Prove2me | Definitions.Def_LinearChoresCLS_PriceFamily
-- name    : LinearChoresCLS_PriceFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:00.366491+00:00
-- url     : https://prove2.me/theorems/1753e0d9-7037-462c-96c9-d3443cbc27ad
-- title:
--   The price family $p(x)$, its normalization $\tilde p(x)$, and the decoder (7.3)
-- statement:
--   For $x\in[0,1]^n$ the **price family** $p(x)$ has basic prices $p_j(x)=(1+tx_j)/(1+t\bar x)$, and, layer by layer, if a gadget at layer $k$ has input prices $u,v$, its plus and minus outputs have prices
--   $$
--   \frac{\max\{u,v\}}{q_k}\quad\text{and}\quad q_k\min\{u,v\}.
--   $$
--   With $T(x)=\sum_{\ell\in M}S_\ell p_\ell(x)$ the **normalized price family** is $\tilde p(x)=\frac{n+1}{T(x)}p(x)$. The **decoder** maps an equilibrium $(p,z)$ to
--   $$
--   g(I,(p,z))=\frac1t\Big(\frac{p_1}{p_0}-1,\dots,\frac{p_n}{p_0}-1\Big).
--   $$
--
--   The reduction encodes a point $x$ of the box in the prices $\tilde p(x)$ and reads it back with $g$.
--
--   **Formalization Note** `priceFam`, `totalPay`, `normPrice` take general $t,L$; `completedPrice` and `completedNormPrice` are the instances at (7.1). The decoder reads the basic chores `Sum.inl`.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Eqs. (5.2), (6.7), (7.2), (7.3), pp.14, 20, 32

import Mathlib
import Definitions.Def_LinearChoresCLS_CompletedMarket

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

variable {n : ℕ}

/-- The output prices of layer `k` of a gadget chain whose layer-0 inputs have prices `u, v`
(arXiv:2611.06589, held version sha256 85d34a9e…, the max–min rule (6.7), p.20, Remark 6.6, p.22,
and the price mapping of Section 7.1, p.32): if a layer's first and second inputs have prices
`u′, v′`, its plus and minus outputs have prices `max{u′, v′}/q_k` and `q_k min{u′, v′}`; layer
`k + 1` takes the outputs of layer `k` as inputs. The pair is `(plus, minus)`. -/
noncomputable def layerOut (t u v : ℝ) : ℕ → ℝ × ℝ
  | 0 => (max u v / qPar t 0, qPar t 0 * min u v)
  | k + 1 =>
    let o := layerOut t u v k
    (max o.1 o.2 / qPar t (k + 1), qPar t (k + 1) * min o.1 o.2)

/-- The **price family** `p(x)` (before normalization) of the completed market (arXiv:2611.06589,
Section 7.1, Price Mapping, p.32): basic prices `p_j(x) = (1 + t x_j)/(1 + t x̄)` (5.2), and output
prices defined layer by layer from them by the max–min rule (6.7). -/
noncomputable def priceFam (t : ℝ) (L : ℕ) (x : Fin n → ℝ) : Chore n L → ℝ
  | Sum.inl j => basicPrice t x j
  | Sum.inr (π, k, s) =>
    let o := layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k.val
    if s then o.1 else o.2

/-- The total payment `T(x) := ∑_{ℓ ∈ M} S_ℓ p_ℓ(x)` (arXiv:2611.06589, (7.2), p.32, and §6.5,
p.28), with the supplies of `chainMarket`. -/
noncomputable def totalPay (P : Quadratic n) (t : ℝ) (L : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ ℓ, (chainMarket P t L).supply ℓ * priceFam t L x ℓ

/-- The **normalized price family** `p̃(x) := ((n + 1)/T(x)) p(x)` (arXiv:2611.06589, (7.2),
p.32). -/
noncomputable def normPrice (P : Quadratic n) (t : ℝ) (L : ℕ) (x : Fin n → ℝ) :
    Chore n L → ℝ :=
  fun ℓ => (n + 1) / totalPay P t L x * priceFam t L x ℓ

/-- The price family `p(x)` of the completed market `f(I)`, with `t`, `L` from (7.1). -/
noncomputable def completedPrice (P : Quadratic n) (ε : ℚ) (x : Fin n → ℝ) :
    Chore n (chainLength P ε) → ℝ :=
  priceFam (tParam P ε) (chainLength P ε) x

/-- The normalized price family `p̃(x)` of the completed market `f(I)` (arXiv:2611.06589, (7.2),
p.32), with `t`, `L` from (7.1). -/
noncomputable def completedNormPrice (P : Quadratic n) (ε : ℚ) (x : Fin n → ℝ) :
    Chore n (chainLength P ε) → ℝ :=
  normPrice P (tParam P ε) (chainLength P ε) x

/-- The **decoder** (7.3) (arXiv:2611.06589, p.32):
`g(I, (p, z)) := (1/t)(p₁/p₀ − 1, …, pₙ/p₀ − 1)`, reading the basic chore prices. -/
noncomputable def decoder {L : ℕ} (t : ℝ) (p : Chore n L → ℝ) : Fin n → ℝ :=
  fun i => (1 / t) * (p (Sum.inl i.succ) / p (Sum.inl 0) - 1)

end LinearChoresCLS


