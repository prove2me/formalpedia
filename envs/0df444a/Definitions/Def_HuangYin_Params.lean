-- Prove2me | Definitions.Def_HuangYin_Params
-- name    : HuangYin_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:33:15.904265+00:00
-- url     : https://prove2.me/theorems/a02833f5-cc31-47ae-a2d2-0e444378b8c2
-- title:
--   Primitives of the two-period probabilistic selling model
-- statement:
--   The model of Huang and Yin has a firm selling two versions $H$ and $L$ of a product over two periods, to a unit mass of new customers in each period. Its primitives are the real numbers
--
--   1. $v_H$ and $v_L$, the customers' valuations of product $H$ and product $L$, with $v_H > v_L$;
--   2. $c_H$ and $c_L$, the firm's marginal costs of offering $H$ and $L$, with $c_H > c_L$;
--   3. $\alpha\in[0,1]$, the probability that any one of a second-period customer's anecdotes comes from the first period.
--
--   A parameter record collects these five numbers together with the paper's standing assumptions $v_H>v_L$, $c_H>c_L$ and $0\le\alpha\le1$.
--
--   Every object of the mission is a function of this record.
--
--   **Formalization Note** No sign condition is imposed on the margins $v_H-c_H$, $v_L-c_L$ or $v_{HL}-c_L$: the paper states none. The number of anecdotes $K$ and the prior belief $\xi_0$ are not fields, since the mission treats $K=1$ and $\xi_0=0$.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §3, p. 7, and §3.1, p. 8 (model primitives)

import Mathlib

namespace HuangYin

/-- **The model primitives** (§3, p. 7, and §3.1, p. 8; unnumbered).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), §3 "Basic Model and Preliminaries", p. 7, and §3.1, p. 8.

A firm sells two versions `H` and `L` of a product over two periods, to a unit mass of new
customers in each period.

* `vH`, `vL` — the customers' valuations of product `H` and product `L`, with `vH > vL` (p. 7);
* `cH`, `cL` — the firm's marginal costs of offering `H` and `L`, with `cH > cL` (p. 7);
* `α` — the probability that any one of a second-period customer's anecdotes comes from the
  first period, `0 ≤ α ≤ 1` (p. 8).

The four fields `hv`, `hc`, `hα0`, `hα1` are exactly the paper's standing assumptions.

**Formalization Note.** No sign condition is imposed on margins such as `vL - cL`; the paper
states none. The number of anecdotes `K` and the prior belief `ξ0` are not fields: this mission is
the case `K = 1`, `ξ0 = 0` (see `estimate`). -/
structure Params where
  /-- valuation of product `H` -/
  vH : ℝ
  /-- valuation of product `L` -/
  vL : ℝ
  /-- marginal cost of product `H` -/
  cH : ℝ
  /-- marginal cost of product `L` -/
  cL : ℝ
  /-- probability that a second-period anecdote comes from period 1 -/
  α : ℝ
  /-- `vH > vL` (p. 7) -/
  hv : vL < vH
  /-- `cH > cL` (p. 7) -/
  hc : cL < cH
  /-- `0 ≤ α` (p. 8) -/
  hα0 : 0 ≤ α
  /-- `α ≤ 1` (p. 8) -/
  hα1 : α ≤ 1

end HuangYin


