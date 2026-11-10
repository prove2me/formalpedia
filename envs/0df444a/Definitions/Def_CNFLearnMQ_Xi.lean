-- Prove2me | Definitions.Def_CNFLearnMQ_Xi
-- name    : CNFLearnMQ_Xi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:31.830942+00:00
-- url     : https://prove2.me/theorems/f2cc4121-a8bf-43bf-ae04-55c77155b1eb
-- title:
--   Inverse $G$ of the binary entropy on $[0,1/2]$, and $\Xi(t)$
-- statement:
--   The **binary entropy function** in base 2 is
--   $$H(x) = -x\log x-(1-x)\log(1-x),\qquad x\in[0,1],$$
--   with the convention $0\log 0=0$. It is concave, symmetric about $1/2$, and strictly increasing on $[0,1/2]$ from $H(0)=0$ to $H(1/2)=1$. For $y\in[0,1]$, $G(y)$ is the inverse of $H$ restricted to $[0,1/2]$: the unique $x\in[0,1/2]$ with $H(x)=y$. For $t\ge 1$ the paper defines
--   $$\Xi(t)=\left\lceil \frac{t-1}{t}\cdot\frac{1}{G(1/t)}\right\rceil .$$
--   $\Xi(1)=0$, and $\Xi(t)=\Theta(t\log t)$ as $t\to\infty$. The exponents of the running time, sample and query bounds of the main theorem are $1+\Xi(t)$, $2+\Xi(t)$, $3+\Xi(t)$ and $2+2\Xi(t)$.
--
--   **Formalization Note** $H$ is the published `SelectiveDPT.H2` (Mathlib's natural-log binary entropy divided by $\ln 2$). $G(y)$ is defined as the infimum of $\{x\in[0,1/2] : y\le H(x)\}$, which equals the inverse on $[0,1]$ by continuity and monotonicity of $H$; values outside $[0,1]$ are never used. $\Xi(t)$ is a natural number.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), §3.3 and eq. (2), p.14

import Mathlib
import Definitions.Def_SelectiveDPT_H2

set_option autoImplicit false

namespace CNFLearnMQ

/-- `G`, the inverse of the binary entropy `H(x) = −x log x − (1 − x) log(1 − x)` (base 2, `0 log 0 = 0`)
restricted to `[0, 1/2]` (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and
Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…), §3.3, p.14: "For x ∈ [0, 1],
let G(x) be the inverse function of H on [0, 1/2]"). `H` is the published `SelectiveDPT.H2`
(`Real.binEntropy / log 2`).

**Formalization Note** `G y` is the least `x ∈ [0, 1/2]` with `y ≤ H(x)`. Since `H` is continuous and
strictly increasing from `H(0) = 0` to `H(1/2) = 1` on `[0, 1/2]`, this is the unique `x ∈ [0, 1/2]`
with `H(x) = y` for every `y ∈ [0, 1]`, i.e. the paper's `G`. Outside `[0, 1]` the value is a junk
value that no statement of the mission uses (the arguments are always `1/t` with `t ≥ 1`). -/
noncomputable def G (y : ℝ) : ℝ := sInf {x : ℝ | x ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ y ≤ SelectiveDPT.H2 x}

/-- `Ξ(t) = ⌈((t − 1)/t) · 1/G(1/t)⌉` for `t ≥ 1`, eq. (2), p.14.

**Formalization Note** The value is a natural number (`Nat.ceil`); for `t ≥ 1` the argument of the
ceiling is `≥ 0`, so this is the paper's ceiling. `Ξ(1) = 0` (p.20) because the numerator vanishes.
The exponents `n^{1+Ξ(t)}` etc. of the mission use this natural number. -/
noncomputable def Xi (t : ℝ) : ℕ := ⌈(t - 1) / t * (1 / G (1 / t))⌉₊

end CNFLearnMQ


