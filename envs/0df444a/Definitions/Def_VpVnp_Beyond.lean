-- Prove2me | Definitions.Def_VpVnp_Beyond
-- name    : VpVnp_Beyond
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T23:36:07.957837+00:00
-- url     : https://prove2.me/theorems/22f37e91-beba-4c96-a70a-ffb811184143
-- title:
--   The gate threshold $m^{c(\log_2 m)^{1/3}}$
-- statement:
--   The quantitative threshold of the mission's lower bounds. For a real constant $c$ and natural numbers $m$ and $s$, the relation $\mathrm{Beyond}(c,m,s)$ states the strict inequality
--
--   $$m^{\,c\,(\log_2 m)^{1/3}} < s ,$$
--
--   read as: a circuit of $s$ gates for an $m \times m$ target has **more than** $m^{\,c(\log_2 m)^{1/3}}$ gates. Since $m^{\,c(\log_2 m)^{1/3}} = 2^{\,c(\log_2 m)^{4/3}}$, the threshold is quasipolynomial in $m$: it exceeds every fixed polynomial $m^C$ once $m$ is large, which is how the source derives its qualitative separation from this bound.
--
--   **Formalization Note.** The exponentiation is real (`Real.rpow`) and the logarithm is `Real.logb 2`, with $m$ cast from $\mathbb N$ to $\mathbb R$; $s$ is cast to $\mathbb R$ for the comparison. Both operations are total: at $m = 0$ and $m = 1$ the logarithm is $0$, the exponent is $0$ and the threshold reads $1 < s$. The theorems quantify over $m \geq m_0$, so those values never occur.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf Theorem 1.1, p. 2 and Theorem L.1, p. 59; Lean vp-vnp/Statement.lean, def Statement.Beyond

import Mathlib

namespace VpVnp

/-- More than `m ^ (c * (log₂ m) ^ (1/3))` gates. -/
def Beyond (c : ℝ) (m s : ℕ) : Prop := (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s

end VpVnp


