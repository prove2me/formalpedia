-- Prove2me | Definitions.Def_NullConeGravity_dilog
-- name    : NullConeGravity_dilog
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T14:11:58.705807+00:00
-- url     : https://prove2.me/theorems/b9f5cd33-b8b9-5895-b492-9a4e6cd4422e
-- title:
--   Dilogarithm $\operatorname{Li}_2$
-- statement:
--   The **dilogarithm** is the special function
--
--   $$ \operatorname{Li}_2(z) = \sum_{n=1}^{\infty} \frac{z^n}{n^2}, \qquad z \in \mathbb{C}. $$
--
--   Here the sum is indexed by $k \in \mathbb{N}$ with $n = k+1$. On the unit circle $|z|=1$ the series converges absolutely, since $\sum 1/n^2 < \infty$; this is the regime in which the graviton-pair amplitude of the source paper evaluates it, at $z = e^{-2i/s}$.
--
--   This definition supplies the closed form in which the connected graviton pair creation–annihilation amplitude on a null cone is expressed (Section 4.4 of the source). It is reusable wherever a weight-two polylogarithm series is needed.
--
--   **Formalization Note.** The series is a `tsum` over `ℕ`; as a total function it returns `0` when the series is not summable, so theorems using it assert summability explicitly where needed.
-- source:
--   V. Chandrasekaran, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924, Section 4.4, Eq. (4.33)

import Mathlib

namespace NullConeGravity

/-- The dilogarithm `Li₂(z) = ∑_{n≥1} z^n / n²`, indexed over `ℕ` with `n = k+1`. -/
noncomputable def dilog (z : ℂ) : ℂ := ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ 2

end NullConeGravity


