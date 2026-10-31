-- Prove2me | Definitions.Def_TestScoreSubmod_mask
-- name    : TestScoreSubmod_mask
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:47.032537+00:00
-- url     : https://prove2.me/theorems/2f0d2546-0c0b-4b6d-b0c3-9e0bf5f34104
-- title:
--   The mask $M_S$
-- statement:
--   For a set $S$ of items and a performance vector $x$, the vector $M_S(x)$ keeps the coordinates of the items in $S$ and replaces every other coordinate by $\varphi=0$:
--
--   $$
--   M_S(x)_i=\begin{cases}x_i,& i\in S,\\ 0,& i\notin S.\end{cases}
--   $$
--
--   The value of a set $S$ at performances $x$ is $g(M_S(x))$.
--
--   **Formalization Note** The paper's minimal element $\varphi$ is taken to be $0$, the least element of $\mathbb R_+$ and the paper's own choice for $g=\max$.
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, §2.1, p.11

import Mathlib

open scoped NNReal

namespace TestScoreSubmod

/-- **The mask `M_S`** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, §2.1, p.11: "M_S(x)_i = x_i
if i ∈ S and M_S(x) = φ, otherwise").

`mask S x` keeps the coordinates of `x` indexed by `S` and sets every other coordinate to `0`.

**Formalization Note** The minimal element `φ` of p.11 is taken to be `0`, the minimal element
of the domain `ℝ₊` (the paper's own example, `g = max`, uses `φ = 0`). -/
def mask {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ≥0) : ι → ℝ≥0 :=
  fun i => if i ∈ S then x i else 0

end TestScoreSubmod


