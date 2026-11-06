-- Prove2me | Definitions.Def_CoverModular_alphaBar
-- name    : CoverModular_alphaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:32.551205+00:00
-- url     : https://prove2.me/theorems/7d9a3092-dcb8-4e51-a1ff-f9316d8b614a
-- title:
--   Primal-derived dual values $\bar\alpha^{\mathcal S}_i,\bar\beta^{\mathcal S}_j$ (display (6))
-- statement:
--   Let $x=x^{\mathcal S}$ be a primal solution of (3) for $\mathcal A=\mathcal S$ and let $P$ be a constant (the paper's "large constant bigger than $p_{ij}$ for all $(i,j)$"). Define
--
--   $$
--   \bar\alpha^{\mathcal S}_i=\begin{cases}\dfrac{\sum_{j'}p_{ij'}x_{ij'}}{c_i},& c_i>0,\\[4pt] P,& c_i=0,\end{cases}\qquad
--   \bar\beta^{\mathcal S}_j=\begin{cases}\dfrac{\sum_{i'}p_{i'j}x_{i'j}}{d_j},& d_j>0,\\[4pt] P,& d_j=0.\end{cases}
--   $$
--
--   They are the profit generated per unit of capacity at supply node $i$ and per unit of demand at demand node $j$. The paper shows they form a dual feasible solution of (4) whose objective is $2f(\mathcal S)$; this is the source of the cover factor $2$.
--
--   **Formalization Note** The set $\mathcal S$ enters only through $x$, which is an argument; optimality of $x$ and the bounds on $P$ are hypotheses of the theorems. The second branch is taken when $c_i>0$ fails, which under $c\ge0$ means $c_i=0$ (likewise for $d_j$).
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.1, display (6), p.11

import Mathlib

namespace CoverModular

variable {I J : Type} [Fintype I] [Fintype J]

/-- The primal-derived dual value `ᾱ^𝒮_i` of (6) (DeValve, Pekeč, Wei, SSRN 3844987, §3.1,
display (6), p.11): for a primal solution `x` (the paper's `x^𝒮`, an optimal solution of (3)
for `𝒜 = 𝒮`) and the constant `P`,
`ᾱ_i = (∑_{j'} p_ij' x_ij') / c_i` if `c_i > 0`, and `ᾱ_i = P` if `c_i = 0`.

**Formalization Note** The set `𝒮` enters only through `x`, which is passed directly; the
optimality of `x` and the bounds on `P` are hypotheses of the theorems that use `ᾱ`. The
`else` branch is taken when `¬ 0 < c i`, which under the standing assumption `c ≥ 0` is
exactly `c i = 0`. -/
noncomputable def alphaBar (c : I → ℝ) (p : I → J → ℝ) (P : ℝ) (x : I → J → ℝ) (i : I) : ℝ :=
  if 0 < c i then (∑ j, p i j * x i j) / c i else P

/-- The primal-derived dual value `β̄^𝒮_j` of (6) (SSRN 3844987, display (6), p.11):
`β̄_j = (∑_{i'} p_i'j x_i'j) / d_j` if `d_j > 0`, and `β̄_j = P` if `d_j = 0`. -/
noncomputable def betaBar (d : J → ℝ) (p : I → J → ℝ) (P : ℝ) (x : I → J → ℝ) (j : J) : ℝ :=
  if 0 < d j then (∑ i, p i j * x i j) / d j else P

end CoverModular


