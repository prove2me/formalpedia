-- Prove2me | Definitions.Def_GivenDegreeSeq_MLE_Basic
-- name    : GivenDegreeSeq_MLE_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:38.407426+00:00
-- url     : https://prove2.me/theorems/79e27a11-b281-419d-857d-40556631c22e
-- title:
--   The $\beta$-model edge probabilities, the ML equations (3), $r_{ij}$ and $\varphi$ of (4)–(5), the expected degrees $\bar d_i$ and the slack $g(d,B)$
-- statement:
--   Fix $n$ vertices $1,\dots,n$ and a vector $\beta=(\beta_1,\dots,\beta_n)\in\mathbb R^n$. In the **$\beta$-model** an edge between distinct vertices $i$ and $j$ is present with probability
--   $$p_{ij}(\beta)=\frac{e^{\beta_i+\beta_j}}{1+e^{\beta_i+\beta_j}}.$$
--
--   1. Given numbers $d_1,\dots,d_n$ (the degrees of an observed graph), the **maximum likelihood (ML) equations** (3) for $\hat\beta\in\mathbb R^n$ are
--   $$d_i=\sum_{j\ne i}\frac{e^{\hat\beta_i+\hat\beta_j}}{1+e^{\hat\beta_i+\hat\beta_j}},\qquad i=1,\dots,n.$$
--   2. For $1\le i\ne j\le n$ and $x\in\mathbb R^n$, eq. (4) sets $r_{ij}(x):=1/(e^{-x_j}+e^{x_i})$.
--   3. Eq. (5) defines $\varphi:\mathbb R^n\to\mathbb R^n$ componentwise by $\varphi_i(x):=\log d_i-\log\sum_{j\ne i}r_{ij}(x)$.
--   4. The **expected degree** of vertex $i$ under the $\beta$-model is
--   $$\bar d_i:=\sum_{j\ne i}\frac{e^{\beta_i+\beta_j}}{1+e^{\beta_i+\beta_j}}.$$
--   5. For a vector $d\in\mathbb R^n$ and a set $B\subseteq\{1,\dots,n\}$, the **slack**
--   $$g(d_1,\dots,d_n,B):=\sum_{j\notin B}\min\{d_j,|B|\}+|B|(|B|-1)-\sum_{i\in B}d_i.$$
--   For the degree sequence of a graph this quantity is nonnegative for every $B$ (the Erdős–Gallai inequality); Lemmas 4.1 and 4.2 ask for it to be of order $n^2$ on all large sets $B$.
--
--   These are the objects in which the existence and consistency of the $\beta$-model maximum likelihood estimate are stated.
--
--   **Formalization Note** Vertices are `Fin n` $=\{0,\dots,n-1\}$ and vectors are `Fin n → ℝ`; Mathlib's norm on this type is the sup norm $|x|_\infty$. The degrees $d$ are real numbers; statements about $\varphi$ assume $d_i>0$ (otherwise $\log d_i$ is Lean's junk value $\log 0=0$). The slack is computed in $\mathbb R$, with $|B|-1$ a real subtraction. The objects $p_{ij}$, (3), $r$ and $\varphi$ have the same bodies as in mission 1 of this series (namespace `GivenDegreeSeq.FixedPoint`).
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 6 (β-model), p. 7 Eq. (3), p. 8 Eqs. (4)–(5), p. 20 (d̄_i and g(d_1,…,d_n,B), proof of Lemma 4.2), p. 16 Lemma 4.1

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

namespace GivenDegreeSeq.MLE

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5: the β-model edge probability (p. 6), the maximum likelihood equations (3)
(p. 7), the functions `r_ij` and `φ` of (4)–(5) (p. 8), the expected degrees `d̄_i` (p. 20)
and the Erdős–Gallai-type slack of Lemmas 4.1–4.2 (pp. 16, 20).

Vertices `1, …, n` of the paper are `Fin n = {0, …, n − 1}`; vectors of `ℝⁿ` are
`Fin n → ℝ`, whose Mathlib norm is the sup norm `|x|∞ = max_i |x_i|`. -/

/-- The expected degree `d̄_i := Σ_{j ≠ i} e^{β_i+β_j}/(1 + e^{β_i+β_j})` of vertex `i`
under the β-model (proof of Lemma 4.2, p. 20). -/
noncomputable def dbar {n : ℕ} (β : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.FixedPoint.edgeProb β i j

/-- The quantity inside the infimum of Lemmas 4.1 and 4.2 (pp. 16, 20), called
`g(d_1, …, d_n, B)` on p. 20:
`Σ_{j ∉ B} min{d_j, |B|} + |B|(|B| − 1) − Σ_{i ∈ B} d_i`, computed in `ℝ`. -/
noncomputable def slack {n : ℕ} (d : Fin n → ℝ) (B : Finset (Fin n)) : ℝ :=
  ∑ j ∈ Bᶜ, min (d j) (B.card : ℝ) + (B.card : ℝ) * ((B.card : ℝ) - 1) - ∑ i ∈ B, d i

end GivenDegreeSeq.MLE


