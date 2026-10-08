-- Prove2me | Definitions.Def_GivenDegreeSeq_GraphLimit_Phi
-- name    : GivenDegreeSeq_GraphLimit_Phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:28.834957+00:00
-- url     : https://prove2.me/theorems/7a4b5aaf-ca38-4fb3-b717-0f9f73433d1b
-- title:
--   The map $\varphi$ of (4)–(5) and the quantity $E(B)$ of §6.2
-- statement:
--   Let $n\ge1$, $d=(d_1,\dots,d_n)\in\mathbb R^n$ and $x\in\mathbb R^n$.
--
--   1. For $i\ne j$ put $r_{ij}(x)=\dfrac{1}{e^{-x_j}+e^{x_i}}$ (4), and define $\varphi:\mathbb R^n\to\mathbb R^n$ by
--   $$\varphi_i(x)=\log d_i-\log\sum_{j\ne i}r_{ij}(x). \tag{5}$$
--   2. For $B\subseteq\{1,\dots,n\}$,
--   $$E(B):=\sum_{j\notin B}\min\{d_j,|B|\}+|B|(|B|-1)-\sum_{i\in B}d_i .$$
--
--   The fixed points of $\varphi$ are the solutions of the β-model maximum likelihood equations, and the iteration $x\mapsto\varphi(x)$ is used in the proof of Theorem 1.1 to compare the MLEs for different $n$. $E(B)$ is the Erdős–Gallai slack of the set $B$; its minimum over $|B|\ge bn$ controls the existence of the MLE.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` (vertices $0,\dots,n-1$). `Real.log` takes the value $0$ at $0$, so $\varphi$ is meaningful only for $d_i>0$; Lemma 2.2 needs no condition because the terms $\log d_i$ cancel in $\varphi(x)-\varphi(y)$. $E(B)$ is computed in $\mathbb R$. The bodies of $r$, $\varphi$ agree with missions 1 and 3; $E$ agrees with mission 3's `slack`.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 8 (Eqs. (4)–(5)) and p. 30 (§6.2, E(B))

import Mathlib

namespace GivenDegreeSeq.GraphLimit

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5: the functions `r_ij` and `φ` of (4)–(5) (p. 8), used by Lemma 2.2 (p. 14),
and the Erdős–Gallai-type quantity `E(B)` of §6.2 (p. 30).

Vertices `1, …, n` of the paper are `Fin n = {0, …, n − 1}`; vectors of `ℝⁿ` are
`Fin n → ℝ`, whose Mathlib norm is the sup norm `|x|∞ = max_i |x_i|`.
(`r`, `phi` have the same bodies as in missions 1 and 3 of this series; `slackE` has the same
body as `GivenDegreeSeq.MLE.slack` of mission 3.) -/

/-- `r_ij(x) = 1/(e^{−x_j} + e^{x_i})`, eq. (4) (p. 8). -/
noncomputable def r {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  1 / (Real.exp (-x j) + Real.exp (x i))

/-- The map `φ : ℝⁿ → ℝⁿ` with `φ_i(x) = log d_i − log Σ_{j ≠ i} r_ij(x)`, eq. (5) (p. 8),
for a degree vector `d`. -/
noncomputable def phi {n : ℕ} (d : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.log (d i) - Real.log (∑ j ∈ Finset.univ.erase i, r x i j)

/-- The quantity of §6.2 (p. 30):
`E(B) := Σ_{j ∉ B} min{d_j, |B|} + |B|(|B| − 1) − Σ_{i ∈ B} d_i`, computed in `ℝ`. -/
noncomputable def slackE {n : ℕ} (d : Fin n → ℝ) (B : Finset (Fin n)) : ℝ :=
  ∑ j ∈ Bᶜ, min (d j) (B.card : ℝ) + (B.card : ℝ) * ((B.card : ℝ) - 1) - ∑ i ∈ B, d i

end GivenDegreeSeq.GraphLimit


