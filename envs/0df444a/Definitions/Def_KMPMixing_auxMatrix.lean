-- Prove2me | Definitions.Def_KMPMixing_auxMatrix
-- name    : KMPMixing_auxMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:20.106548+00:00
-- url     : https://prove2.me/theorems/67243d3f-ecbb-4cbc-b081-7c7d2f19096b
-- title:
--   The auxiliary matrices $A_{e,p}$, $B_k$ and the expectation over $(e_s,p_s)_{s\le k}$
-- statement:
--   For an edge $e=\{a,b\}$ with $a<b$ and $p\in[0,1]$, the $d\times d$ row-stochastic matrix $A_{e,p}$ of Eq. (8) is
--   $$
--   A_{e,p}(i,j)=\begin{cases}p&(i,j)=(a,a)\text{ or }(b,a)\\1-p&(i,j)=(a,b)\text{ or }(b,b)\\1&i=j\notin\{a,b\}\\0&\text{otherwise,}\end{cases}
--   $$
--   the one-step law of a single labeled particle given the edge and the split parameter. For edges $e_1,\dots,e_k$ and parameters $p_1,\dots,p_k$, $B_k=A_{e_1,p_1}A_{e_2,p_2}\cdots A_{e_k,p_k}$ (Eq. (9)), with $B_0=I$.
--
--   The auxiliary randomness of $k$ steps draws the edges $e_1,\dots,e_k$ independently and uniformly from $E$ and the parameters $p_1,\dots,p_k$ independently from $\mathrm{Unif}[0,1]$, independent of the edges. For a function $F$ of the edges and parameters,
--   $$
--   \mathbb E_{\{e_s\},\{p_s\}}[F]=|E|^{-k}\sum_{(e_1,\dots,e_k)\in E^k}\int_{[0,1]^k}F(e,p)\,dp.
--   $$
--
--   These objects express the labeled chain and its stationary law as averages of product measures (Remark 4.3, Observation 4.4, Lemma 4.5).
--
--   **Formalization Note** The orientation of $A_{e,p}$ follows footnote 2 of the paper ($p$ goes to the smaller endpoint). The cube $[0,1]^k$ is `Set.Icc 0 1` in `Fin k → ℝ` with Lebesgue measure, the product of $k$ uniform laws. Every integrand used in the mission is a polynomial in $p$.
-- source:
--   Chen et al., arXiv:2609.38044, Definition 4.2 and Eqs. (8), (9), p.19 (PDF p.21); Observation 4.4, p.20; Eq. (42), p.61

import Mathlib
import Definitions.Def_KMPMixing_kmpChain

namespace KMPMixing

open MeasureTheory

/-- The random row-stochastic matrix `A_{e,p}` of Eq. (8) (arXiv:2609.38044, p.19 (PDF p.21);
restated as Eq. (42), p.61 (PDF p.63)) for the edge `e = {a, b}` written with `a < b` and the
split parameter `p ∈ [0, 1]`: `A(a, a) = A(b, a) = p`, `A(a, b) = A(b, b) = 1 − p`,
`A(i, i) = 1` for `i ∉ {a, b}`, and `0` otherwise. It is the one-step transition matrix of a
single labeled particle given the edge and the split parameter (Definition 4.2, p.19).

**Formalization Note** The orientation follows footnote 2 (p.15): the parameter `p` belongs to
the smaller endpoint `a`. -/
def auxMatrix {d : ℕ} (a b : Fin d) (p : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    if i = a ∨ i = b then (if j = a then p else if j = b then 1 - p else 0)
    else (if i = j then 1 else 0)

/-- `B_k = A_1 · A_2 ⋯ A_k` of Eq. (9) (arXiv:2609.38044, p.19 (PDF p.21)), for the edges
`es s = (i_s, j_s)` (with `i_s < j_s`) and the split parameters `ps s` of steps `s = 1, …, k`.
`B_0` is the identity. -/
def auxProd {d k : ℕ} (es : Fin k → Fin d × Fin d) (ps : Fin k → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (List.ofFn fun s : Fin k => auxMatrix (es s).1 (es s).2 (ps s)).prod

/-- The expectation `E_{{i_s,j_s}_{1≤s≤k}, {p_s}_{1≤s≤k}}[F]` over the auxiliary randomness of
`k` steps of the labeled chain (arXiv:2609.38044, Definition 4.2 and Observation 4.4, pp.19–20
(PDF pp.21–22)): the edges `e_1, …, e_k` are independent and uniform on `E`, the parameters
`p_1, …, p_k` are independent `Unif[0, 1]` and independent of the edges, one pair `(e_s, p_s)`
per step:
`E[F] = |E|^{-k} Σ_{(e_1,…,e_k) ∈ E^k} ∫_{[0,1]^k} F(e, p) dp`.

**Formalization Note** The `k` uniform edges are a finite average over `(edgePairs G)^k`; the
`k` uniform parameters are Lebesgue measure on the cube `[0,1]^k = Set.Icc 0 1 ⊆ (Fin k → ℝ)`,
which is the product of `k` copies of `Unif[0, 1]`. Every integrand used in the mission is a
polynomial in `p`, hence integrable on the cube. -/
noncomputable def auxExpect {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] (k : ℕ)
    (F : (Fin k → Fin d × Fin d) → (Fin k → ℝ) → ℝ) : ℝ :=
  ((edgePairs G).card : ℝ)⁻¹ ^ k *
    ∑ es ∈ Fintype.piFinset (fun _ : Fin k => edgePairs G),
      ∫ ps in Set.Icc (0 : Fin k → ℝ) 1, F es ps

end KMPMixing


