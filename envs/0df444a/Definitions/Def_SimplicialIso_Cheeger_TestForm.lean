-- Prove2me | Definitions.Def_SimplicialIso_Cheeger_TestForm
-- name    : SimplicialIso_Cheeger_TestForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:02.96738+00:00
-- url     : https://prove2.me/theorems/d0fe779c-0304-4ef9-bd70-1346447a5040
-- title:
--   (4.1), p. 12 — the test form f ∈ Ω^{d−1} of a partition A_0, …, A_d
-- statement:
--   Let $A_0,\dots,A_d$ be subsets of the vertex set $V$ (in the paper, a partition of $V$ into nonempty blocks). The **test form** $f\in\Omega^{d-1}$ of equation (4.1) is defined on a $(d-1)$-cell $\sigma=[\sigma_0\,\sigma_1\cdots\sigma_{d-1}]$ by
--   $$f([\sigma_0\,\sigma_1\cdots\sigma_{d-1}])=\begin{cases}\operatorname{sgn}(\pi)\,|A_{\pi(d)}| & \exists\,\pi\in\mathrm{Sym}_{\{0,\dots,d\}}\text{ with }\sigma_i\in A_{\pi(i)}\text{ for }0\le i\le d-1,\\ 0 & \text{else, i.e. }\exists k,\ i\ne j\text{ with }\sigma_i,\sigma_j\in A_k.\end{cases}$$
--   In words: when the vertices of $\sigma$ lie in $d$ distinct blocks, $A_{\pi(d)}$ is the one block that $\sigma$ misses, and $f(\sigma)$ is $\pm$ its size, with the sign of the permutation that lists the blocks of $\sigma_0,\dots,\sigma_{d-1}$ followed by the missing block.
--
--   With the cells oriented by increasing vertex order, $\operatorname{sgn}\pi=(-1)^{N}$ where $N$ is the number of inversions of the sequence $(\pi(0),\dots,\pi(d))$: the pairs $u<w$ in $\sigma$ whose blocks are in decreasing order, plus the vertices of $\sigma$ whose block index exceeds that of the missing block.
--
--   This form is the test vector in the proof of Theorem 1.2: it is a $(d-1)$-cycle, and its Rayleigh quotient for $\Delta^+$ equals the Cheeger ratio of the partition.
--
--   **Formalization Note.** The Lean definition is stated for any family $A$; it agrees with (4.1) when $A$ is a partition. When the vertices of $\sigma$ are in distinct blocks it sums over the blocks disjoint from $\sigma$; for a partition there is exactly one. Sizes are cast to reals.
-- source:
--   Parzanchevski, Rosenthal and Tessler, Isoperimetric inequalities in simplicial complexes, arXiv:1207.0638v3, p. 12, §4.1, equation (4.1)

import Mathlib
import Definitions.Def_SimplicialIso_Cheeger_Setting

namespace SimplicialIso.Cheeger

open Finset

variable {n d : ℕ}

/-- The number of inversions of the block sequence of the increasingly ordered vertex set `σ`:
pairs `u < w` of vertices of `σ` with `u ∈ A_i`, `w ∈ A_j` and `j < i`. -/
def blockInv (A : Fin (d + 1) → Finset (Fin n)) (σ : Finset (Fin n)) : ℕ :=
  ((σ ×ˢ σ).filter (fun p => p.1 < p.2 ∧ ∃ i j, j < i ∧ p.1 ∈ A i ∧ p.2 ∈ A j)).card

/-- The test form `f ∈ Ω^{d-1}` of (4.1). For a `(d-1)`-cell `σ = [σ_0 … σ_{d-1}]` (vertices in
increasing order) whose vertices lie in pairwise distinct blocks, let `A_m` be the block missing
from `σ` and let `π` be the permutation of `{0, …, d}` with `σ_i ∈ A_{π(i)}` for `i < d` and
`π(d) = m`; then `f(σ) = sgn(π) · |A_m|`. Otherwise (two vertices of `σ` in one block)
`f(σ) = 0`. Here `sgn π = (-1)^(inversions of (π(0), …, π(d)))`, the inversions being those of
the block sequence of `σ` (`blockInv`) plus the vertices of `σ` whose block index exceeds `m`. -/
def testForm (A : Fin (d + 1) → Finset (Fin n)) : Form n d :=
  WithLp.toLp 2 (fun σ =>
    if ∀ i, (σ.1 ∩ A i).card ≤ 1 then
      ∑ m ∈ univ.filter (fun m => Disjoint σ.1 (A m)),
        (-1 : ℝ) ^ (blockInv A σ.1 + (σ.1.filter (fun u => ∃ i, m < i ∧ u ∈ A i)).card)
          * ((A m).card : ℝ)
    else 0)

end SimplicialIso.Cheeger


