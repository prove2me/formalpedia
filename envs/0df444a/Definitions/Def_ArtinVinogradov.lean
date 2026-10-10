-- Prove2me | Definitions.Def_ArtinVinogradov
-- name    : ArtinVinogradov
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T14:50:55.660547+00:00
-- url     : https://prove2.me/theorems/5a129f73-d86b-4ac4-aeb5-ebc0f37fd30c
-- title:
--   Vinogradov's mean value count J_{s,k}(M) and the Weyl sum S(α), as in §3 of OpenAI's Prime Predecessors paper
-- statement:
--   Two objects of Vinogradov's method, used by `vinogradov_mean_value` and `weylSum_box_sup_moment`.
--
--   - `vinogradovCount s k M` is $J_{s,k}(M)$: the number of pairs of $s$-tuples $u, v$ of integers in $[1, M]$ with $\sum_{i=1}^s u_i^j = \sum_{i=1}^s v_i^j$ for $1 \le j \le k$. A tuple entry `i : Fin M` stands for the integer $i + 1$.
--   - `weylSum M k α` is $S(\alpha) = \sum_{h=1}^{M} e\bigl(\sum_{j=1}^{k}\alpha_j h^j\bigr)$, with $e(t) = \exp(2\pi i t)$ and $\alpha \in \mathbb R^k$; the coordinate `j : Fin k` of `α` is the coefficient of $h^{j+1}$.
--
--   OpenAI, *Prime Predecessors with an Even Number of Prime Factors* (2026), p. 4: “For integers $k \ge 2$, $s \ge 1$, and $M \ge 1$, let $J_{s,k}(M)$ count the solutions of $\sum_{i=1}^s u_i^j = \sum_{i=1}^s v_i^j$ $(1 \le j \le k)$, $1 \le u_i, v_i \le M$.” On p. 7: “$S(\boldsymbol\alpha) = \sum_{h=1}^{M} e\Bigl(\sum_{j=1}^{k}\alpha_j h^j\Bigr)$”.
-- source:
--   OpenAI, Prime Predecessors with an Even Number of Prime Factors, OpenAI Math Release preprint, September 17, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf (Apache-2.0), p. 4, 7, §3 (Vinogradov count J_{s,k}(M), Weyl sum S(α))

import Mathlib

namespace ArtinPrimitiveRoots

open Real

open Classical in
/-- Vinogradov's count `J_{s,k}(M)`: the number of pairs of `s`-tuples `u, v` of integers in
`[1, M]` with `∑ᵢ uᵢ^j = ∑ᵢ vᵢ^j` for `1 ≤ j ≤ k`. A tuple entry `i : Fin M` stands for the integer
`i + 1`. -/
noncomputable def vinogradovCount (s k M : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin s → Fin M)) ×ˢ (Finset.univ : Finset (Fin s → Fin M))).filter
    (fun uv : (Fin s → Fin M) × (Fin s → Fin M) => ∀ j ∈ Finset.Icc 1 k,
      ∑ i, ((uv.1 i : ℕ) + 1) ^ j = ∑ i, ((uv.2 i : ℕ) + 1) ^ j)).card

/-- The Weyl sum `S(α) = ∑_{h=1}^{M} e(∑_{j=1}^{k} α_j h^j)`, `e(t) = exp(2πit)`; coordinate
`j : Fin k` of `α` is the coefficient of `h^(j+1)`. -/
noncomputable def weylSum (M k : ℕ) (α : Fin k → ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 M,
    Complex.exp (2 * π * Complex.I * ((∑ j : Fin k, α j * (h : ℝ) ^ (j.val + 1) : ℝ) : ℂ))

end ArtinPrimitiveRoots


