-- Prove2me | Definitions.Def_MaxEntSampling_GammaS
-- name    : MaxEntSampling_GammaS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:27.012984+00:00
-- url     : https://prove2.me/theorems/75eb99b7-79b8-40cf-a25f-9f7b6e27865f
-- title:
--   $\Gamma_s(X)$ (Definition 2)
-- statement:
--   For a $d\times d$ matrix $X\succeq 0$ with eigenvalues $\lambda_1\ge\cdots\ge\lambda_d\ge 0$ and $k$ the index of Lemma 2,
--
--   $$
--   \Gamma_s(X) := \log\Bigl(\prod_{i\in[k]}\lambda_i\Bigr) + (s-k)\log\Bigl(\frac{1}{s-k}\sum_{i\in[k+1,d]}\lambda_i\Bigr).
--   $$
--
--   It is the objective of the primal characterization PC (9) and equals $\log\det^s(X)$ when $\operatorname{rank}X\le s$ (Appendix A.4); it is $-\infty$ when $\operatorname{rank} X<s$.
--
--   **Formalization Note** The value lies in the extended reals with $\log 0=-\infty$ and is computed as $\log\bigl(\prod_{i\in[k]}\lambda_i\cdot(\frac1{s-k}\sum_{i\in[k+1,d]}\lambda_i)^{s-k}\bigr)$ with `ENNReal.log ∘ ENNReal.ofReal`; for nonnegative factors and $s-k\ge1$ this equals the displayed sum on every input, including $-\infty$.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Definition 2, p.8 (PDF p.8)

import Mathlib
import Definitions.Def_MaxEntSampling_eigDesc
import Definitions.Def_MaxEntSampling_kIdx

open Finset

namespace MaxEntSampling

/-- **`Γ_s(X)` (Definition 2).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Definition 2, p.8 (PDF p.8): "For a d × d matrix X ⪰ 0 with its eigenvalues
λ1 ≥ ··· ≥ λd ≥ 0, let us denote
Γs(X) := log(∏_{i∈[k]} λi) + (s − k) log((1/(s−k)) Σ_{i∈[k+1,d]} λi),
where the unique integer k is defined in Lemma 2."

With `λ = eigDesc X` and `k = kIdx s λ`,
`GammaS s X = log ( ∏_{i∈[k]} λ_i · ((1/(s−k)) Σ_{i∈[k+1,d]} λ_i)^{s−k} )`.

**Formalization Note.** The value lies in `EReal` with `log 0 = −∞` (`ENNReal.log ∘ ENNReal.ofReal`),
the convention of Appendix A.4, p.45, where `Γ_s(X) = −∞` when `rank X < s`. For `X ⪰ 0` the
factors are nonnegative and `s − k ≥ 1`, so `log(a · b^{s−k}) = log a + (s−k) log b` in the
extended reals; the two forms take the same value on every input, including `−∞`. The 1-based
ranges `[k]` and `[k+1, d]` are the 0-based ranges `i.val < k` and `k ≤ i.val`. -/
noncomputable def GammaS {d : ℕ} (s : ℕ) (X : Matrix (Fin d) (Fin d) ℝ) : EReal :=
  ENNReal.log (ENNReal.ofReal
    ((∏ i ∈ univ.filter (fun i : Fin d => i.val < kIdx s (eigDesc X)), eigDesc X i) *
      ((∑ i ∈ univ.filter (fun i : Fin d => kIdx s (eigDesc X) ≤ i.val), eigDesc X i) /
          ((s : ℝ) - kIdx s (eigDesc X))) ^ (s - kIdx s (eigDesc X))))

end MaxEntSampling


