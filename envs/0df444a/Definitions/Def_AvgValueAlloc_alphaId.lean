-- Prove2me | Definitions.Def_AvgValueAlloc_alphaId
-- name    : AvgValueAlloc_alphaId
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:26.548206+00:00
-- url     : https://prove2.me/theorems/307bb451-1bb9-4a81-809e-1d49788c3825
-- title:
--   Optimal identification success $\alpha_\ell$
-- statement:
--   For $d$ candidates, let $J$ be uniform and observe $\ell$ independent masks $X\in\{0,1\}^d$ with $X_J\sim\mathrm{Ber}(k/T)$ and the other coordinates $\mathrm{Ber}(1/T)$. Then
--   $$
--   \alpha_\ell=\max_{\text{estimators}}\ \Pr\bigl[\widehat J(X^{(1)},\dots,X^{(\ell)})=J\bigr],
--   $$
--   the optimal identification success from $\ell$ pure masks.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §5.1, p.11

import Mathlib

namespace AvgValueAlloc

/-- The probability of `ℓ` pure mask observations `x` over `d` coordinates under hypothesis `J`:
coordinate `J` is `Ber(k/T)`, the others `Ber(1/T)`, all independent. -/
noncomputable def maskProb (k T : ℕ) {d ℓ : ℕ} (J : Fin d) (x : Fin ℓ → Fin d → Bool) : ℝ :=
  ∏ l, ∏ i, (if x l i then (if i = J then (k : ℝ) / T else 1 / (T : ℝ))
    else 1 - (if i = J then (k : ℝ) / T else 1 / (T : ℝ)))

/-- **Optimal identification success `α_ℓ`.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §5.1, p.11: "Choose J uniformly in I. … Let α_ℓ be
optimal identification success from ℓ pure mask observations, without sponsor substitutions."

`alphaId d k T ℓ = max_est (1/d) Σ_J P_J(est(X) = J)`, the best success probability of an
estimator of a uniform `J ∈ [d]` from `ℓ` independent masks `X ∈ {0,1}^d`, whose coordinate `J` is
`Ber(k/T)` and the others `Ber(1/T)`.

**Formalization Note.** A real `⨆` over the finite type of deterministic estimators (randomized
ones are mixtures and do no better); `d = |I|` after relabeling `I` as `Fin d`. -/
noncomputable def alphaId (d k T ℓ : ℕ) : ℝ :=
  ⨆ est : (Fin ℓ → Fin d → Bool) → Fin d,
    (1 / (d : ℝ)) * ∑ J : Fin d, ∑ x : Fin ℓ → Fin d → Bool,
      maskProb k T J x * (if est x = J then 1 else 0)

end AvgValueAlloc


