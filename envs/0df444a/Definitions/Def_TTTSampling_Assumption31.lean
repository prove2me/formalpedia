-- Prove2me | Definitions.Def_TTTSampling_Assumption31
-- name    : TTTSampling_Assumption31
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:54.491201+00:00
-- url     : https://prove2.me/theorems/b490f7e2-c46e-4701-a96b-63eb4f2335ea
-- title:
--   Assumption 3.1 ($\ell_\infty$-closeness of the oracle $\hat\mu$ to $\mu^\star$)
-- statement:
--   Let $\mu^\star$ be a distribution on $\Sigma^n$ and $R>0$. An oracle $\hat\mu:\Sigma^{\le n}\to\mathbb R_{\ge0}$ satisfies **Assumption 3.1** with parameter $R$ if
--
--   1. for every $x\in\Sigma^{\le n}$ (the empty string included),
--   $$
--   \frac1R\;\le\;\frac{\mu^\star(x)}{\hat\mu(x)}\;\le\;R, \tag{9}
--   $$
--   where $0/0$ is read as $1$;
--   2. $\hat\mu(x)=\mu^\star(x)$ for every full string $x\in\Sigma^n$.
--
--   Here $\mu^\star(x)$ is the prefix marginal. The oracle models a learned value function that is accurate up to a multiplicative factor $R$ at every prefix and exact on complete sequences.
--
--   **Formalization Note** (9) is stated multiplicatively, $\hat\mu(x)\le R\,\mu^\star(x)$ and $\mu^\star(x)\le R\,\hat\mu(x)$, which is exactly (9) with $0/0=1$ for $R>0$. The oracle is a function on all lists; only lists of length at most $n$ are constrained. The convention $\hat\mu(\emptyset)=1$ is not part of this definition; the statements that use it assume it separately.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Assumption 3.1 and footnote 12, pp.17–18 (PDF pp.19–20)

import Mathlib
import Definitions.Def_TTTSampling_prefixMass

namespace TTTSampling

/-- **Assumption 3.1 (ℓ∞-closeness)** of the oracle `µ̂` to the target `µ⋆`, with parameter `R`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Assumption 3.1,
printed pp.17–18 (PDF pp.19–20), with footnote 12: "µ̂ : Σ^{≤n} → ℝ≥0 is a mapping so that, for
some R > 0, for all x ∈ Σ^{≤n}, 1/R ≤ µ⋆(x)/µ̂(x) ≤ R. (9) Moreover, we assume that µ⋆(x) = µ̂(x)
for all x ∈ Σⁿ." Footnote 12: "0/0 in the context of (9) is to be interpreted as 1."

**Formalization Note**
* (9) is stated multiplicatively: `µ̂(x) ≤ R·µ⋆(x)` and `µ⋆(x) ≤ R·µ̂(x)` for every list of length
  `≤ n`, including the empty list. For `R > 0` this is exactly (9) with `0/0 = 1`: if one side is
  `0` the other is forced to be `0`.
* `µ̂` is a function on all lists; only its values on lists of length `≤ n` (the paper's
  `Σ^{≤n}`) are constrained.
* The convention `µ(∅) = 1` is **not** imposed on `µ̂` here; the statements that use it take
  `µ̂ [] = 1` as a separate hypothesis. -/
def Assumption31 {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}
    (μs : PMF (Fin n → α)) (μh : List α → NNReal) (R : ℝ) : Prop :=
  0 < R ∧
  (∀ x : List α, x.length ≤ n →
      ((μh x : ℝ) ≤ R * prefixMass μs x ∧ prefixMass μs x ≤ R * (μh x : ℝ))) ∧
  ∀ v : Fin n → α, (μh (List.ofFn v) : ℝ) = prefixMass μs (List.ofFn v)

end TTTSampling


