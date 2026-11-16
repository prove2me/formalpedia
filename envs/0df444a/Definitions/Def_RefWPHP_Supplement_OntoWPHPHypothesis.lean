-- Prove2me | Definitions.Def_RefWPHP_Supplement_OntoWPHPHypothesis
-- name    : RefWPHP_Supplement_OntoWPHPHypothesis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:23:22.978693+00:00
-- url     : https://prove2.me/theorems/aee472f7-4274-49d4-9f3f-280daed5ce62
-- title:
--   Hypothesis 1.9 — hardness of the onto weak pigeonhole principle in $\mathrm{Res}(k)$
-- statement:
--   **Hypothesis 1.9** states that for every $k \in \mathbb N$ there exist constants $\alpha = \alpha(k)$ and $\beta = \beta(k)$ with $0 < \alpha < \beta$, and $n_0 \in \mathbb N$, such that for every $n \ge n_0$, every $\mathrm{Res}(k)$-refutation of $\mathrm{ontoPHP}^{2^{\lfloor n^\alpha \rfloor}}_n$ has size at least
--
--   $$
--   2^{n^\beta}.
--   $$
--
--   The exponent $\alpha$ controls the number of pigeons and $\beta$ the strength of the bound; $\alpha < \beta$ makes the bound superpolynomial in the size of the formula. The paper uses it to derive Theorem 4.7.
--
--   **Formalization Note** This is a proposition used only as a hypothesis. $\mathrm{Res}(k)$ is $\mathrm{PK}^k_0$ (`IsPKkRefutation k 0`) and size is the base `derivSize`. The case $k = 0$ follows from $k = 1$, since a $\mathrm{PK}^0_0$-refutation is a $\mathrm{PK}^1_0$-refutation.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Hypothesis 1.9, p.7 (PDF p.9), restated p.34 (PDF p.36)

import Mathlib
import Definitions.Def_RefWPHP_Supplement_ontoPhpCNF
import Definitions.Def_RefWPHP_Supplement_IsPKkDerivation

namespace RefWPHP

namespace Supplement

/-- Hypothesis 1.9 (Hardness of ontoWPHP in `Res(k)`) of N. Arteche, *Resolution Lower Bounds
versus the Weak Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…),
p.7 (PDF 9), restated p.34 (PDF 36): "for every `k ∈ ℕ` there exist constants `α = α(k)` and
`β = β(k)`, such that `0 < α < β`, and `n₀ ∈ ℕ` such that for every `n ≥ n₀` the unsatisfiable
CNF formula `ontoPHP^{2^⌊n^α⌋}_n` requires size at least `2^{n^β}` to be refuted in `Res(k)`".

**Formalization Note.** `Res(k)` is `PK^k_0` (`IsPKkRefutation k 0`), size is the base
`derivSize`. For `k = 0` the clause follows from `k = 1`, since a `PK^0_0`-refutation is a
`PK^1_0`-refutation. This is a `Prop`, used only as a hypothesis. -/
def OntoWPHPHypothesis : Prop :=
  ∀ k : ℕ, ∃ α β : ℝ, 0 < α ∧ α < β ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ ρ : List (Cedent (Fin (2 ^ ⌊(n : ℝ) ^ α⌋₊) × Fin n)),
      IsPKkRefutation k 0 (ontoPhpCNF (2 ^ ⌊(n : ℝ) ^ α⌋₊) n) ρ →
        (2 : ℝ) ^ ((n : ℝ) ^ β) ≤ (derivSize ρ : ℝ)

end Supplement

end RefWPHP


