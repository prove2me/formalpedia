-- Prove2me | Definitions.Def_PartPredAlloc_EventE
-- name    : PartPredAlloc_EventE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:21.541397+00:00
-- url     : https://prove2.me/theorems/392d3eb5-ddda-4b99-b1cc-3c2223966e88
-- title:
--   Event $\mathcal E$ (Definition 4)
-- statement:
--   With $\alpha=10+2\sqrt6$ and $k=16$, the event $\mathcal E$ occurs for the outcome $(\mathcal S,\sigma)$ if:
--
--   1. when $n_1\ge\frac{k}{p^2}\log n$, for all $\lambda\in\{0,1/n,\dots,1\}$,
--   $$
--   |O_1(\lambda)-\tilde o_1(\lambda)|<\alpha\sqrt{n_1\log n}\quad\text{and}\quad |O_1(\lambda)+O_2(\lambda)-(\tilde o_1(\lambda)+\tilde o_2(\lambda))|<\alpha\sqrt{(n_1+n_2)\log n};
--   $$
--   2. when $n_2\ge\frac{k}{p^2}\log n$, for all $\lambda\in\{0,1/n,\dots,1\}$,
--   $$
--   |O_2(\lambda)-\tilde o_2(\lambda)|<\alpha\sqrt{n_2\log n}\quad\text{and}\quad |O^{\mathcal S}_2(\lambda)-\tilde o^{\mathcal S}_2(\lambda)|<\alpha\sqrt{n_2\log n}.
--   $$
--
--   These are the conditions (2a)–(3b) of Lemma 1; the analysis of Algorithm 1 is carried out on realizations in $\mathcal E$.
--
--   **Formalization Note** One predicate on $(\mathcal S,\sigma)$ serves both Lemma 1 (random counts) and Definition 4 (realized counts). As in the paper, $\mathcal E$ imposes nothing when $n_1,n_2<\frac k{p^2}\log n$.
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Definition 4, pp.13–14

import Mathlib
import Definitions.Def_PartPredAlloc_obsCount
import Definitions.Def_PartPredAlloc_alphaL1

namespace PartPredAlloc

/-- Event `𝓔` (arXiv:1810.00447v1, Definition 4, pp.13–14), as a predicate on the outcome `(S, σ)`
of the partially predictable model, given `p` and the adversarial sequence `v_I` of length `n`.
With `α = 10 + 2√6`, `k = 16`, `n₁, n₂` the type counts of `v_I` and `λ = t/n`:

* if `n₁ ≥ (k/p²) log n`, then for all `t ∈ {0, …, n}`,
  `|O₁(λ) − õ₁(λ)| < α √(n₁ log n)` and
  `|O₁(λ) + O₂(λ) − (õ₁(λ) + õ₂(λ))| < α √((n₁ + n₂) log n)`;
* if `n₂ ≥ (k/p²) log n`, then for all `t ∈ {0, …, n}`,
  `|O₂(λ) − õ₂(λ)| < α √(n₂ log n)` and `|O^S₂(λ) − õ^S₂(λ)| < α √(n₂ log n)`.

**Formalization Note.** Time `λ ∈ {0, 1/n, …, 1}` is `t/n` with `t : ℕ`, `t ≤ n`; `log` is the
natural logarithm. The paper writes Lemma 1 with the random `O_j` and Definition 4 with their
realizations `o_j`; one predicate on `(S, σ)` serves both. As in the paper, the event constrains
nothing when both `n₁, n₂ < (k/p²) log n`. -/
def EventE {n : ℕ} (p : ℝ) (vI : Fin n → Cust) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    Prop :=
  ((nType1 vI : ℝ) ≥ kL1 / p ^ 2 * Real.log n →
    ∀ t : ℕ, t ≤ n →
      |(O1 vI σ t : ℝ) - otilde1 p vI t| < alphaL1 * Real.sqrt ((nType1 vI : ℝ) * Real.log n) ∧
      |(O1 vI σ t : ℝ) + (O2 vI σ t : ℝ) - (otilde1 p vI t + otilde2 p vI t)| <
        alphaL1 * Real.sqrt (((nType1 vI : ℝ) + nType2 vI) * Real.log n)) ∧
  ((nType2 vI : ℝ) ≥ kL1 / p ^ 2 * Real.log n →
    ∀ t : ℕ, t ≤ n →
      |(O2 vI σ t : ℝ) - otilde2 p vI t| < alphaL1 * Real.sqrt ((nType2 vI : ℝ) * Real.log n) ∧
      |(OS2 vI S σ t : ℝ) - otildeS2 p vI t| <
        alphaL1 * Real.sqrt ((nType2 vI : ℝ) * Real.log n))

end PartPredAlloc


