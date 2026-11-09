-- Prove2me | Definitions.Def_GevreyGibbsSep_queryCount
-- name    : GevreyGibbsSep_queryCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:40:28.065684+00:00
-- url     : https://prove2.me/theorems/61763260-3866-49ce-84a4-affa1bffccf7
-- title:
--   Definition 3 — query count $N_A(\mathcal P,\varepsilon)$
-- statement:
--   The **query count** of a classical randomized algorithm $A$ on an instance class $\mathcal P$ at accuracy $\varepsilon$ is
--   $$N_A(\mathcal P,\varepsilon)=\inf\Big\{N\in\mathbb N\ :\ \sup_{p\in\mathcal P}\mathrm{TV}(\widehat p_N,p)<\varepsilon\Big\},$$
--   a worst-case guarantee of $\varepsilon$-accurate output on every instance of the class, with $\inf\emptyset=+\infty$.
--
--   **Formalization Note** "$\sup<\varepsilon$" is written: some $\eta<\varepsilon$ bounds $\mathrm{TV}(\widehat p_N,p)$ for every $p\in\mathcal P$. The class is a set of scaled potentials and the value lies in $\mathbb N\cup\{\infty\}$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition 3, Eq. (10), p.7

import Mathlib
import Definitions.Def_GevreyGibbsSep_gibbs
import Definitions.Def_GevreyGibbsSep_tv
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_SamplingAlg
import Definitions.Def_GevreyGibbsSep_outputLaw

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition 3, Eq. (10), arXiv:2608.24527 (sha256 d4fd40eb…), p.7: the query count
`N_A(P, ε) = inf{N ∈ ℕ : sup_{p ∈ P} TV(p̂_N, p) < ε}` of an algorithm with the order-`k` oracle.

**Formalization Note** `sup_{p∈P} TV < ε` is written `∃ η < ε, ∀ p ∈ P, TV ≤ η` (the strict
inequality is on the supremum, not on each instance). Instances are given by their scaled
potentials. The value is in `ℕ∞`, with `inf ∅ = ⊤`. -/
noncomputable def queryCount {d : ℕ} (A : SamplingAlg d) (k : ℕ∞)
    (P : Set ((Fin d → ℝ) → ℝ)) (ε : ℝ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : ∃ η < ε, ∀ V ∈ P, tv (outputLaw A k V N) (gibbs V) ≤ η), (N : ℕ∞)

end GevreyGibbsSep


