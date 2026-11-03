-- Prove2me | Definitions.Def_FreeOrderEPTAS_V
-- name    : FreeOrderEPTAS_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:11.157189+00:00
-- url     : https://prove2.me/theorems/6c2019b5-d107-40a1-b5d1-5b1bd8069680
-- title:
--   The value $V(\sigma)$ of a permutation
-- statement:
--   For a permutation $\sigma$, $V(\sigma)$ is the expected value obtained by an algorithm that utilizes the optimal stopping rule on $\sigma$:
--   $$V(\sigma)=\sup_{\tau}\ \mathbb E\big[\text{reward of }\tau\text{ on }\sigma\big],$$
--   the supremum being over all stopping rules.
--
--   This is the quantity the main theorem bounds from below. The milestone `value_eq_recursion` identifies it with the backward recursion.
--
--   **Formalization Note** The index type is nonempty, each reward is integrable, and all expected rewards are bounded by $\sum_i\mathbb E[X_i]$, so the real supremum is meaningful.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.1, p.17

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Instance
import Definitions.Def_FreeOrderEPTAS_StoppingRule

open MeasureTheory

namespace FreeOrderEPTAS

/-- `V(σ)`, "the expected value obtained by an algorithm that utilizes the optimal stopping rule
on σ" (arXiv:2007.13121v3, p.17): the supremum over stopping rules of the expected reward.

**Formalization Note.** `StoppingRule n` is nonempty, every reward is integrable and bounded in
absolute value by `∑ i, |x i|`, so the real supremum is over a nonempty bounded set. -/
noncomputable def V {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ⨆ τ : StoppingRule n, ∫ x, reward τ σ x ∂(Measure.pi I.μ)

end FreeOrderEPTAS


