-- Prove2me | Definitions.Def_CryptoMiningMFG_Admissible
-- name    : CryptoMiningMFG_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:22.572822+00:00
-- url     : https://prove2.me/theorems/d007dafc-73a2-4bfa-8f86-6a711ef0097e
-- title:
--   Admissible mean hash rate $\bar\alpha$
-- statement:
--   A **mean hash rate** is a deterministic function of time $\bar\alpha:\mathbb R\to\mathbb R$, the average hash rate of the population. It is **admissible** when it is measurable and strictly positive on the mining period:
--
--   $$
--   \bar\alpha_t>0\qquad\text{for all } t\in[t_0,T].
--   $$
--
--   Positivity is the paper's standing assumption "$\bar\alpha^*_t\neq0$ for all $t$" together with $\bar\alpha_t\ge0$. An individual miner's reward intensity depends on $\bar\alpha$ through the competing hash rate $M\bar\alpha_t$.
--
--   **Formalization Note** Values outside $[t_0,T]$ play no role in any statement.
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, §2.3 p.9 ("ᾱ_t ≥ 0 denote the mean hash rate"); §2.5 p.11 ("We assume that ᾱ*_t ≠ 0 for all t")

import Mathlib
import Definitions.Def_CryptoMiningMFG_Model

namespace CryptoMiningMFG

/-- **Admissible mean hash rate.** Li, Reppen, Sircar, arXiv:1912.01952v2, §2.3, p.9
("ᾱ_t ≥ 0 denote the mean hash rate across all miners") and §2.5, p.11 ("We assume that
ᾱ*_t ≠ 0 for all t"): a deterministic function of time `ᾱ : ℝ → ℝ`, measurable, and strictly
positive on the mining period `[t0, T]`.

**Formalization Note.** Values of `ᾱ` outside `[t0, T]` are irrelevant: every statement only
uses `ᾱ` on `[t0, T]`. -/
def Admissible (P : Model) (abar : ℝ → ℝ) : Prop :=
  Measurable abar ∧ ∀ t ∈ Set.Icc P.t0 P.T, 0 < abar t

end CryptoMiningMFG


