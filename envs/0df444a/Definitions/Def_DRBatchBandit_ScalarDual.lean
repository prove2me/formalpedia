-- Prove2me | Definitions.Def_DRBatchBandit_ScalarDual
-- name    : DRBatchBandit_ScalarDual
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:05.829502+00:00
-- url     : https://prove2.me/theorems/a7aa52c1-b927-45c4-9c69-c83861230551
-- title:
--   KL dual value $\sup_{\alpha\ge0}\{-\alpha\log\mathbf E_{\mathbf P}[e^{-Y/\alpha}]-\alpha\delta\}$ and quantile $q_{\mathbf P}(t)$ of a law on $\mathbb R$
-- statement:
--   For a probability measure $\mathbf P$ on $\mathbb R$ (the law of a reward $Y$) and $\delta>0$, Lemmas 5 and 6 (p.17) compare the **dual values**
--   $$\sup_{\alpha\ge0}\big\{-\alpha\log\mathbf E_{\mathbf P}[\exp(-Y/\alpha)]-\alpha\delta\big\}.$$
--   The **$t$-quantile** of $\mathbf P$ is
--   $$q_{\mathbf P}(t)=\inf\{x\in\mathbb R:\ t\le F_{\mathbf P}(x)\},$$
--   where $F_{\mathbf P}$ is the CDF of $\mathbf P$ (p.17).
--
--   **Formalization Note** The dual value is extended-real: when $e^{-Y/\alpha}$ is not $\mathbf P$-integrable the expectation is $+\infty$ and the objective is $-\infty$. The supremum is over $\alpha>0$ (Remark 2, p.11). The quantile is a real infimum; it is the paper's value for $t\in(0,1)$, where the set is nonempty and bounded below.
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Lemma 5 and Lemma 6 p.17 (dual value, q_P(t), F_P). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib

open MeasureTheory ProbabilityTheory

namespace DRBatchBandit

open Classical in
/-- The KL dual objective of a law `P` of a real reward `Y`,
`−α log E_P[exp(−Y/α)] − αδ` (arXiv:2006.05630v7, Lemmas 5 and 6, p.17).

**Formalization Note.** Valued in `EReal`: when `exp(−Y/α)` is not `P`-integrable the
expectation is `+∞` and the objective is `−∞` (`⊥`). -/
noncomputable def dualObj (P : Measure ℝ) (δ α : ℝ) : EReal :=
  if Integrable (fun y => Real.exp (-y / α)) P then
    ((-α * Real.log (∫ y, Real.exp (-y / α) ∂P) - α * δ : ℝ) : EReal)
  else ⊥

/-- The KL dual value `sup_{α ≥ 0} {−α log E_P[exp(−Y/α)] − αδ}` of a law `P` on `ℝ`
(arXiv:2006.05630v7, Lemmas 5 and 6, p.17).

**Formalization Note.** The supremum is over `α > 0` (Remark 2, p.11, defines the `α = 0` value
as the right limit), in `EReal`. -/
noncomputable def dualValue (P : Measure ℝ) (δ : ℝ) : EReal :=
  ⨆ α : Set.Ioi (0 : ℝ), dualObj P δ α

/-- The `t`-quantile `q_P(t) = inf {x ∈ ℝ : t ≤ F_P(x)}` of a probability measure `P` on `ℝ`,
`F_P` its CDF (arXiv:2006.05630v7, p.17, below Lemma 5).

**Formalization Note.** For `t ∈ (0, 1)` the set is nonempty and bounded below, so the real
infimum is the paper's; at `t = 0` the paper's value is `−∞` and Lean's is `0`. -/
noncomputable def quantile (P : Measure ℝ) (t : ℝ) : ℝ :=
  sInf {x : ℝ | t ≤ cdf P x}

end DRBatchBandit


