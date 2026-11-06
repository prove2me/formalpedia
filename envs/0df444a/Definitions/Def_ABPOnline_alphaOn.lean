-- Prove2me | Definitions.Def_ABPOnline_alphaOn
-- name    : ABPOnline_alphaOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:59.81436+00:00
-- url     : https://prove2.me/theorems/de79509f-4adb-49d2-80d0-0b8999496a3b
-- title:
--   Online achievability and the online threshold $\alpha_{\mathrm{on}}(\kappa)$
-- statement:
--   A constraint density $\alpha>0$ is **online-achievable at margin** $\kappa$ if, for every integer sequence $M_N$ with $M_N/N\to\alpha$, there is a sequence of online algorithms (one for each $N$, on $M_N\times N$ instances) such that
--   $$
--   \mathbb P\Big(\min_{1\le i\le M_N}X_{N,i}\ge\kappa\Big)\longrightarrow1 .
--   $$
--   The **online threshold** is
--   $$
--   \alpha_{\mathrm{on}}(\kappa):=\sup\{\alpha>0:\ \alpha\text{ is online-achievable at margin }\kappa\}.
--   $$
--
--   This is the quantity determined exactly by Theorem 1.1.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$, so an empty set gives $0$ and an unbounded one gives $+\infty$; no real-valued junk supremum is involved. The paper's remark that random seeds do not change the definition is not part of it and is not formalized.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Definition 2.2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_ABPOnline_IsOnlineAlg

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace ABPOnline

/-- A constraint density `α` is **online-achievable at margin `κ`** (arXiv:2609.02124,
Definition 2.2, printed p.5, PDF p.6): for every integer sequence `M_N` with `M_N/N → α` there is a
sequence of online algorithms whose success probability at margin `κ` tends to one.

**Formalization Note** The sequence is `Mseq : ℕ → ℕ`; `(Mseq N : ℝ)/N` is `0` at `N = 0`, which
does not affect the limit. Probabilities are in `ℝ≥0∞`. The positivity `α > 0` is imposed in
`alphaOn`, as in the paper. -/
def OnlineAchievable (κ α : ℝ) : Prop :=
  ∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
    ∃ σ : ∀ N : ℕ, Fin N → (Fin (Mseq N) × Fin N → ℝ) → ℝ,
      (∀ N, IsOnlineAlg (Mseq N) N (σ N)) ∧
      Tendsto (fun N : ℕ => gaussMat (Mseq N) N (successSet (σ N) κ)) atTop (𝓝 1)

/-- The **online threshold** `α_on(κ) := sup{α > 0 : α is online-achievable at margin κ}`
(arXiv:2609.02124, Definition 2.2, p.5).

**Formalization Note** The supremum is taken in `ℝ≥0∞`, so an unbounded set gives `⊤` and the
empty set gives `0`; no real-valued `sSup` junk value is involved. -/
noncomputable def alphaOn (κ : ℝ) : ℝ≥0∞ :=
  ⨆ (α : ℝ) (_ : 0 < α ∧ OnlineAchievable κ α), ENNReal.ofReal α

end ABPOnline


