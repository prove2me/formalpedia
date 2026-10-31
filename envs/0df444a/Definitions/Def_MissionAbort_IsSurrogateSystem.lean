-- Prove2me | Definitions.Def_MissionAbort_IsSurrogateSystem
-- name    : MissionAbort_IsSurrogateSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:58.657994+00:00
-- url     : https://prove2.me/theorems/b2394092-3639-44a1-b0bf-fd5c225113dc
-- title:
--   The surrogate system
-- statement:
--   A probability space carrying a process $X^{(\lambda)}$ on $\{1,\dots,m_1+m_2+1\}$ and signals $Y_1^{(\lambda)},\dots,Y_N^{(\lambda)}$ is the surrogate system at $\lambda$ if $X^{(\lambda)}$ has, on the decision grid, the law of the chain with initial distribution (4) and rate matrix (5), (6), and if, for every path $x$ on the grid and signal vector $y$,
--   $$
--   P^{(\lambda)}\big(X^{(\lambda)}=x\text{ on the grid},\ Y_{1:N}^{(\lambda)}=y\big)=P^{(\lambda)}\big(X^{(\lambda)}=x\text{ on the grid}\big)\prod_{n=1}^N e\big(\text{cluster of }x(n\delta),y_n\big).
--   $$
--
--   **Formalization Note** The law of the chain is required at the times the problem reads, which a genuine chain satisfies. This covers the paper's object and admits a realization on a finite space. Conditional independence of the signals is what the proof uses on p.EC.2.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, pp.13–14; Appendix A.2, p.EC.2

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_emit
import Definitions.Def_MissionAbort_decisionGrid
import Definitions.Def_MissionAbort_pathWeight
import Definitions.Def_MissionAbort_HasRateChainLaw
import Definitions.Def_MissionAbort_clusterOf
import Definitions.Def_MissionAbort_initialProb
import Definitions.Def_MissionAbort_hazard
import Definitions.Def_MissionAbort_offRate
import Definitions.Def_MissionAbort_rateMatrix

namespace MissionAbort

open MeasureTheory

/-- The surrogate system at parameter `lam` (the page's `λ`) (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1,
pp.13–14): on a probability space `(Ω⁽λ⁾, ℱ⁽λ⁾, P⁽λ⁾)`, the chain `X⁽λ⁾` on `{1, …, m₁ + m₂ + 1}`
with initial law (4) and rate matrix (5), (6), and signals drawn independently given the chain, with
`Yₙ⁽λ⁾` from the cluster of `X⁽λ⁾(nδ)`.

**Formalization Note.** The chain's law is required on `decisionGrid M` only, the times the problem reads
(`HasRateChainLaw`); a genuine CTMC satisfies this. In `signals`, `x : ℝ → Fin _` is a value of the
chain on the grid, and its values off the grid play no role. Conditional independence of the signals
is what the proof uses (p.EC.2). -/
structure IsSurrogateSystem {K : ℕ} (M : Model K) (F G : Measure ℝ) (lam : ℝ) (m₁ m₂ : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℝ → Ω → Fin (m₁ + m₂ + 1))
    (Y : ℕ → Ω → Fin (K + 1)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  measurable_X : ∀ t ∈ decisionGrid M, Measurable (X t)
  measurable_Y : ∀ n, 1 ≤ n → n ≤ M.N → Measurable (Y n)
  chain : HasRateChainLaw (initialProb G M.ζ lam m₁ m₂) (rateMatrix F M.ζ lam m₁ m₂)
    (decisionGrid M) X μ
  signals : ∀ (x : ℝ → Fin (m₁ + m₂ + 1)) (y : Fin M.N → Fin (K + 1)),
    μ.real ({ω | ∀ t ∈ decisionGrid M, X t ω = x t} ∩
        {ω | ∀ i : Fin M.N, Y (i.val + 1) ω = y i}) =
      μ.real {ω | ∀ t ∈ decisionGrid M, X t ω = x t} *
        ∏ i : Fin M.N, emit M (clusterOf m₁ m₂ (x (((i.val + 1 : ℕ) : ℝ) * M.δ))) (y i)

end MissionAbort


