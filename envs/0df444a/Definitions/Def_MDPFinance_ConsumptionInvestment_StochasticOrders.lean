-- Prove2me | Definitions.Def_MDPFinance_ConsumptionInvestment_StochasticOrders
-- name    : MDPFinance_ConsumptionInvestment_StochasticOrders
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:58:47.80677+00:00
-- url     : https://prove2.me/theorems/203e32fd-0254-4948-b2b9-7c19caff4e27
-- title:
--   The increasing concave order and stochastic monotonicity of a chain
-- statement:
--   $\mu \le_{\mathrm{icv}} \nu$ iff $\int f\,d\mu \le \int f\,d\nu$ for every increasing
--   concave $f$. A finite Markov chain with transition matrix $p$ on a linearly ordered state space
--   is **stochastically monotone** if $j \mapsto \sum_k p_{jk}v(k)$ is increasing for every
--   increasing $v$.
--
--   **Formalization Note.** $\le_{\mathrm{icv}}$ is restated fresh (Definition B.3.9c), distinct from
--   chunk `02c`'s `LEConcaveOrder`/`LEStochasticOrder`/`LEConvexOrder` triple (`≤_st`/`≤_cv`/`≤_cx`),
--   which does not include the increasing-concave order this chunk needs — reusing one of those three
--   in its place would be a strictly different, and here wrong, hypothesis (per the chunk brief's own
--   warning not to conflate `≤_icv` with plain `≤_cv`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 361-363, PDF 368-369, Definition B.3.9c / Definition B.3.13

import Mathlib

open MeasureTheory

namespace MDPFinance.ConsumptionInvestment

/-- The increasing concave order on measures on `ℝ` (Bäuerle–Rieder, Definition B.3.9c, p. 361,
PDF 368): `μ ≤_icv ν` iff `∫ f dμ ≤ ∫ f dν` for every increasing, concave `f` for which both
integrals exist. Restated from `MDPFinance.StructuredModels`'s `≤_st`/`≤_cx`/`≤_cv` triple
(chunk `02c`), which does not itself include this order. -/
def LEIncreasingConcaveOrder (μ ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Monotone f → ConcaveOn ℝ Set.univ f → Integrable f μ → Integrable f ν →
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν

/-- A finite Markov chain with transition matrix `p` on a linearly ordered state space `EY` is
stochastically monotone (Bäuerle–Rieder, Definition B.3.13, p. 362-363, PDF 369, specialized to
a finite chain via transition probabilities) if `j ↦ Σ_k p_{jk} v(k)` is increasing for every
increasing `v : EY → ℝ`. -/
def IsStochasticallyMonotoneChain {EY : Type*} [Fintype EY] [Preorder EY] (p : EY → EY → ℝ) :
    Prop :=
  ∀ v : EY → ℝ, Monotone v → Monotone (fun j => ∑ k, p j k * v k)

end MDPFinance.ConsumptionInvestment


