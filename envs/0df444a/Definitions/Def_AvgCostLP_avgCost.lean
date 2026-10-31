-- Prove2me | Definitions.Def_AvgCostLP_avgCost
-- name    : AvgCostLP_avgCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:17.32126+00:00
-- url     : https://prove2.me/theorems/af776549-41cf-4231-861c-ced9b6d9dda2
-- title:
--   §2.1.1 — the average cost $J(\pi,\zeta)$ and the minimum average cost $\rho^*$
-- statement:
--   A policy $\pi\in\Pi$ and an initial distribution $\zeta\in\mathcal P(\mathbb X)$ induce, by the Ionescu-Tulcea theorem, a probability measure $\mathbf P^\pi_\zeta$ of the process $\{(x_n,a_n)\}_{n\ge0}$ on $(\mathbb X\times\mathbb A)^\infty$: $x_0\sim\zeta$, $a_n\sim\mu_n(\cdot\mid x_0,a_0,\dots,x_n)$, $x_{n+1}\sim q(\cdot\mid x_n,a_n)$. The **long-run expected average cost** is
--   $$J(\pi,\zeta):=\limsup_{n\to\infty}n^{-1}\,\mathbb E^\pi_\zeta\Big[\sum_{k=0}^{n-1}c(x_k,a_k)\Big]\in[0,+\infty],$$
--   and the **minimum average cost** is the infimum over all policies and all initial distributions,
--   $$\rho^*:=\inf_{\zeta\in\mathcal P(\mathbb X)}\ \inf_{\pi\in\Pi}J(\pi,\zeta).$$
--
--   These are the quantities that the primal and dual linear programs of §3 compute.
--
--   **Formalization Note** Expectations are lower Lebesgue integrals and $J$ takes values in $[0,+\infty]$; the term $n=0$ of the $\limsup$ is $0$ and does not affect it.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §2.1.1, pp.5-6

import Mathlib
import Definitions.Def_AvgCostLP_Policy

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace AvgCostLP

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- The history `(x₀, a₀, …, x_n, a_n)`, indexed by `Finset.Iic n`, as a `Fin (n+1)`-tuple. -/
def histFin (n : ℕ) (h : Π _ : Finset.Iic n, X × A) : Fin (n + 1) → X × A :=
  fun j => h ⟨j.val, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt)⟩

lemma measurable_histFin (n : ℕ) : Measurable (histFin (X := X) (A := A) n) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- The last state–action pair `(x_n, a_n)` of a history indexed by `Finset.Iic n`. -/
def lastPair (n : ℕ) (h : Π _ : Finset.Iic n, X × A) : X × A :=
  h ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- One step of the controlled process: given `(x₀, a₀, …, x_n, a_n)`, the next state `x_{n+1}`
is drawn from `q(· | x_n, a_n)` and then the next action `a_{n+1}` from
`μ_{n+1}(· | x₀, a₀, …, x_n, a_n, x_{n+1})`. -/
noncomputable def stepKernel (M : Model X A) (π : Policy M) (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, X × A) (X × A) :=
  (M.q.comap (lastPair n) (measurable_pi_apply _)) ⊗ₖ
    ((π.rule (n + 1)).comap (fun p => (histFin n p.1, p.2))
      (((measurable_histFin n).comp measurable_fst).prodMk measurable_snd))

instance (M : Model X A) (π : Policy M) (n : ℕ) : IsMarkovKernel (stepKernel M π n) := by
  have h1 : IsMarkovKernel (M.q.comap (lastPair (X := X) (A := A) n) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  have h2 : IsMarkovKernel ((π.rule (n + 1)).comap (fun p : (Π _ : Finset.Iic n, X × A) × X =>
      (histFin n p.1, p.2)) (((measurable_histFin n).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  exact Kernel.IsMarkovKernel.compProd _ _

/-- The law of `(x₀, a₀)`: `x₀ ∼ ζ` and `a₀ ∼ μ₀(· | x₀)`. -/
noncomputable def initMeasure (M : Model X A) (π : Policy M) (ζ : ProbabilityMeasure X) :
    Measure (X × A) :=
  (ζ : Measure X) ⊗ₘ ((π.rule 0).comap (fun x => (fun k => k.elim0, x))
    (measurable_const.prodMk measurable_id))

/-- Yu, arXiv:1905.12095v3, §2.1.1, p.5: the probability measure `P^π_ζ` of the process
`{(x_n, a_n)}_{n ≥ 0}` on `(X × A)^∞` induced by the policy `π` and the initial distribution
`ζ ∈ P(X)` (Ionescu-Tulcea, [3, Prop. 7.28]). -/
noncomputable def pathMeasure (M : Model X A) (π : Policy M) (ζ : ProbabilityMeasure X) :
    Measure (ℕ → X × A) :=
  Kernel.trajMeasure (X := fun _ => X × A) (initMeasure M π ζ) (stepKernel M π)

/-- Yu, arXiv:1905.12095v3, §2.1.1, p.5: the long-run expected average cost
`J(π, ζ) := limsup_{n→∞} n⁻¹ E^π_ζ[∑_{k=0}^{n−1} c(x_k, a_k)]`.

**Formalization Note** `J` takes values in `[0, +∞]` (`ℝ≥0∞`), and the expectation is a
`lintegral`, so it is defined for every policy and initial distribution. At `n = 0` the term is
`⊤ * 0 = 0`, which the `limsup` ignores. -/
noncomputable def avgCost (M : Model X A) (π : Policy M) (ζ : ProbabilityMeasure X) : ℝ≥0∞ :=
  limsup (fun n : ℕ => (n : ℝ≥0∞)⁻¹ *
    ∫⁻ ω, ∑ k ∈ Finset.range n, M.c (ω k) ∂(pathMeasure M π ζ)) atTop

/-- Yu, arXiv:1905.12095v3, §2.1.1, p.6: the minimum average cost over all policies and initial
distributions, `ρ* := inf_{ζ ∈ P(X)} inf_{π ∈ Π} J(π, ζ)`, an infimum in `[0, +∞]` over all
(randomized, history-dependent) policies `π ∈ Π` and all initial distributions `ζ`. -/
noncomputable def minAvgCost (M : Model X A) : ℝ≥0∞ :=
  ⨅ ζ : ProbabilityMeasure X, ⨅ π : Policy M, avgCost M π ζ

end AvgCostLP


