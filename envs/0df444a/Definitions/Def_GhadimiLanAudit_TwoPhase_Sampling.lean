-- Prove2me | Definitions.Def_GhadimiLanAudit_TwoPhase_Sampling
-- name    : GhadimiLanAudit_TwoPhase_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:49:48.898404+00:00
-- url     : https://prove2.me/theorems/bbd11be8-6263-4b89-b3a3-723de00526fd
-- title:
--   Finite-query A1, independent RSG candidates and validation sampling laws
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\Omega$. Along a sequence of $K$ actual queries $q_k$ with samples $\xi_k$, finite A1 requires a filtration $\mathcal F_k$ such that $q_k$ is known at time $k-1$, $\xi_k$ is measurable at time $k$, and the oracle return and squared error are integrable. Its substantive requirements are
--
--   $$\mathbb E[G(q_k,\xi_k)\mid\mathcal F_{k-1}]=g(q_k),\qquad \mathbb E\|G(q_k,\xi_k)-g(q_k)\|^2\le\sigma^2,\quad 1\le k\le K.$$
--
--   This is the restriction of the published RSG A1 interface to the calls actually executed. In each RSG run, the query points are computed by the recursion. The output index has the published mass function (2.3), uniform on $1,\ldots,N$ for the constant step, and is independent of its run's noise. The $S$ candidate outputs are independent random vectors.
--
--   For positive noise, each validation stream has its own filtration containing its candidate at time zero, and obeys the same conditional-mean and unconditional-error conditions through time $T$. Streams may share samples; successive samples need not be independent. No validation law is requested at zero noise, and no active-run law is requested at $N=0$.
--
--   This interface describes sampling, not performance. In particular it contains no expected-gradient bound, success event, selected-minimum assertion or cost inequality.
--
--   **Formalization Note** Conditioning uses the paper's proof-level reading (2.10). General measurable probability spaces include the paper's Borel setting. No assertion about unused oracle calls beyond the finite horizon is needed.
-- source:
--   Ghadimi and Lan, Stochastic First- and Zeroth-Order Methods for Nonconvex Stochastic Programming, arXiv:1309.5549v1, https://arxiv.org/abs/1309.5549v1, p. 2, A1 (1.2)–(1.3); p. 7, (2.10); pp. 10–11, independent runs, known-candidate validation and recycled samples

import Definitions.Def_GhadimiLanAudit_TwoPhase_Execution

open MeasureTheory ProbabilityTheory

namespace GhadimiLanAudit.TwoPhase

/-- Finite-horizon restriction of the published RSG AssumptionA1 to the calls
actually made. The input is known before its query, the noise is adapted, the
conditional mean is the gradient, and the error bound is UNCONDITIONAL.
This makes no claim about unused samples after K. -/
def FiniteA1 {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [m : MeasurableSpace Ω]
    (P : Problem n Ξ) (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (q : ℕ → Ω → GhadimiLan.RSG.E n) (ξ : ℕ → Ω → Ξ) (K : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 K,
    Measurable[ℱ (k - 1)] (q k) ∧
    Measurable[ℱ k] (ξ k) ∧
    Integrable (fun ω => P.G (q k ω) (ξ k ω)) μ ∧
    (μ[fun ω => P.G (q k ω) (ξ k ω) | ℱ (k - 1)] =ᵐ[μ] fun ω => P.g (q k ω)) ∧
    Integrable (fun ω => ‖P.G (q k ω) (ξ k ω) - P.g (q k ω)‖ ^ 2) μ ∧
    (∫ ω, ‖P.G (q k ω) (ξ k ω) - P.g (q k ω)‖ ^ 2 ∂μ) ≤ P.σ ^ 2

/-- One run's permitted law: finite A1, the published (2.3) random index,
and independence of R from its noise. For the constant positive step, (2.3)
is uniform on {1,...,N}; no iid assumption is imposed within the run. -/
def RunLaw {n : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [m : MeasurableSpace Ω]
    (P : Problem n Ξ) (μ : Measure Ω) (N : ℕ)
    (ξ : ℕ → Ω → Ξ) (R : Ω → ℕ) : Prop :=
  (∃ ℱ : Filtration ℕ m, FiniteA1 P μ ℱ (trajectory P N ξ) ξ N) ∧
  GhadimiLan.RSG.IsRandomOutputIndex μ R P.L (fun _ => completedStep P N) N ∧
  IndepFun R (fun ω k => ξ k ω) μ

/-- Independent candidate outputs and finite conditional A1 for validation at
known candidates. Different candidates may reuse validation randomness.
Nothing here assumes a success probability, expected gradient bound, selected
minimizer or call bound. -/
def ActiveLaw {n S N T : ℕ} {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [m : MeasurableSpace Ω]
    (P : Problem n Ξ) (μ : Measure Ω) (A : ActiveInput P S Ω) : Prop :=
  (∀ s, RunLaw P μ N (A.ξ s) (A.R s)) ∧
  iIndepFun (fun s ω => candidate (N := N) P A s ω) μ ∧
  (∀ hσ : P.σ ≠ 0, ∀ s, ∃ 𝒢 : Filtration ℕ m,
    Measurable[𝒢 0] (candidate (N := N) P A s) ∧
    FiniteA1 P μ 𝒢 (fun _ => candidate (N := N) P A s) (A.η hσ s) T)

/-- The prescribed execution needs no sampling law in its zero-iteration branch. -/
def SamplingLaw {n S N T : ℕ} {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (P : Problem n Ξ) (μ : Measure Ω) (A : Input P S N Ω) : Prop :=
  ∀ hN : N ≠ 0, ActiveLaw (N := N) (T := T) P μ (A hN)

end GhadimiLanAudit.TwoPhase


