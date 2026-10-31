-- Prove2me | Definitions.Def_AdaDiscRL_IsRun
-- name    : AdaDiscRL_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:51.591863+00:00
-- url     : https://prove2.me/theorems/52bb3398-4561-4139-9f44-61b0603ed64e
-- title:
--   An online run of AdaMB or AdaQL on an episodic MDP
-- statement:
--   On a probability space $(\Omega,\mathbb P)$, a **run** of an adaptive-partition algorithm for $K$ episodes is a sequence of random episode data $(X^k,A^k,R^k)$ such that, for every episode $k\in[K]$ and step $h$, with $B^k_h$ the ball the algorithm selects from its state after episode $k-1$:
--
--   1. given the history up to $X^k_h$, the action $A^k_h$ has law $\mathrm{play}(B^k_h)(X^k_h)$, a distribution over actions in $B^k_h$;
--   2. given the history and $A^k_h$, the reward $R^k_h$ has law $R_h(X^k_h,A^k_h)$;
--   3. given the history and $A^k_h$, the next state $X^k_{h+1}$ has law $T_h(\cdot\mid X^k_h,A^k_h)$.
--
--   The starting states $X^k_1$ are arbitrary.
--
--   **Formalization Note** Conditional laws are stated in their defining form $\mathbb P(F\cap\{Y\in E\})=\int_F\kappa(E)\,d\mathbb P$ for events $F$ of the conditioning σ-algebra. Starting states may depend on the past (a fixed sequence is a special case); the joint law of $(R^k_h,X^k_{h+1})$ is constrained only through these two marginals.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, §2.1 Online Interaction Structure, p.9; §3.2, p.16

import Mathlib
import Definitions.Def_AdaDiscRL_EpisodicMDP
import Definitions.Def_AdaDiscRL_AlgState

open MeasureTheory ProbabilityTheory

namespace AdaDiscRL

variable {S A ι Ω : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace Ω]
  {D : S × A → S × A → ℝ} {dS Lmax H : ℕ}

/-- The history before the action of step `h` (paper step `h + 1`) of episode `k`: all data of
episodes `1, …, k − 1`, and the states `X_1, …, X_{h+1}`, actions and rewards of the earlier steps
of episode `k` (arXiv:2110.15843v3, p.9 and p.39, `F_k`). -/
def histSigma (traj : Ω → ℕ → EpData S A H) (k : ℕ) (h : Fin H) : MeasurableSpace Ω :=
  (⨆ j ∈ Finset.Ico 1 k, MeasurableSpace.comap (fun ω => traj ω j) inferInstance) ⊔
  (⨆ (i : Fin (H + 1)) (_ : i.val ≤ h.val),
    MeasurableSpace.comap (fun ω => (traj ω k).1 i) inferInstance) ⊔
  (⨆ (i : Fin H) (_ : i < h),
    MeasurableSpace.comap (fun ω => (traj ω k).2.1 i) inferInstance ⊔
    MeasurableSpace.comap (fun ω => (traj ω k).2.2 i) inferInstance)

/-- **An online run of an adaptive-partition algorithm** (arXiv:2110.15843v3, "Online Interaction
Structure", p.9; §3.2, p.16), on a probability space `(Ω, μ)` with episode data
`traj ω k = (X^k, A^k, R^k)` for episodes `k = 1, …, K`.

`alg data k` is the algorithm state after episodes `1, …, k` of the data sequence `data`
(`statesQL` or `statesMB`); the selected ball at step `h` of episode `k` is
`B_h^k = selBall … (alg (traj ω) (k−1)) h X_h^k`. For `1 ≤ k ≤ K` and every step `h`:
1. given the history `histSigma k h` (which contains `X_h^k`), the action `A_h^k` has law
   `play B_h^k X_h^k`;
2. given the history and `A_h^k`, the reward `R_h^k` has law `R_h(X_h^k, A_h^k)`;
3. given the history and `A_h^k`, the next state `X_{h+1}^k` has law `T_h(· | X_h^k, A_h^k)`.
Each law is stated in its defining form: `μ(F ∩ {Y ∈ E}) = ∫⁻_F κ(E) dμ` for every event `F` of
the conditioning σ-algebra and measurable `E`.

**Formalization Note.** The starting states `X_1^k` are unrestricted random variables, so they
may depend on the past (a fixed sequence `{X_1^k}` is a special case). The joint law of
`(R_h^k, X_{h+1}^k)` given the history and action is not restricted beyond its two marginals. -/
def IsRun (M : EpisodicMDP S A H) (P : HierPartition S A ι D dS Lmax)
    (choose : Finset ι → (ι → ℝ) → ι) (play : ι → Kernel S A)
    (alg : (ℕ → EpData S A H) → ℕ → AlgState S ι H) (K : ℕ)
    (μ : Measure Ω) (traj : Ω → ℕ → EpData S A H) : Prop :=
  IsProbabilityMeasure μ ∧
  (∀ k, Measurable (fun ω => traj ω k)) ∧
  ∀ k ∈ Finset.Icc 1 K, ∀ h : Fin H,
    (∀ E : Set A, MeasurableSet E → ∀ F, MeasurableSet[histSigma traj k h] F →
      μ (F ∩ {ω | (traj ω k).2.1 h ∈ E}) =
        ∫⁻ ω in F, play (selBall P choose (alg (traj ω) (k - 1)) h ((traj ω k).1 h.castSucc))
          ((traj ω k).1 h.castSucc) E ∂μ) ∧
    (∀ E : Set ℝ, MeasurableSet E → ∀ F,
      MeasurableSet[histSigma traj k h ⊔
        MeasurableSpace.comap (fun ω => (traj ω k).2.1 h) inferInstance] F →
      μ (F ∩ {ω | (traj ω k).2.2 h ∈ E}) =
        ∫⁻ ω in F, M.R h ((traj ω k).1 h.castSucc, (traj ω k).2.1 h) E ∂μ) ∧
    (∀ E : Set S, MeasurableSet E → ∀ F,
      MeasurableSet[histSigma traj k h ⊔
        MeasurableSpace.comap (fun ω => (traj ω k).2.1 h) inferInstance] F →
      μ (F ∩ {ω | (traj ω k).1 h.succ ∈ E}) =
        ∫⁻ ω in F, M.T h ((traj ω k).1 h.castSucc, (traj ω k).2.1 h) E ∂μ)

end AdaDiscRL


