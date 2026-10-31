-- Prove2me | Definitions.Def_FoundationsRL_LSVI_IsLSVITrace
-- name    : FoundationsRL_LSVI_IsLSVITrace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:23:22.97299+00:00
-- url     : https://prove2.me/theorems/1ef7a6b8-2534-4ff2-8fc1-d2862ff1a187
-- title:
--   LSVI-UCB: Gram matrices, optimistic $\bar Q^t_h$, least-squares step, greedy policy, and the regret
-- statement:
--   Fix features $\phi$, inputs $R,\rho>0$, a horizon $H$ and $T$ episodes. Given the states $s^i_h$, actions $a^i_h=\hat\pi^i_h(s^i_h)$ and rewards $r^i_h$ of the episodes $i<t$, **LSVI-UCB** computes in episode $t$, for $h=H,\dots,1$ and with $\bar Q^t_{H+1}\equiv0$,
--   $$
--   \hat\theta^t_h\in\operatorname*{arg\,min}_{\theta\in\mathsf B^d_2(\rho)}\sum_{i<t}\Big(\langle\phi(s^i_h,a^i_h),\theta\rangle-r^i_h-\max_a\bar Q^t_{h+1}(s^i_{h+1},a)\Big)^2,
--   $$
--   $$
--   \Sigma^t_h=\sum_{i<t}\phi(s^i_h,a^i_h)\phi(s^i_h,a^i_h)^\top+I,\qquad
--   \bar Q^t_h(s,a)=\Big\{\langle\phi(s,a),\hat\theta^t_h\rangle+\sqrt R\,\|\phi(s,a)\|_{(\Sigma^t_h)^{-1}}\Big\}\wedge1,
--   $$
--   and plays the greedy policy $\hat\pi^t_h(s)\in\operatorname*{arg\,max}_{a\in\mathcal A}\bar Q^t_h(s,a)$, where $\|x\|_{A}=\sqrt{x^\top Ax}$. The predicate `IsLSVITrace` states that these computations hold along one realization of the data, for every $t\in[T]$ and $h\in[H]$. The module also defines the **regret** of the played policies,
--   $$
--   \mathrm{Reg}=\sum_{t=1}^T f^M(\pi_M)-f^M(\hat\pi^t).
--   $$
--
--   The constrained least-squares step has no ridge term; the identity in $\Sigma^t_h$ only enters the elliptic bonus.
--
--   **Formalization Note** Ties in the $\arg\min$ and $\arg\max$ are left open, so every selection rule satisfies the predicate; if $\bar Q^t_h(s,\cdot)$ has no maximizer, no policy satisfies it, as the algorithm is then undefined. $\max_a\bar Q^t_{h+1}$ in the target is the supremum, which equals the maximum when it is attained.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, algorithm box LSVI-UCB, p. 133; p. 134; regret (5.3), p. 82, as used on p. 137

import Mathlib
import Definitions.Def_FoundationsRL_LSVI_EpisodicMDP

open MeasureTheory Matrix

namespace FoundationsRL.LSVI

variable {S A : Type*} {d : ℕ}

/-- The Gram matrix of LSVI-UCB (Foster & Rakhlin, *Foundations of Reinforcement Learning and
Interactive Decision Making*, arXiv:2312.16730v1, algorithm box, p. 133):
`Σ^t_h = Σ_{i<t} ϕ(s^i_h, a^i_h) ϕ(s^i_h, a^i_h)^⊤ + I`, built from the states `s i h = s^i_h`
and actions `a i h = a^i_h` of the episodes `i = 1, …, t − 1`. -/
noncomputable def gram (ϕ : S → A → EuclideanSpace ℝ (Fin d)) (s : ℕ → ℕ → S) (a : ℕ → ℕ → A)
    (t h : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i ∈ Finset.Ico 1 t,
      Matrix.vecMulVec (WithLp.ofLp (ϕ (s i h) (a i h))) (WithLp.ofLp (ϕ (s i h) (a i h)))
    + 1

/-- The elliptic norm `‖x‖_{Σ^{-1}} = √(x^⊤ Σ^{-1} x)`. -/
noncomputable def ellNorm (G : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.sqrt (WithLp.ofLp x ⬝ᵥ (G⁻¹ *ᵥ WithLp.ofLp x))

/-- The optimistic value function of layer `h` in episode `t` (algorithm box, p. 133):
`Q̄^t_h(s, a) = {⟨ϕ(s, a), θ̂^t_h⟩ + √R ‖ϕ(s, a)‖_{(Σ^t_h)^{-1}}} ∧ 1` for `h ∈ [H]`, and
`Q̄^t_{H+1} ≡ 0`, where `θ̂ t h = θ̂^t_h`. It is `0` outside `[H]`. -/
noncomputable def Qbar (ϕ : S → A → EuclideanSpace ℝ (Fin d)) (R : ℝ) (H : ℕ) (s : ℕ → ℕ → S)
    (a : ℕ → ℕ → A) (θhat : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (t h : ℕ) : S → A → ℝ :=
  fun x b =>
    if 1 ≤ h ∧ h ≤ H then
      min (inner ℝ (ϕ x b) (θhat t h) + Real.sqrt R * ellNorm (gram ϕ s a t h) (ϕ x b)) 1
    else 0

/-- The least-squares objective of layer `h` in episode `t` (algorithm box, p. 133):
`θ ↦ Σ_{i<t} (⟨ϕ(s^i_h, a^i_h), θ⟩ − r^i_h − V(s^i_{h+1}))²`, where `V = max_a Q̄^t_{h+1}(·, a)`
in the algorithm and `r i h = r^i_h`. -/
noncomputable def lsLoss (ϕ : S → A → EuclideanSpace ℝ (Fin d)) (s : ℕ → ℕ → S) (a : ℕ → ℕ → A)
    (r : ℕ → ℕ → ℝ) (V : S → ℝ) (t h : ℕ) (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i ∈ Finset.Ico 1 t, (inner ℝ (ϕ (s i h) (a i h)) θ - r i h - V (s i (h + 1))) ^ 2

/-- The computations of LSVI-UCB with inputs `R, ρ > 0` along one realization of the data of `T`
episodes of horizon `H` (Foster & Rakhlin, arXiv:2312.16730v1, algorithm box, p. 133, and
p. 134). The data are the states `s t h = s^t_h` and rewards `r t h = r^t_h`; the policy of
episode `t` is `pol t`, with `pol t h x = π̂^t_h(x)`, so the action is `a^t_h = π̂^t_h(s^t_h)`;
`θhat t h = θ̂^t_h`. For every episode `t ∈ [T]` and layer `h ∈ [H]`:

1. `θ̂^t_h ∈ arg min_{θ ∈ B^d_2(ρ)} Σ_{i<t} (⟨ϕ(s^i_h, a^i_h), θ⟩ − r^i_h − max_a Q̄^t_{h+1}(s^i_{h+1}, a))²`;
2. `π̂^t_h(x) ∈ arg max_{a ∈ A} Q̄^t_h(x, a)` for every state `x`.

`Q̄^t_h` is `Qbar`, with `Q̄^t_{H+1} ≡ 0`.

**Formalization Note.** Ties in both `arg min` and `arg max` are left open: every selection
satisfies this predicate. `max_a Q̄^t_{h+1}(s', a)` is `⨆ a`; `Q̄^t_{h+1}` is bounded, so this is
the maximum whenever it is attained. If `Q̄^t_h(x, ·)` has no maximizer, no policy satisfies
condition 2: the algorithm is then undefined, as in the book. -/
def IsLSVITrace (ϕ : S → A → EuclideanSpace ℝ (Fin d)) (R ρ : ℝ) (H T : ℕ) (s : ℕ → ℕ → S)
    (r : ℕ → ℕ → ℝ) (θhat : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (pol : ℕ → ℕ → S → A) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ h ∈ Finset.Icc 1 H,
    θhat t h ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ ∧
    (∀ θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ,
      lsLoss ϕ s (fun i k => pol i k (s i k)) r
          (fun x => ⨆ b, Qbar ϕ R H s (fun i k => pol i k (s i k)) θhat t (h + 1) x b) t h
          (θhat t h) ≤
        lsLoss ϕ s (fun i k => pol i k (s i k)) r
          (fun x => ⨆ b, Qbar ϕ R H s (fun i k => pol i k (s i k)) θhat t (h + 1) x b) t h θ) ∧
    (∀ x b, Qbar ϕ R H s (fun i k => pol i k (s i k)) θhat t h x b ≤
      Qbar ϕ R H s (fun i k => pol i k (s i k)) θhat t h x (pol t h x))

/-- The regret of the policies `π̂^1, …, π̂^T` played in `T` episodes (Foster & Rakhlin,
arXiv:2312.16730v1, (5.3), p. 82, as used on p. 137):
`Reg = Σ_{t=1}^T f^M(π_M) − f^M(π̂^t)`. -/
noncomputable def regret (M : EpisodicMDP S A) (H T : ℕ) (pol : ℕ → ℕ → S → A) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (M.optValue H - M.valueDet H (pol t))

end FoundationsRL.LSVI


