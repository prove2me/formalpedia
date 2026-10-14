-- Prove2me | Definitions.Def_CorruptRobustRL_ElimLB_MDP
-- name    : CorruptRobustRL_ElimLB_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:49:45.951988+00:00
-- url     : https://prove2.me/theorems/3f5bf93f-1baf-4fa9-8424-049fc750f2e6
-- title:
--   §2, pp. 6–8 — stochastic episodic instance (p₀, p, D_rew) on finite X × A, mean reward r⋆, Q⋆, V⋆ by backward recursion, optimal actions π⋆_h(x)
-- statement:
--   A **stochastic problem instance** $\mathcal M=(p_0,p,\mathcal D_{\mathrm{rew}})$ on a finite state set $\mathcal X$ and a finite nonempty action set $\mathcal A$ consists of
--
--   1. an initial state distribution $p_0$ on $\mathcal X$;
--   2. a transition kernel $p(\cdot\mid x,a)$, the same at every stage;
--   3. for every pair $(x,a)$ a reward distribution $\mathcal D_{\mathrm{rew}}(x,a)$ supported in $[0,1]$.
--
--   The mean reward is $r^\star(x,a)=\mathbb E_{R\sim\mathcal D_{\mathrm{rew}}(x,a)}[R]$. For a horizon $H$ and stages $h\in[H]$, the optimal value and Q-functions are defined by backward recursion from $V^\star_{H+1}\equiv0$:
--
--   $$
--   Q^\star_h(x,a)=r^\star(x,a)+\sum_{x'\in\mathcal X}p(x'\mid x,a)\,V^\star_{h+1}(x'),\qquad V^\star_h(x)=\max_{a\in\mathcal A}Q^\star_h(x,a).
--   $$
--
--   The optimal actions at $(h,x)$ form the set $\pi^\star_h(x)=\{a\in\mathcal A:Q^\star_h(x,a)=V^\star_h(x)\}$, and the optimal value of the instance is $V^\star=\sum_x p_0(x)V^\star_1(x)$.
--
--   These are the objects with respect to which confidence-admissibility and regret are measured in the lower bound for action-eliminating algorithms.
--
--   **Formalization Note** Stages are 0-based: the paper's stage $h$ is Lean's $h-1$. Because the kernel is stage-independent, the recursion is written on the number of remaining stages: `Vopt n` is the optimal value with $n$ stages left, so $V^\star_h=$ `Vopt (H+1-h)`. Reward distributions are discrete (`PMF ℝ`) with support in $[0,1]$. The recursion is the paper's own definition of $V^\star_h$ (p. 8).
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, pp. 6–8, §2 (problem instance M = (p0, p, D_rew), r⋆, Q⋆_h, V⋆_h, π⋆)

import Mathlib

namespace CorruptRobustRL.ElimLB

/-- A stochastic problem instance `ℳ = (p₀, p, D_rew)` on a finite environment `(X, A)`
(Lykouris–Simchowitz–Slivkins–Sun, arXiv:1911.08689v4, §2, p. 6): an initial state law `p0`,
a stage-independent transition kernel `p`, and reward laws `R x a` supported in `[0, 1]`.
Reward laws are discrete (`PMF ℝ`). -/
structure Instance (X A : Type) where
  p0 : PMF X
  p : X → A → PMF X
  R : X → A → PMF ℝ
  hR : ∀ x a, ∀ r ∈ (R x a).support, 0 ≤ r ∧ r ≤ 1

variable {X A : Type} [Fintype X] [Fintype A] [Nonempty A]

/-- The mean reward `r⋆(x, a) = E_{R ∼ D_rew(x,a)}[R]`. -/
noncomputable def Instance.rbar (inst : Instance X A) (x : X) (a : A) : ℝ :=
  ∑' r : ℝ, (inst.R x a r).toReal * r

/-- Optimal value with `n` stages remaining: `Vopt 0 ≡ 0` and
`Vopt (n+1) x = max_a (r⋆(x,a) + Σ_{x'} p(x'|x,a) Vopt n x')`. Since the kernel is
stage-independent, the paper's `V⋆_h` equals `Vopt (H + 1 - h)` (1-based stage `h`). -/
noncomputable def Vopt (inst : Instance X A) : ℕ → X → ℝ
  | 0, _ => 0
  | n + 1, x => Finset.univ.sup' Finset.univ_nonempty
      (fun a => inst.rbar x a + ∑ x', (inst.p x a x').toReal * Vopt inst n x')

/-- `Q⋆_h(x, a) = r⋆(x,a) + p(x,a)ᵀ V⋆_{h+1}` at the 0-based stage `h < H`
(the paper's stage `h + 1`); `V⋆_{h+1}` has `H - (h + 1)` stages remaining. -/
noncomputable def Qstar (inst : Instance X A) (H h : ℕ) (x : X) (a : A) : ℝ :=
  inst.rbar x a + ∑ x', (inst.p x a x').toReal * Vopt inst (H - (h + 1)) x'

/-- `V⋆_h(x)` at the 0-based stage `h` (paper's stage `h + 1`). -/
noncomputable def VstarAt (inst : Instance X A) (H h : ℕ) (x : X) : ℝ :=
  Vopt inst (H - h) x

/-- The optimal actions `π⋆_h(x) = {a : Q⋆_h(x, a) = V⋆_h(x)}` at the 0-based stage `h`. -/
def optActions (inst : Instance X A) (H h : ℕ) (x : X) : Set A :=
  {a | Qstar inst H h x a = VstarAt inst H h x}

/-- `V⋆ = Σ_x p₀(x) V⋆_1(x)`, the optimal expected total reward over `H` stages. -/
noncomputable def Vstar (inst : Instance X A) (H : ℕ) : ℝ :=
  ∑ x, (inst.p0 x).toReal * Vopt inst H x

end CorruptRobustRL.ElimLB


