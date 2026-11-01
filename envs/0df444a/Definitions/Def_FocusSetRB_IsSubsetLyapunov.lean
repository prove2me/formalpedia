-- Prove2me | Definitions.Def_FocusSetRB_IsSubsetLyapunov
-- name    : FocusSetRB_IsSubsetLyapunov
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:40.838317+00:00
-- url     : https://prove2.me/theorems/3b72e995-9227-4e86-a53a-d06cb019c313
-- title:
--   Subset Lyapunov functions (Definition 1)
-- statement:
--   Let $\mathcal D$ be a collection of subsets of $[N]$, and let $h(\cdot,D)$, $D\in\mathcal D$, be real functions of the system state such that $h(x,D)$ depends only on the states of the arms in $D$. They are **subset Lyapunov functions** for $\bar\pi^*$ with constants $\rho_2\in(0,1)$, $K_{\mathrm{drift}}>0$, $K_{\mathrm{dist}}>0$, $L_h>0$ if, for every $D\in\mathcal D$ and every system state $x$:
--
--   1. (drift) $\displaystyle \mathbb E\big[h(X_1,D)\mid X_0=x,\ A_0(i)\sim\bar\pi^*(\cdot\mid S_0(i))\ \forall i\in D\big]\le\rho_2\,h(x,D)+\frac{K_{\mathrm{drift}}}{\sqrt N}$;
--   2. (distance domination) $h(x,D)\ge K_{\mathrm{dist}}\,\|x(D)-m(D)\mu^*\|_1$;
--   3. (Lipschitz continuity in $D$) $|h(x,D')-h(x,D)|\le L_h\big(m(D')-m(D)\big)$ for $D\subseteq D'$ in $\mathcal D$.
--
--   The function $h(\cdot,D)$ witnesses the convergence of the arms of a fixed set $D$ to $m(D)\mu^*$ when they follow $\bar\pi^*$; Theorem 5 combines it with conditions on how the focus set moves.
--
--   **Formalization Note** The constants are parameters of the predicate. In the drift condition the arms outside $D$ take arbitrary actions, quantified over all choices; $h(\cdot,D)$ does not depend on them.
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Definition 1, eqs. (12)–(14), p.13

import Mathlib
import Definitions.Def_FocusSetRB_scaledCount

namespace FocusSetRB

variable {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ}

/-- **Subset Lyapunov functions** for `π̄*` (arXiv:2402.05689v4, Definition 1, eqs. (12)–(14),
p.13). Let `𝒟` be a collection of subsets of `[N]` and `h(·, D)`, `D ∈ 𝒟`, real functions of the
system state such that `h(·, D)` depends only on the states of the arms in `D`. They are subset
Lyapunov functions with constants `ρ₂ ∈ (0, 1)`, `K_drift > 0`, `K_dist > 0`, `L_h > 0` if:
1. (drift, (12)) for every `D ∈ 𝒟` and state `x`,
   `𝔼[h(X₁, D) | X₀ = x, A₀(i) ∼ π̄*(·|S₀(i)) ∀ i ∈ D] ≤ ρ₂ h(x, D) + K_drift/√N`;
2. (distance domination, (13)) `h(x, D) ≥ K_dist ‖x(D) − m(D)μ*‖₁`;
3. (Lipschitz continuity in `D`, (14)) `|h(x, D') − h(x, D)| ≤ L_h (m(D') − m(D))` for
   `D ⊆ D'` in `𝒟`.

**Formalization Note.** The source's "there exist constants" are parameters of the predicate
(Theorem 5 states its bound in terms of them). In (12) the arms outside `D` take arbitrary
actions `aOut` (quantified universally), and the expectation is over the ideal actions and the
next state. `h` is a function on all subsets; only its values on `𝒟` are constrained. -/
def IsSubsetLyapunov (M : SingleArmMDP S) (y : S → Bool → ℝ) (𝒟 : Set (Finset (Fin N)))
    (h : (Fin N → S) → Finset (Fin N) → ℝ) (ρ₂ Kdrift Kdist Lh : ℝ) : Prop :=
  (∀ D ∈ 𝒟, ∀ x x' : Fin N → S, (∀ i ∈ D, x i = x' i) → h x D = h x' D) ∧
  (0 < ρ₂ ∧ ρ₂ < 1 ∧ 0 < Kdrift ∧
    ∀ D ∈ 𝒟, ∀ (x : Fin N → S) (aOut : Fin N → Bool),
      ∑ Ahat, idealLaw y x Ahat * ∑ x', stepProb M x (followOn D Ahat aOut) x' * h x' D ≤
        ρ₂ * h x D + Kdrift / Real.sqrt N) ∧
  (0 < Kdist ∧ ∀ D ∈ 𝒟, ∀ x : Fin N → S, Kdist * l1Dev y x D ≤ h x D) ∧
  (0 < Lh ∧ ∀ D ∈ 𝒟, ∀ D' ∈ 𝒟, D ⊆ D' → ∀ x : Fin N → S,
    |h x D' - h x D| ≤ Lh * (frac D' - frac D))

end FocusSetRB


