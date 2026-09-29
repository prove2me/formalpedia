-- Prove2me | Definitions.Def_ImprovedLinBandits_OFUL_IsOFULRun
-- name    : ImprovedLinBandits_OFUL_IsOFULRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:19:32.047809+00:00
-- url     : https://prove2.me/theorems/fe82473a-09d6-443f-9066-b8092fe2f380
-- title:
--   Runs of the OFUL algorithm
-- statement:
--   Let $D_1, D_2, \dots \subseteq \mathbb R^d$ be decision sets (which may depend on the outcome $\omega$, i.e. on the past), $X_t$ the actions, $Y_t$ the rewards and $\widetilde\theta_t$ the optimistic parameters, and let $C_t$ be the confidence ellipsoid of Theorem 2 built from $(R, S, \lambda, \delta)$ and the first $t$ rounds. The process is a **run of the OFUL algorithm** ("optimism in the face of uncertainty linear bandit algorithm") if for every outcome and every round $t \ge 1$
--
--   $$(X_t, \widetilde\theta_t) \in \operatorname*{argmax}_{(x,\theta) \in D_t \times C_{t-1}} \langle x, \theta\rangle ,$$
--
--   that is, $X_t \in D_t$, $\widetilde\theta_t \in C_{t-1}$ and $\langle x, \theta\rangle \le \langle X_t, \widetilde\theta_t\rangle$ for all $x \in D_t$ and $\theta \in C_{t-1}$ (Figure 1 of the paper).
--
--   Any tie-breaking rule is allowed. The definition presupposes that the maximum is attained, as the paper's argmax does. Runs exist whenever every $D_t$ is nonempty and compact, since $C_{t-1}$ is then nonempty and compact for $\lambda > 0$, $S \ge 0$.
--
--   **Formalization Note** Round $t+1$ uses `confidenceSet … t`, the paper's $C_{t-1}$ at round $t$. The values at index $0$ are never used.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 3, §2 and Figure 1 (OFUL algorithm)

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_ImprovedLinBandits_OFUL_confidenceSet

open Matrix NNReal

namespace ImprovedLinBandits.OFUL

/-- `(D, X, Y, θtilde)` is a run of the OFUL algorithm (Abbasi-Yadkori, Pál, Szepesvári,
NIPS 2011, §2 and Figure 1, p. 3) with the confidence sets `C_t = confidenceSet d R S lam δ X Y t`
of Theorem 2: for every outcome `ω` and every round `t + 1`, the pair `(X_{t+1}, θ̃_{t+1})` lies in
`D_{t+1} × C_t` and maximizes `⟨x, θ⟩` over `D_{t+1} × C_t`. (Round `t + 1` uses `C_t`, which is the
paper's `C_{t-1}` at round `t`.) Every tie-breaking rule is allowed. The predicate presupposes that
the maximum is attained, as the paper's `argmax` does; this is the case when `D_{t+1}` is compact and
nonempty, since `C_t` is then compact and nonempty for `λ > 0`, `S ≥ 0`. The values at index `0` are
never used. -/
def IsOFULRun {Ω : Type*} (d : ℕ) (R : ℝ≥0) (S lam δ : ℝ)
    (D : ℕ → Ω → Set (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (Y : ℕ → Ω → ℝ)
    (θtilde : ℕ → Ω → Fin d → ℝ) : Prop :=
  ∀ (ω : Ω) (t : ℕ),
    X (t + 1) ω ∈ D (t + 1) ω ∧
    θtilde (t + 1) ω ∈ confidenceSet d R S lam δ X Y t ω ∧
    ∀ x ∈ D (t + 1) ω, ∀ θ ∈ confidenceSet d R S lam δ X Y t ω,
      x ⬝ᵥ θ ≤ X (t + 1) ω ⬝ᵥ θtilde (t + 1) ω

end ImprovedLinBandits.OFUL


