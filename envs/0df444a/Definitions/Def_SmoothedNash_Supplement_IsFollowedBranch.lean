-- Prove2me | Definitions.Def_SmoothedNash_Supplement_IsFollowedBranch
-- name    : SmoothedNash_Supplement_IsFollowedBranch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:03:30.695447+00:00
-- url     : https://prove2.me/theorems/950eb49d-f663-40c0-b8f3-78c532f35c85
-- title:
--   The followed lifted branch of length $T$ with $\sigma_n(J_K) \ge \theta$
-- statement:
--   With $a = L_0 + L_1$, a curve $\gamma = (\gamma_x, \gamma_t) : [0, T] \to \mathbb R^n \times \mathbb R$ is **the followed lifted branch of length $T$ with row gap $\theta$** if:
--
--   1. $\gamma$ is $C^1$ on $[0, T]$ and has unit speed: $\|\gamma_x'(s)\|^2 + \gamma_t'(s)^2 = 1$;
--   2. $\gamma(0) = (0, 0)$ and $\gamma'(0)$ is a positive multiple of $(F(0)/a, 1)$, so the branch leaves $(0,0)$ into $t > 0$;
--   3. $K(\gamma(s)) = 0$ for all $s \in [0, T]$;
--   4. $\|\gamma_x(s)\| < 1$ and $\gamma_t(s) < 1$ for $s < T$, while $\|\gamma_x(T)\| = 1$ or $\gamma_t(T) = 1$ (the branch is stopped at its first point with $t = 1$ or $\|x\| = 1$);
--   5. $\sigma_n(J_K(\gamma(s))) \ge \theta$ for all $s \in [0, T]$.
--
--   This is the hypothesis of Theorem 4.5: the branch has finite length $T$ and the row singular value bound holds along it.
--
--   **Formalization Note** Derivatives are taken within $[0, T]$. Only points of this branch carry the singular-value bound, not every zero of $K$ (that stronger condition is Property 4.1).
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §4.1.1, p.26, and Theorem 4.5, p.28

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_homK
import Definitions.Def_SmoothedNash_Supplement_rowSigma
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The hypothesis of Theorem 4.5 on the followed lifted branch (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §4.1.1, p.26, and
Theorem 4.5, p.28): `γ = (γx, γt) : [0, T] → ℝ^n × ℝ` is the unit-speed `C¹` branch of zeros of the
homotopy `K` leaving `(0, 0)` into `t > 0`, stopped at its first point with `t = 1` or `‖x‖ = 1`, and
the smallest row singular value satisfies `σ_n(J_K) ≥ θ` along it. Precisely, with `a = L0 + L1`:
1. `γx` and `γt` are `C¹` on `[0, T]`, and `‖γx'(s)‖² + γt'(s)² = 1` on `[0, T]` (unit speed);
2. `γ(0) = (0, 0)` and `γ'(0)` is a positive multiple of `(F(0)/a, 1)` (the outgoing direction);
3. `K(γ(s)) = 0` for every `s ∈ [0, T]`;
4. `‖γx(s)‖ < 1` and `γt(s) < 1` for `s ∈ [0, T)`, and `‖γx(T)‖ = 1` or `γt(T) = 1`;
5. `σ_n(J_K(γ(s))) ≥ θ` for every `s ∈ [0, T]`.

**Formalization Note** `T` is the (finite) length of the branch. Derivatives are taken within
`[0, T]`. Only the points of this branch carry the singular-value bound (not every zero of `K`). -/
def IsFollowedBranch {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L0 L1 θ T : ℝ) (γx : ℝ → EuclideanSpace ℝ (Fin n)) (γt : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 γx (Set.Icc 0 T) ∧ ContDiffOn ℝ 1 γt (Set.Icc 0 T) ∧
  (∀ s ∈ Set.Icc 0 T,
    ‖derivWithin γx (Set.Icc 0 T) s‖ ^ 2 + (derivWithin γt (Set.Icc 0 T) s) ^ 2 = 1) ∧
  γx 0 = 0 ∧ γt 0 = 0 ∧
  (∃ c : ℝ, 0 < c ∧ derivWithin γx (Set.Icc 0 T) 0 = c • ((L0 + L1)⁻¹ • F 0) ∧
    derivWithin γt (Set.Icc 0 T) 0 = c) ∧
  (∀ s ∈ Set.Icc 0 T, homK F (L0 + L1) (γx s, γt s) = 0) ∧
  (∀ s ∈ Set.Ico 0 T, ‖γx s‖ < 1 ∧ γt s < 1) ∧ (‖γx T‖ = 1 ∨ γt T = 1) ∧
  (∀ s ∈ Set.Icc 0 T, θ ≤ rowSigma F (L0 + L1) (γx s, γt s))

end SmoothedNash.Supplement


