-- Prove2me | Definitions.Def_ChitourPrescribedTime_Linear_timeChange
-- name    : ChitourPrescribedTime_Linear_timeChange
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:57:48.397682+00:00
-- url     : https://prove2.me/theorems/002ca55c-7a5e-49f9-a54e-502f75aff000
-- title:
--   Prescribed-time scaling: admissible weight $a$, parameter $\lambda(t)=1/\int_t^T a$ and new time $s(t)=\int_0^t\lambda$
-- statement:
--   Fix a prescribed time $T>0$. A function $a:[0,T]\to\mathbb R$ is an **admissible weight** if it is continuous and nonnegative on $[0,T]$ and
--   $$A(t) = \int_t^T a(\xi)\,d\xi > 0 \qquad \text{for every } t\in[0,T).$$
--   For such an $a$ the **time-varying homogeneity parameter** and the **new time** are
--   $$\lambda(t) = \frac{1}{\int_t^T a(\xi)\,d\xi}, \qquad s(t) = \int_0^t \lambda(\xi)\,d\xi, \qquad 0\le t<T.$$
--
--   The parameter $\lambda(t)$ grows to $+\infty$ as $t\to T^-$, and $s$ maps the finite horizon $[0,T)$ onto the infinite horizon $[0,\infty)$. This is what turns an exponential estimate in the time $s$ into a convergence estimate at the prescribed time $T$.
--
--   **Formalization Note** `AdmissibleWeight T a` bundles the four standing hypotheses: $T>0$, continuity of $a$ on $[0,T]$, nonnegativity of $a$ on $[0,T]$, and positivity of $\int_t^T a$ for $t\in[0,T)$. The functions `lam T a` and `sTime T a` are total functions on $\mathbb R$. Outside $[0,T)$ their values are meaningless (for example `lam T a T = 1/0 = 0` in Lean), and every statement of the mission uses them only for $t\in[0,T)$.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1026, eq. (6); p. 1027, eq. (10); p. 1030, Corollary 14, eq. (21)

import Mathlib

namespace ChitourPrescribedTime.Linear

/-- The standing hypothesis on the prescribed time `T` and the weight `a` (§3, p. 1027, and
Corollary 14, p. 1030): `T > 0`, and `a : [0, T] → ℝ` is continuous and nonnegative with
`∫_t^T a(ξ) dξ > 0` for every `t ∈ [0, T)`. Values of `a` outside `[0, T]` are irrelevant. -/
structure AdmissibleWeight (T : ℝ) (a : ℝ → ℝ) : Prop where
  T_pos : 0 < T
  continuousOn : ContinuousOn a (Set.Icc 0 T)
  nonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ a t
  tail_pos : ∀ t ∈ Set.Ico 0 T, 0 < ∫ ξ in t..T, a ξ

/-- The time-varying homogeneity parameter `λ(t) = 1 / ∫_t^T a(ξ) dξ` of (10)/(21); it is only
meaningful for `t ∈ [0, T)`. -/
noncomputable def lam (T : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / ∫ ξ in t..T, a ξ

/-- The new time `s(t) = ∫_0^t λ(ξ) dξ` of (6)/(21); it is only meaningful for `t ∈ [0, T)`. -/
noncomputable def sTime (T : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ ξ in (0)..t, lam T a ξ

end ChitourPrescribedTime.Linear


