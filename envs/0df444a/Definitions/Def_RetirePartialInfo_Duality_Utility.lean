-- Prove2me | Definitions.Def_RetirePartialInfo_Duality_Utility
-- name    : RetirePartialInfo_Duality_Utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:53.694717+00:00
-- url     : https://prove2.me/theorems/27d76eb8-0b78-4dd7-b9a6-91e906397e34
-- title:
--   Assumption 2.2 and (11), pp. 10–11 — utilities, inverse marginal utility I, convex dual Ũ
-- statement:
--   **Utilities and their convex duals** (Assumption 2.2 and (11) of Chen, Jeon and Wong).
--
--   A utility function is a map $U:[0,T]\times(0,\infty)\to\mathbb R$. **Assumption 2.2** requires that $U\in C^\infty([0,T]\times(0,\infty))$ and
--   1. $U(t,\cdot)$ is strictly concave, with $\lim_{c\to0+}\partial_cU(t,c)=+\infty$ and $\lim_{c\to+\infty}\partial_cU(t,c)=0$;
--   2. the inverse $I(t,\cdot)$ of $\partial_cU(t,\cdot)$ satisfies, for some constants $K_1>0$, $k_1,k_2\ge1$,
--   $$I(t,y)\le K_1(1+y^{-k_1}),\qquad |\partial_yI(t,y)|\le K_1(1+y^{-k_2}),\qquad (t,y)\in[0,T]\times(0,\infty).$$
--
--   The inverse marginal utility is $I(t,y)=\inf\{c>0:\partial_cU(t,c)\le y\}$, and the convex dual is
--   $$\tilde U(t,y):=\sup_{c>0}\bigl[U(t,c)-yc\bigr].$$
--
--   The paper applies Assumption 2.2 to the felicity function $U_1$ and to the bequest function $U_2$; logarithmic and CRRA utilities satisfy it. The dual functions $\tilde U_1,\tilde U_2$ are the integrands of the dual value functions (13)–(14).
--
--   **Formalization Note.** Values of $U(t,c)$ for $c\le0$ or $t\notin[0,T]$ are unconstrained. Under part 1, $\partial_cU(t,\cdot)$ is a continuous strictly decreasing bijection of $(0,\infty)$ onto itself, so for $y>0$ the infimum defining $I$ is the unique $c>0$ with $\partial_cU(t,c)=y$. The identity $\tilde U(t,y)=U(t,I(t,y))-yI(t,y)$ is the milestone (11), not part of the definition. The page states the constants once for $i=1,2$; posing them per utility is equivalent, since two sets of constants merge into one ($2\max K$, $\max k$).
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 10–11, Assumption 2.2 and (11)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market

open Filter Set
open scoped Topology

namespace RetirePartialInfo.Duality

/-- Assumption 2.2 (ii), p. 11 (SSRN 3683553, June 8, 2021): `I(t, ·)`, "the inverse function of
`∂_c U(t, c)`": `I(t, y) = inf {c > 0 : ∂_c U(t, c) ≤ y}`.

**Formalization Note.** Under Assumption 2.2 (i), `∂_c U(t, ·)` is a continuous, strictly decreasing
bijection of `(0, ∞)` onto itself, so for `y > 0` this infimum is the unique `c > 0` with
`∂_c U(t, c) = y`. Values at `y ≤ 0` play no role. -/
noncomputable def Iinv (U : ℝ → ℝ → ℝ) (t y : ℝ) : ℝ :=
  sInf {c | 0 < c ∧ deriv (U t) c ≤ y}

/-- (11), p. 11 (SSRN 3683553, June 8, 2021): the convex dual of the concave utility `U`,
`Ũ(t, y) := sup_{c>0} [U(t, c) − yc]` (a supremum of real numbers; that it equals
`U(t, I(t, y)) − y I(t, y)` is a theorem). -/
noncomputable def Utilde (U : ℝ → ℝ → ℝ) (t y : ℝ) : ℝ :=
  sSup ((fun c => U t c - y * c) '' Ioi 0)

/-- **Assumption 2.2**, pp. 10–11 (SSRN 3683553, June 8, 2021), for one utility function
`U : [0, T] × (0, ∞) → ℝ` (applied to `U_1` and to `U_2`):
`U ∈ C^∞([0, T] × (0, ∞))`, and
1. (i) `U(t, ·)` is strictly concave on `(0, ∞)` with `lim_{c→0+} ∂_c U(t, c) = +∞` and
   `lim_{c→+∞} ∂_c U(t, c) = 0`, for every `t ∈ [0, T]`;
2. (ii) for some constants `K_1 > 0`, `k_1, k_2 ≥ 1`, the inverse `I` of `∂_c U` satisfies
   `I(t, y) ≤ K_1(1 + y^{−k_1})` and `|∂_y I(t, y)| ≤ K_1(1 + y^{−k_2})` for all
   `(t, y) ∈ [0, T] × (0, ∞)`.

**Formalization Note.** Values of `U(t, c)` for `c ≤ 0` or `t ∉ [0, T]` are unconstrained. The page
writes the constants once for `i = 1, 2`; posing them per utility is equivalent (two sets of
constants merge into one by taking `2 max K` and `max k`). -/
def Assumption22 (p : Params) (U : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => U q.1 q.2) (Icc 0 p.T ×ˢ Ioi 0) ∧
  (∀ t ∈ Icc 0 p.T, StrictConcaveOn ℝ (Ioi 0) (U t)) ∧
  (∀ t ∈ Icc 0 p.T, Tendsto (deriv (U t)) (𝓝[>] 0) atTop) ∧
  (∀ t ∈ Icc 0 p.T, Tendsto (deriv (U t)) atTop (𝓝 0)) ∧
  ∃ K1 : ℝ, 0 < K1 ∧ ∃ k1 k2 : ℝ, 1 ≤ k1 ∧ 1 ≤ k2 ∧
    ∀ t ∈ Icc 0 p.T, ∀ y : ℝ, 0 < y →
      Iinv U t y ≤ K1 * (1 + y ^ (-k1)) ∧
      |deriv (fun z => Iinv U t z) y| ≤ K1 * (1 + y ^ (-k2))

end RetirePartialInfo.Duality


