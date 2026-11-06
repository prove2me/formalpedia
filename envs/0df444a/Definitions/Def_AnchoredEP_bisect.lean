-- Prove2me | Definitions.Def_AnchoredEP_bisect
-- name    : AnchoredEP_bisect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:35.901344+00:00
-- url     : https://prove2.me/theorems/62d5c30e-6230-442c-98a0-03563106df29
-- title:
--   Bisection intervals of the line search
-- statement:
--   If the upper trial fails, the line search sets $a^-=0$, $a^+=\bar a_k$ and repeatedly evaluates the midpoint $a=(a^-+a^+)/2$, updating
--   $$
--   a^-\leftarrow a \ \text{ if } \psi_k(a)<p!\rho/\sqrt2,\qquad a^+\leftarrow a \ \text{ if } \psi_k(a)>p!\rho,
--   $$
--   and accepting $a$ if $p!\rho/\sqrt2\le\psi_k(a)\le p!\rho$ ($\rho=1/\sqrt2$). The $t$-th interval ($t=0,1,\dots$) is the pair $(a^-,a^+)$ before the $t$-th bisection trial.
--
--   **Formalization Note** Once a midpoint is accepted the interval is frozen, so all later midpoints equal the accepted step.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, Eq. (91), p.38

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_psi
import Definitions.Def_AnchoredEP_abar

namespace AnchoredEP

/-- **The bisection intervals of the line search.** Jiang–Yoon, arXiv:2609.30212, Appendix G.2,
Eq. (91), p.38: "Otherwise, it initializes `a⁻ = 0` and `a⁺ = ā_k`. At every bisection step it
evaluates `a = (a⁻ + a⁺)/2` and performs the update
`a⁻ ← a` if `ψ_k(a) < p!ρ/√2`; `a⁺ ← a` if `ψ_k(a) > p!ρ`; accept `a` if
`p!ρ/√2 ≤ ψ_k(a) ≤ p!ρ`", with `ρ = 1/√2`.

`bisect F p L ε sol z0 s t = (a⁻, a⁺)` is the interval before the `t`-th bisection trial
(`t = 0, 1, …`); the `t`-th trial is evaluated at its midpoint.

**Formalization Note.** Once a midpoint is accepted the interval is frozen, so every later
midpoint is the accepted step; the line search's step is the midpoint at the first accepted `t`
(`accepted`, `stepSize`). -/
noncomputable def bisect {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) : ℕ → ℝ × ℝ
  | 0 => (0, abar F p L ε s)
  | t + 1 =>
    let I := bisect F p L ε sol z0 s t
    let m := (I.1 + I.2) / 2
    if psi F p L sol z0 s m < (p.factorial : ℝ) * (1 / Real.sqrt 2) / Real.sqrt 2 then (m, I.2)
    else if (p.factorial : ℝ) * (1 / Real.sqrt 2) < psi F p L sol z0 s m then (I.1, m)
    else I

end AnchoredEP


