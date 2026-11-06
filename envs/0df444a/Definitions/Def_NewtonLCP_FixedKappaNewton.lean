-- Prove2me | Definitions.Def_NewtonLCP_FixedKappaNewton
-- name    : NewtonLCP_FixedKappaNewton
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:19.618299+00:00
-- url     : https://prove2.me/theorems/419e1481-b6cc-4481-af9c-648d656dae18
-- title:
--   Subroutine FixedKappaNewton of Algorithm 3 (with a Newton-solve counter)
-- statement:
--   FixedKappaNewton$(M,q,x^0,s^0,\mu^0,\mu_1,\kappa)$ runs, with $\beta=\beta_N(\kappa)$ and $\delta=\delta_N(\kappa)$ from (54), starting from $(x,s,\mu)=(x^0,s^0,\mu^0)$ and while $\mu>\mu_1$:
--
--   1. compute the Newton step (10) for $(x,s,\mu/(1+\delta))$; if (10) has no solution or a non-unique one, return "$M\notin\mathcal P_\star$";
--   2. set $(x',s')=(x+\Delta x,s+\Delta s)$; if $(x',s')\notin\mathcal F_{>0}$, return "$\hat\kappa(M)>\kappa$";
--   3. compute the Newton step for $(x',s',\mu/(1+\delta))$; if (10) is singular, return "$M\notin\mathcal P_\star$";
--   4. set $(x_g,s_g,\mu_g)=(x'+\Delta x,s'+\Delta s,\mu/(1+\delta))$; if it is not in $\mathcal N^2(\beta)$, return "$\hat\kappa(M)>\kappa$"; otherwise continue from it.
--
--   When $\mu\le\mu_1$ it returns the current $(x,s,\mu)$. The run also reports the number of linear-system solves performed (one per executed step 1 or 3).
--
--   **Formalization Note** "(10) has no or a non-unique solution" is the test $\det(I_n+\mu'^{-1}XMX)=0$. The parameters $\beta,\delta$ are passed in. The while loop is a recursion with fuel $\lceil\log(\mu^0/\mu_1)/\log(1+\delta)\rceil+1$, which for $\mu^0,\mu_1,\delta>0$ is never exhausted (proved in the verification file); an exhausted fuel would be reported as a separate outcome.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Algorithm 3, lines 1–14, p.32

import Mathlib
import Definitions.Def_NewtonLCP_NewtonStep

open Matrix

namespace NewtonLCP

/-!
# Subroutine `FixedKappaNewton` of Algorithm 3, with a Newton-solve counter

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), Algorithm 3, lines 1–14, p.32 (with (10), p.13,
and `N²(β)`, p.6).

From `(x, s, µ) = (x⁰, s⁰, µ⁰)`, while `µ > µ₁`, with `µ' = µ/(1+δ)`:
line 5 computes the Newton step for `(x, s, µ')`; line 6 returns "`M ∉ P⋆`" if (10) has no or a
non-unique solution; line 7 sets `(x', s') = (x + ∆x, s + ∆s)`; line 8 returns "`κ̂(M) > κ`" if
`(x', s') ∉ F_{>0}`; line 9 computes the Newton step for `(x', s', µ')`; line 10 as line 6;
line 11 sets `(x_g, s_g, µ_g) = (x' + ∆x, s' + ∆s, µ')`; line 12 returns "`κ̂(M) > κ`" if
`(x_g, s_g, µ_g) ∉ N²(β)`; line 13 continues from it. Line 14 returns `(x, s, µ)`.

**Formalization Note.**
* (10) is the linear system `(Iₙ + µ'⁻¹ XMX)(∆x/x) = err(x, s, µ')`; it has no solution or a
  non-unique one exactly when its matrix is singular, which lines 6 and 10 test as `det = 0`.
* The parameters `β, δ` are passed in (line 3 sets them by (54); Algorithm 3 passes
  `β_{2n}(κ), δ_{2n}(κ)`).
* The second component of the result counts linear-system solves: one at line 5 and one at
  line 9, counted when the line is executed (an exit at line 6 or 8 has used one solve, an exit
  at line 10 or 12 two). The algorithm never reads the counter.
* The `while` loop is a recursion on a fuel `⌈log(µ⁰/µ₁)/log(1+δ)⌉₊ + 1`. For `µ⁰, µ₁ > 0` and
  `δ > 0` the loop condition fails before the fuel runs out (after `k` rounds `µ = µ⁰/(1+δ)ᵏ`),
  so the fuel changes nothing; `outOfFuel` is the value of an exhausted fuel.
* Comparisons of real numbers are decided classically; the tests are exactly the printed ones.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Outcomes of `FixedKappaNewton`: a point `(x, s, µ)` (line 14), "`M ∉ P⋆`" (lines 6, 10),
"`κ̂(M) > κ`" (lines 8, 12), or an exhausted fuel. -/
inductive FKOut (ι : Type*) where
  | point (x s : ι → ℝ) (mu : ℝ)
  | notPStar
  | kappaTooSmall
  | outOfFuel

open Classical in
/-- The `while` loop of lines 4–13, run with `fuel` rounds from `(x, s, µ)`; `c` is the number of
Newton solves so far. -/
noncomputable def fkLoop (M : Matrix ι ι ℝ) (q : ι → ℝ) (mu1 β δ : ℝ) :
    ℕ → (ι → ℝ) → (ι → ℝ) → ℝ → ℕ → FKOut ι × ℕ
  | 0, x, s, mu, c => if mu1 < mu then (FKOut.outOfFuel, c) else (FKOut.point x s mu, c)
  | fuel + 1, x, s, mu, c =>
    if mu1 < mu then
      if (1 + (mu / (1 + δ))⁻¹ • (diagonal x * M * diagonal x)).det = 0 then
        (FKOut.notPStar, c + 1)
      else
        let x' := x + newtonDx M x s (mu / (1 + δ))
        let s' := s + newtonDs M x s (mu / (1 + δ))
        if (x', s') ∉ FeasPos M q then (FKOut.kappaTooSmall, c + 1)
        else if (1 + (mu / (1 + δ))⁻¹ • (diagonal x' * M * diagonal x')).det = 0 then
          (FKOut.notPStar, c + 2)
        else
          let xg := x' + newtonDx M x' s' (mu / (1 + δ))
          let sg := s' + newtonDs M x' s' (mu / (1 + δ))
          if ¬ InN2 M q β xg sg (mu / (1 + δ)) then (FKOut.kappaTooSmall, c + 2)
          else fkLoop M q mu1 β δ fuel xg sg (mu / (1 + δ)) (c + 2)
    else (FKOut.point x s mu, c)

/-- The fuel `⌈log(µ⁰/µ₁)/log(1+δ)⌉₊ + 1` of the `while` loop. -/
noncomputable def fkFuel (mu0 mu1 δ : ℝ) : ℕ :=
  ⌈Real.log (mu0 / mu1) / Real.log (1 + δ)⌉₊ + 1

/-- `FixedKappaNewton(M, q, x⁰, s⁰, µ⁰, µ₁, κ)` with `β = β_N(κ)`, `δ = δ_N(κ)` passed in
(Algorithm 3, lines 1–14): the outcome and the number of Newton solves. -/
noncomputable def fixedKappaNewton (M : Matrix ι ι ℝ) (q x0 s0 : ι → ℝ) (mu0 mu1 β δ : ℝ) :
    FKOut ι × ℕ :=
  fkLoop M q mu1 β δ (fkFuel mu0 mu1 δ) x0 s0 mu0 0

end NewtonLCP


