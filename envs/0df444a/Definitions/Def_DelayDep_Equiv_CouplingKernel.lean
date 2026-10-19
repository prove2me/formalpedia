-- Prove2me | Definitions.Def_DelayDep_Equiv_CouplingKernel
-- name    : DelayDep_Equiv_CouplingKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:00.695423+00:00
-- url     : https://prove2.me/theorems/4ac2e772-d5ef-4977-acb9-73b7deaafafd
-- title:
--   Proof of Theorem 1, p. 3349 — steps (ii)–(iii): the law of the coupled pair (S^c, T^c) given the endogenous draws (t, s) at offered wait z
-- statement:
--   Steps (ii)–(iii) of the construction in the proof of Theorem 1. Fix a joint pdf $f$ of (service, patience), its patience marginal $f^{ex}_T$, and an offered wait $z$. Given the endogenous draws — a patience time $t$ and a virtual service time $s$ at wait $z$ — the coupled customer's pair $(S^c, T^c)$ is generated as follows.
--
--   1. (ii) If $t \le z$ (the customer abandons in the endogenous system): $T^c = t$, and $S^c$ is drawn from the density $f(\cdot, t)/f^{ex}_T(t)$ on $[0,\infty)$, the conditional law of the exogenous service time given patience $t$.
--   2. (iii) If $t > z$ (the customer is served): $S^c = s$, and $T^c$ is drawn from the density
--   $$\frac{f(s, \cdot)\,\mathbb I_{\{\cdot > z\}}}{\int_z^\infty f(s, y)\,dy},$$
--   the conditional law of the exogenous patience given service time $s$ and patience $> z$.
--
--   The object defined is the resulting law $\mu_{f,z}(t,s)$ of $(S^c, T^c)$ on $\mathbb R^2$. It is the kernel of the verification step of Theorem 1.
--
--   **Formalization Note** The densities are built with `withDensity` of `ENNReal.ofReal` of the displayed ratios, and the laws of $(S^c,T^c)$ are images under $x \mapsto (x, t)$ and $y \mapsto (s, y)$. Where a denominator vanishes, Lean's division by zero gives the zero measure; those $(t, s)$ form a null set under the endogenous laws.
-- source:
--   Wu, Bassamboo & Perry, When service times depend on customers’ delays, Operations Research 70(6) (2022), p. 3349 (PDF 6), proof of Theorem 1, steps ii–iii

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

namespace DelayDep.Equiv

open MeasureTheory

/-- Steps (ii)–(iii) of the proof of Theorem 1, p. 3349, for a customer whose offered wait is `z`.
Given the endogenous draws `p = (t, s)` (patience `t`, virtual service time `s` at wait `z`), this
is the law of the coupled pair `(S^c, T^c)`:
* (ii) if `t ≤ z`: `T^c = t` and `S^c` has density `f(·, t) / f^ex_T(t)` on `[0, ∞)`;
* (iii) if `t > z`: `S^c = s` and `T^c` has density
  `f(s, ·) 1{· > z} / ∫_z^∞ f(s, y) dy`. -/
noncomputable def couplingMeasure (f : ℝ → ℝ → ℝ) (z : ℝ) (p : ℝ × ℝ) : Measure (ℝ × ℝ) :=
  if p.1 ≤ z then
    (pdfLaw (fun x => f x p.1 / fTex f p.1)).map (fun x => (x, p.1))
  else
    ((volume.restrict (Set.Ioi z)).withDensity
      (fun y => ENNReal.ofReal (f p.2 y / ∫ y' in Set.Ioi z, f p.2 y'))).map (fun y => (p.2, y))

end DelayDep.Equiv


