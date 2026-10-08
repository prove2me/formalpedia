-- Prove2me | Definitions.Def_Helfgott_PrimitiveLowZeroRightExclusion
-- name    : Helfgott_PrimitiveLowZeroRightExclusion
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-06T03:46:21.725493+00:00
-- url     : https://prove2.me/theorems/6397ed51-0b3a-49d5-9bf0-6f73f9b93956
-- title:
--   Finite one-sided zero exclusion for the original Goldbach major arcs
-- statement:
--   For a primitive Dirichlet character $\chi$ of conductor $d\ge1$, put $Q_d=2d$ when $d$ is odd and $Q_d=d$ when $d$ is even. Write $H_\chi(s)=L(s,\chi)$ for nonprincipal characters and use the pole-removed zeta function for the primitive principal character. This finite certificate states that, whenever $Q_d\le300000$, every zero in $-1/2\le\Re\rho\le2$ satisfies $$\Re\rho\le\frac12$$ below either height $200+75000000/Q_d$ or height $10^8/d$. It excludes zeros on the right of the critical line; it allows the trivial zero at zero.
-- source:
--   Primitive Dirichlet functional equation and gamma-factor zero locations in Mathlib. Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897, section 4.6. Written by Codex.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
open Complex
open scoped Classical
namespace Helfgott
def PrimitiveLowZeroRightExclusion : Prop :=
  ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),χ.IsPrimitive →
    let Q : ℕ := if Odd d then 2*d else d
    Q≤300000 →
    let H : ℂ → ℂ := if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction
    (∀ ρ : ℂ,-(1/2 : ℝ)≤ρ.re → ρ.re≤2 → H ρ=0 →
      |ρ.im|<200+75000000/(Q : ℝ) → ρ.re≤1/2) ∧
    (∀ ρ : ℂ,-(1/2 : ℝ)≤ρ.re → ρ.re≤2 → H ρ=0 →
      |ρ.im|<(10 : ℝ)^8/(d : ℝ) → ρ.re≤1/2)
end Helfgott


