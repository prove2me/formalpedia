-- Prove2me | Definitions.Def_BorderD4_IsEpsUnit
-- name    : BorderD4_IsEpsUnit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:16.738468+00:00
-- url     : https://prove2.me/theorems/3d3bbac6-46cf-4bdf-810b-ac33a13543ca
-- title:
--   $\varepsilon$-units in $F[[\varepsilon,u]]$
-- statement:
--   A power series $g\in F[[\varepsilon,u]]$ is an $\varepsilon$-unit if
--   $$g=\varepsilon^{a}\tilde g,\qquad a\ge 0,\quad \tilde g\in F[[\varepsilon,u]],\quad \tilde g(0,0)\ne 0.$$
--   Every nonzero element of $F[[\varepsilon]]$ is an $\varepsilon$-unit, while $\varepsilon+u_1$ is not.
--
--   **Formalization Note** $F[[\varepsilon,u]]$ is `PowerSeries (MvPowerSeries τ F)`, power series in $\varepsilon$ over power series in $u$.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 4.2, p.38

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The ring `F[[ε, u]]`, as power series in `ε` over power series in `u`. Here `PowerSeries.constantCoeff`
sets `ε = 0` and `PowerSeries.map MvPowerSeries.constantCoeff` sets `u = 0`. -/
abbrev EpsSeries (F : Type*) [Field F] (τ : Type*) := PowerSeries (MvPowerSeries τ F)

/-- `g ∈ F[[ε, u]]` is an ε-unit: `g = ε^a g̃` for some `a ≥ 0` and some `g̃` with `g̃(0, 0) ≠ 0`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 4.2, p.38. -/
def IsEpsUnit {F τ : Type*} [Field F] (g : EpsSeries F τ) : Prop :=
  ∃ (a : ℕ) (g' : EpsSeries F τ), g = PowerSeries.X ^ a * g' ∧
    MvPowerSeries.constantCoeff (PowerSeries.constantCoeff g') ≠ 0

end BorderD4


