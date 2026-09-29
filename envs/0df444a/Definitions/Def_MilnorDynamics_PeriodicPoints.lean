-- Prove2me | Definitions.Def_MilnorDynamics_PeriodicPoints
-- name    : MilnorDynamics_PeriodicPoints
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T10:40:35.904985+00:00
-- url     : https://prove2.me/theorems/f7556267-5268-4875-9814-ea9802d33cbe
-- title:
--   Fixed point index; repelling and non-repelling periodic points (Milnor §§12–14)
-- statement:
--   Notions from Milnor's §§12–14 (*Holomorphic Fixed Point Formula*, *Most Periodic Orbits Repel*, *Repelling Cycles are Dense in J*) for a self-map $f$ of the Riemann sphere $\hat{\mathbb C}$.
--
--   1. The **fixed point index** of a fixed point $z$ with multiplier $\lambda\neq1$ is $\iota(f,z)=\dfrac{1}{1-\lambda}$ (Lemma 12.2, formula (12:2)).
--   2. A periodic point is **repelling** if the multiplier $\lambda$ of its cycle satisfies $|\lambda|>1$, and **attracting or indifferent** if $|\lambda|\le1$.
--
--   **Formalization Note** The index is defined by the formula $1/(1-\lambda)$ for every point; it agrees with Milnor's residue index $\frac{1}{2\pi i}\oint\frac{dz}{z-f(z)}$ exactly when $\lambda\neq1$, and all statements using it assume $\lambda\neq1$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §12, p. 143, Lemma 12.2 (index formula (12:2)); §13, p. 153 (cycles and their multipliers)

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- The holomorphic fixed point index `ι(g, z) = 1 / (1 - λ)` of a fixed point `z` of `g` with
multiplier `λ`. This is Milnor's residue index in the case `λ ≠ 1` (Lemma 12.2); for `λ = 1`
the formula is not meaningful and the value is a junk value. -/
noncomputable def fixedPointIndex (g : OnePoint ℂ → OnePoint ℂ) (z : OnePoint ℂ) : ℂ :=
  1 / (1 - multiplier g z)

/-- The repelling periodic points of `g`: periodic points whose cycle has multiplier `|λ| > 1`. -/
def repellingPeriodicPts (g : OnePoint ℂ → OnePoint ℂ) : Set (OnePoint ℂ) :=
  {p | p ∈ Function.periodicPts g ∧ 1 < ‖multiplier g p‖}

/-- The attracting or indifferent periodic points of `g`: periodic points whose cycle has
multiplier `|λ| ≤ 1`. -/
def nonRepellingPeriodicPts (g : OnePoint ℂ → OnePoint ℂ) : Set (OnePoint ℂ) :=
  {p | p ∈ Function.periodicPts g ∧ ‖multiplier g p‖ ≤ 1}

end MilnorDynamics


