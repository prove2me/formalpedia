-- Prove2me | Definitions.Def_GeoSemialgCSP_regMass
-- name    : GeoSemialgCSP_regMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:00.662204+00:00
-- url     : https://prove2.me/theorems/19361244-21aa-41d1-bc52-69b562996e63
-- title:
--   Region mass $\xi_A$ of a fractional solution
-- statement:
--   For a fractional solution with output points $x_1,\dots,x_n$ and distributions $G(z)\in\mathcal P_n$, and a region $A$, the **region mass** is
--   $$\xi_A(z)=\xi(z)(A)=\sum_{i:\ x_i\in A}G(z)_i .$$
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, p.13 (PDF p.14); Eq. (4), p.14 (PDF p.15)

import Mathlib

namespace GeoSemialgCSP

/-- **Region mass of a fractional solution.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, printed p.13 (PDF p.14), and Eq. (4),
printed p.14 (PDF p.15): for a region `A`, `ξ_A(z) = ξ(z)(A)`, the mass the distribution `ξ(z)`
on the points `x₁, …, x_n` puts on `A`. -/
noncomputable def regMass {U W : Type*} {R n : ℕ} (x : Fin n → U) (G : (Fin R → W) → Fin n → ℝ)
    (A : Set U) (z : Fin R → W) : ℝ :=
  ∑ i, (x ⁻¹' A).indicator (G z) i

end GeoSemialgCSP


