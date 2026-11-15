-- Prove2me | Definitions.Def_FiniteEnergyPlane_QMember
-- name    : FiniteEnergyPlane_QMember
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-14T10:20:43.498632+00:00
-- url     : https://prove2.me/theorems/02f24a99-c4bd-4e08-908f-6ab562fc71e2
-- title:
--   Plane maps $\mathbb{C} \to \mathbb{C} \times \mathbb{C}$ of the weighted cylinder unknowns
-- statement:
--   Throughout, `QDom` $= W^{1,4} \times \mathbb{C} \times W^{1,4}$ is the space of unknowns from `FiniteEnergyPlane_TubeFamily`, and $W^{1,4} = $ `W1p 4 1` consists of triples $(f, \partial_s f, \partial_t f)$ of $L^4$ classes on the cylinder $\mathbb{R} \times \mathbb{R}/\mathbb{Z}$ (measure `cylMeasure`).
--
--   **Representatives.** For $w \in W^{1,4}$, `qRep w` $: \mathbb{R} \times \mathbb{R} \to \mathbb{R}^2$ is a continuous function, $1$-periodic in the second variable, that agrees `cylMeasure`-a.e. with the first component of $w$, when such a function exists; otherwise it is $0$.
--
--   **Cylinder coordinates.** For $z \in \mathbb{C}$, `cylCoord z` $= \big(\log|z| / 2\pi,\ \arg z / 2\pi\big)$, so that $z = e^{2\pi(s + it)}$ for $(s, t) = $ `cylCoord z` when $z \neq 0$.
--
--   **Plane maps.** For weights $\chi_T, \chi_N, \beta : \mathbb{R} \to \mathbb{R}$ and $x = (\zeta_T, c, \zeta_N) \in$ `QDom`, `qMember χT χN β x` $: \mathbb{C} \to \mathbb{C} \times \mathbb{C}$ is the map $G = (\psi, v)$ with, at $z \neq 0$ and $(s, t) = $ `cylCoord z`,
--   $$\psi(z) = z + e^{\chi_T(s)}\, \tilde\zeta_T(s, t), \qquad v(z) = \beta(s)\, c + e^{\chi_N(s)}\, \tilde\zeta_N(s, t),$$
--   where $\tilde\zeta = $ `vecToC (qRep ζ ·)` $\in \mathbb{C}$, and $G(0) = (0, c)$.
--
--   **Families.** For a curve $\gamma : \mathbb{R} \to$ `QDom`, `qFamily χT χN β γ` $: \mathbb{C} \times \mathbb{R} \to \mathbb{C} \times \mathbb{C}$ is $(z, t) \mapsto$ `qMember χT χN β (γ t) z`.
--
--   **Role.** `qMember` reads an unknown of `qMap` (`FiniteEnergyPlane_TubeFamily`) as a map on the whole plane $\mathbb{C}$, including $z = 0$, so that statements about zeros of `qMap` and curves of zeros can be phrased for maps $\mathbb{C} \to \mathbb{C} \times \mathbb{C}$ and their families.
-- source:
--   Normal form near a fast plane, toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

/-!
# The plane maps of the weighted cylinder unknowns

For unknowns `x = (ζT, c, ζN) ∈ QDom` (see `FiniteEnergyPlane_TubeFamily`), the map
`qMember χT χN β x : ℂ → ℂ × ℂ` is the map `G = (ψ, v)` that `x` parametrizes, read on the plane:
at `z = e^{2π(s+it)} ≠ 0`,
* `ψ(z) = z + e^{χT(s)} ζT(s, t)`;
* `v(z) = β(s) c + e^{χN(s)} ζN(s, t)`;

and `G(0) = (0, c)`. Here `ζT, ζN` are evaluated through `qRep`, a continuous `1`-periodic
representative of their first component (`0` if there is none), and `(s, t) = cylCoord z`.
For a curve `γ : ℝ → QDom`, `qFamily χT χN β γ (z, t) = qMember χT χN β (γ t) z`.
-/

namespace FiniteEnergyPlane

open MeasureTheory CauchyRiemannIndex
open scoped Real

noncomputable section

open Classical in
/-- A continuous `1`-periodic representative of the first component of `w ∈ W^{1,4}`, if one
exists, and `0` otherwise. -/
def qRep (w : ↥(W1p 4 1)) : ℝ × ℝ → Vec 1 :=
  if h : ∃ g : ℝ × ℝ → Vec 1, Continuous g ∧ (∀ s t, g (s, t + 1) = g (s, t)) ∧
      (((w : Triple 1 4).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] g) then Classical.choose h else 0

/-- Cylinder coordinates `(log |z| / 2π, arg z / 2π)` of `z ≠ 0`, so `z = e^{2π(s+it)}`. -/
def cylCoord (z : ℂ) : ℝ × ℝ := (Real.log ‖z‖ / (2 * π), Complex.arg z / (2 * π))

open Classical in
/-- The plane map `ℂ → ℂ × ℂ` parametrized by `x = (ζT, c, ζN)`. -/
def qMember (χT χN β : ℝ → ℝ) (x : QDom) (z : ℂ) : ℂ × ℂ :=
  if z = 0 then (0, x.2.1) else
    (z + (Real.exp (χT (cylCoord z).1) : ℂ) * vecToC (qRep x.1 (cylCoord z)),
      (β (cylCoord z).1 : ℂ) * x.2.1 +
        (Real.exp (χN (cylCoord z).1) : ℂ) * vecToC (qRep x.2.2 (cylCoord z)))

/-- The family of plane maps along a curve `γ : ℝ → QDom`. -/
def qFamily (χT χN β : ℝ → ℝ) (γ : ℝ → QDom) (p : ℂ × ℝ) : ℂ × ℂ :=
  qMember χT χN β (γ p.2) p.1

end

end FiniteEnergyPlane


