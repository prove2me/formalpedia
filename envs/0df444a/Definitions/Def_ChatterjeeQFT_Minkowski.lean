-- Prove2me | Definitions.Def_ChatterjeeQFT_Minkowski
-- name    : ChatterjeeQFT_Minkowski
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T20:39:44.401985+00:00
-- url     : https://prove2.me/theorems/21c94ede-d598-439c-8508-84ee46409b19
-- title:
--   Minkowski space $\mathbb{R}^{1,3}$ and the restricted Lorentz group
-- statement:
--   Minkowski spacetime is modelled as $\mathbb{R}^{1,3}$: four-vectors are real-valued
--   functions on a four-element index set, written $x = (x^0, x^1, x^2, x^3)$. The **Minkowski inner
--   product** is
--
--   $$(x, y) \;=\; x^0 y^0 - \big(x^1 y^1 + x^2 y^2 + x^3 y^3\big),$$
--
--   and $x^2 := (x, x)$ is the **Minkowski square**.
--
--   A **Lorentz transformation** is a real $4 \times 4$ matrix $L$, acting on four-vectors by
--   matrix-vector multiplication, such that $(Lx, Ly) = (x, y)$ for all $x, y$. The **restricted
--   Lorentz group** $SO^{\uparrow}(1,3)$ consists of those Lorentz transformations that are in
--   addition *proper*, $\det L = 1$, and *orthochronous*, $L^0{}_0 > 0$. These are the coordinate
--   changes under which special relativity requires the laws of physics to be invariant.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 9 (Special relativity), §9.1-§9.2, pp. 37-38.

import Mathlib

/-!
# Minkowski space `R^{1,3}`, Lorentz transformations, and the restricted Lorentz group

Following S. Chatterjee, *Lectures on Quantum Field Theory*, Lecture 9.
-/

open Matrix

namespace ChatterjeeQFT

/-- The Minkowski inner product on `R^{1,3}`, with signature `(+,-,-,-)`:
`(x, y) = x⁰y⁰ - (x¹y¹ + x²y² + x³y³)`. -/
def minkowskiInner (x y : Fin 4 → ℝ) : ℝ :=
  x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)

/-- The Minkowski square `x² = (x, x)`. -/
def minkowskiSq (x : Fin 4 → ℝ) : ℝ := minkowskiInner x x

/-- A Lorentz transformation: a linear map of `R^{1,3}` preserving the Minkowski inner
product. -/
def IsLorentz (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ x y : Fin 4 → ℝ, minkowskiInner (L *ᵥ x) (L *ᵥ y) = minkowskiInner x y

/-- The restricted Lorentz group `SO↑(1,3)`: Lorentz transformations with determinant `1`
that are orthochronous (`L⁰₀ > 0`). -/
def IsRestrictedLorentz (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  IsLorentz L ∧ L.det = 1 ∧ 0 < L 0 0

end ChatterjeeQFT


