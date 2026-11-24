-- Prove2me | Definitions.Def_FTheoryK3Core
-- name    : FTheoryK3Core
-- status  : Definition
-- author  : @andreaskapfer
-- created : 2026-09-21T19:59:19.395952+00:00
-- url     : https://prove2.me/theorems/d1ea235d-008e-4bc6-8e30-f372973b335a
-- title:
--   Weierstrass model over the affine line: discriminant, $E_8$ points, K3 degree data
-- statement:
--   This bundle fixes the algebraic objects for an elliptically fibered Weierstrass model $y^2 = x^3 + f\,x + g$ over the affine line, with $f, g \in k[X]$ polynomials over a field $k$.
--
--   1. **Discriminant.** For $f, g \in k[X]$, $$\Delta(f,g) = 4f^3 + 27g^2 \in k[X].$$ This is the discriminant of the model up to the nonzero constant factor $-16$; its vanishing locus is the set of base points over which the fibre degenerates (the F-theory 7-branes).
--
--   2. **$E_8$ point (Kodaira type II\*).** A point $t_0 \in k$ is an $E_8$ point when $$\operatorname{ord}_{t_0}(f) \ge 4 \quad\text{and}\quad \operatorname{ord}_{t_0}(g) = 5,$$ where $\operatorname{ord}_{t_0}$ is the multiplicity of $t_0$ as a root. These are the vanishing orders of a Kodaira type II\* fibre, whose gauge algebra is $E_8$.
--
--   3. **K3 degree data.** The pair $(f,g)$ satisfies the Calabi--Yau/K3 degree bound when $$\deg f \le 8,\qquad \deg g \le 12,\qquad \Delta(f,g) \ne 0.$$ Over $\mathbb{P}^1$ these are the degrees of sections of $\mathcal{O}(8)$ and $\mathcal{O}(12)$ for an elliptic surface with $\chi = 24$ (the maximal, K3, case and below); $\Delta \ne 0$ excludes the everywhere-degenerate model.
--
--   **Formalization Note.** `natDegree` assigns degree $0$ to the zero polynomial, and `rootMultiplicity` is $0$ at a non-root and for the zero polynomial. The K3-bound predicate `IsK3Data` encodes only the degree inequalities and non-degeneracy, not a full surface-theoretic K3 hypothesis.
-- source:
--   Kodaira classification of singular fibres and Tate's algorithm: M. Schuett and T. Shioda, "Elliptic Surfaces," Adv. Stud. Pure Math. 60 (2010), arXiv:0907.0298 (Euler number of an elliptic surface = degree of the discriminant divisor = 12*deg L; elliptic K3 => 24 singular fibres). F-theory dictionary between Kodaira/Tate fibre types and gauge algebras up to E8, and 7-branes: T. Weigand, "TASI Lectures on F-theory," arXiv:1806.01854.

import Mathlib

open Polynomial

namespace FTheoryK3

variable {k : Type*} [Field k]

/-- Discriminant of the short Weierstrass model `y² = x³ + f x + g`. -/
noncomputable def Δ (f g : k[X]) : k[X] := 4 * f ^ 3 + 27 * g ^ 2

/-- A base point carrying a Kodaira type II* fiber (gauge algebra E₈):
    `ord f ≥ 4` and `ord g = 5`. -/
def IsE8Point (f g : k[X]) (t₀ : k) : Prop :=
  4 ≤ f.rootMultiplicity t₀ ∧ g.rootMultiplicity t₀ = 5

/-- Calabi–Yau / K3 Weierstrass data over the affine chart, with nondegenerate discriminant. -/
def IsK3Data (f g : k[X]) : Prop :=
  f.natDegree ≤ 8 ∧ g.natDegree ≤ 12 ∧ Δ f g ≠ 0

end FTheoryK3


