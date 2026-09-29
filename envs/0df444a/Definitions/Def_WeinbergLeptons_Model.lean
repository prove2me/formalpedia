-- Prove2me | Definitions.Def_WeinbergLeptons_Model
-- name    : WeinbergLeptons_Model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T17:24:55.554554+00:00
-- url     : https://prove2.me/theorems/5ce0cfed-c5d5-4448-83d4-306f6fc99e32
-- title:
--   Weinberg's model of leptons: tree-level mass data
-- statement:
--   Tree-level data of Weinberg's model of leptons after spontaneous breaking of the $SU(2)\times U(1)$ gauge symmetry by the scalar vacuum expectation value $\langle\varphi\rangle=\lambda\binom10$.
--
--   A gauge-field configuration at a point is a vector $V=(A^1,A^2,A^3,B)\in\mathbb R^4$; $g$ and $g'$ are the couplings of the isospin fields $\vec A_\mu$ and the hypercharge field $B_\mu$. The file defines:
--
--   1. the spin-one mass terms of eq. (7), $-\tfrac18\lambda^2g^2[(A^1)^2+(A^2)^2]-\tfrac18\lambda^2(gA^3+g'B)^2$;
--   2. the symmetric mass-squared matrix $\mathcal M$ whose quadratic form is $-2\times$ this mass term;
--   3. the coefficient vectors of the fields of definite mass: $W=2^{-1/2}(A^1+iA^2)$ (eq. 8), $Z=(g^2+g'^2)^{-1/2}(gA^3+g'B)$ (eq. 10), $A=(g^2+g'^2)^{-1/2}(-g'A^3+gB)$ (eq. 11);
--   4. $M_W=\tfrac12\lambda g$ (eq. 9), $M_Z=\tfrac12\lambda(g^2+g'^2)^{1/2}$ (eq. 12), the rationalized charge $e=gg'/(g^2+g'^2)^{1/2}$ (eq. 15), the weak coupling $G_W$ defined by $G_W/\sqrt2=g^2/8M_W^2$ (eq. 16), the electron mass $M_e=\lambda G_e$;
--   5. the scalar self-interaction $-M_1^2\varphi^\dagger\varphi+h(\varphi^\dagger\varphi)^2$ of eq. (4) restricted to $\varphi=(x,0)$.
--
--   These are the objects in terms of which all theorems of the mission are stated.
--
--   **Formalization Note** Eq. (7) is taken as printed in the paper. Lean's division returns $0$ on division by zero, so $Z$, $A$ and $e$ vanish when $g=g'=0$ and $G_W=0$ when $\lambda g=0$; theorems carry the hypotheses excluding these cases where needed. $M_W$ and $M_Z$ are signed (no absolute value).
-- source:
--   S. Weinberg, A Model of Leptons, Phys. Rev. Lett. 19, 1264-1266 (1967), https://doi.org/10.1103/PhysRevLett.19.1264, p. 1264 eqs. (4), p. 1265 eqs. (5)-(16)

import Mathlib

/-!
# Weinberg, "A Model of Leptons" (Phys. Rev. Lett. 19, 1264 (1967)) — tree-level data

A real gauge-field configuration at a point is encoded as a vector `V : Fin 4 → ℝ` with
`V 0 = A¹`, `V 1 = A²`, `V 2 = A³` (the isospin gauge fields) and `V 3 = B` (the hypercharge
gauge field). `g`, `g'` are the isospin and hypercharge gauge couplings and `lam` is the
vacuum expectation value `λ = ⟨φ⁰⟩` of the scalar doublet.
-/

namespace WeinbergLeptons

/-- The spin-one mass terms of the Lagrangian after symmetry breaking, eq. (7):
`-(1/8) λ² g² [(A¹)² + (A²)²] - (1/8) λ² (g A³ + g' B)²`. -/
noncomputable def vectorMassTerm (g g' lam : ℝ) (V : Fin 4 → ℝ) : ℝ :=
  -(1 / 8) * lam ^ 2 * g ^ 2 * (V 0 ^ 2 + V 1 ^ 2) - (1 / 8) * lam ^ 2 * (g * V 2 + g' * V 3) ^ 2

/-- The (mass)² matrix of the spin-one fields `(A¹, A², A³, B)`: the symmetric matrix `𝓜²`
whose quadratic form reproduces eq. (7) as `-(1/2) Vᵀ 𝓜² V`. -/
noncomputable def massSqMatrix (g g' lam : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![lam ^ 2 * g ^ 2 / 4, 0, 0, 0;
     0, lam ^ 2 * g ^ 2 / 4, 0, 0;
     0, 0, lam ^ 2 * g ^ 2 / 4, lam ^ 2 * g * g' / 4;
     0, 0, lam ^ 2 * g * g' / 4, lam ^ 2 * g' ^ 2 / 4]

/-- Coefficient vector of the charged field `W = 2^{-1/2} (A¹ + i A²)`, eq. (8). -/
noncomputable def wVec : Fin 4 → ℂ :=
  ![1 / (Real.sqrt 2 : ℂ), Complex.I / (Real.sqrt 2 : ℂ), 0, 0]

/-- Coefficient vector of `Z = (g² + g'²)^{-1/2} (g A³ + g' B)`, eq. (10). -/
noncomputable def zVec (g g' : ℝ) : Fin 4 → ℝ :=
  (1 / Real.sqrt (g ^ 2 + g' ^ 2)) • ![0, 0, g, g']

/-- Coefficient vector of `A = (g² + g'²)^{-1/2} (-g' A³ + g B)`, eq. (11). -/
noncomputable def photonVec (g g' : ℝ) : Fin 4 → ℝ :=
  (1 / Real.sqrt (g ^ 2 + g' ^ 2)) • ![0, 0, -g', g]

/-- `M_W = (1/2) λ g`, eq. (9). -/
noncomputable def wMass (g lam : ℝ) : ℝ := lam * g / 2

/-- `M_Z = (1/2) λ (g² + g'²)^{1/2}`, eq. (12). -/
noncomputable def zMass (g g' lam : ℝ) : ℝ := lam * Real.sqrt (g ^ 2 + g' ^ 2) / 2

/-- The rationalized electric charge `e = g g' / (g² + g'²)^{1/2}`, eq. (15). -/
noncomputable def electricCharge (g g' : ℝ) : ℝ := g * g' / Real.sqrt (g ^ 2 + g' ^ 2)

/-- The weak coupling constant defined by the first equality of eq. (16),
`G_W / √2 = g² / (8 M_W²)`, i.e. `G_W = √2 g² / (8 M_W²)`. -/
noncomputable def weakCoupling (g lam : ℝ) : ℝ := Real.sqrt 2 * g ^ 2 / (8 * wMass g lam ^ 2)

/-- The electron mass `M_e = λ G_e`, where `G_e` is the electron–scalar Yukawa coupling. -/
noncomputable def electronMass (Ge lam : ℝ) : ℝ := lam * Ge

/-- The scalar self-interaction terms of the Lagrangian (4), `-M₁² φ†φ + h (φ†φ)²`, evaluated on
the vacuum configuration `φ = (x, 0)` with `x` real. -/
noncomputable def scalarPotentialTerm (M1 h x : ℝ) : ℝ := -M1 ^ 2 * x ^ 2 + h * x ^ 4

end WeinbergLeptons


