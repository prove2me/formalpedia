-- Prove2me | Definitions.Def_PNormReg_Scaled
-- name    : PNormReg_Scaled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:17.354482+00:00
-- url     : https://prove2.me/theorems/19b52174-d441-4d48-924e-8f87375f5080
-- title:
--   The scaled residual problem and the matrix game (21)
-- statement:
--   The residual after eliminating the constraints is $\phi(u)=h^\top u-u^\top Du-\|Au\|_p^p$, with optimum $\phi^\star$. For a scale $\zeta>0$ and $s=\|w\|_1$,
--
--   $$\bar A=\frac{A}{(8\zeta)^{1/p}},\quad\bar h=\frac h\zeta,\quad\bar D=\frac1{8\zeta}\Big(D+\big(\tfrac\zeta s\big)^{1-2/p}A^\top W^{1-2/p}A+\frac{hh^\top}{4\zeta}\Big),\quad\lambda_\xi=\min\Big\{\frac18,\Big(\frac1{128\xi^p}\Big)^{1/(p-1)}\Big\}.$$
--
--   For $L$ with $LL^\top=\bar D$, the game has $M=\rho\bar AL^{-\top}$ and $c=-\tfrac12\bar AL^{-\top}L^{-1}\bar h$, with $\rho=\tfrac12\sqrt{\|L^{-1}\bar h\|_2^2-1/2}$, and objective $h(x,y)=y^\top Mx-c^\top y$. A primal point $\tilde x$ is recovered as $\tilde u=L^{-\top}(\rho\tilde x+\tfrac12L^{-1}\bar h)$.
--
--   These objects carry the reduction of one residual problem to $O(\log p)$ matrix games.
--
--   **Formalization Note** $L$ is any factor with $LL^\top=\bar D$: the printed $\bar D^{1/2}$ and the Cholesky factor of p.25 are both covered. $\phi^\star$ is the real `sSup`; its attainment is a clause of the milestone on (17).
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), (17)–(18), pp.21–22; Lemma 10, p.22; Lemma 11, p.23; Cholesky form, p.25

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_PNormReg_Lewis

open Matrix

namespace PNormReg

/-!
# The scaled residual problem and the matrix game (21)

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), (17)–(18), p.21–22; Lemma 10, p.22; Lemma 11, p.23;
the Cholesky form, p.25.

**Formalization Note.**
* `L` is any matrix with `LL⊤ = D̄`. The printed `D̄^{1/2}` is one such `L`, and the Cholesky factor of
  p.25 is another. `D̄^{−1/2}` is written `L^{−⊤}` or `L^{−1}`, as p.25 does: `M = ρĀL^{−⊤}` and
  `c = −½ĀL^{−⊤}L^{−1}h̄`.
* `s` is `∥w∥₁`, the sum of the weights.
* `phiStar` is the real `sSup` of `φ`. Under the hypotheses of the lemmas `φ` has a maximum.
-/

variable {n k : ℕ}

/-- `φ(u) = h⊤u − u⊤Du − ∥Au∥_p^p` of (18). -/
noncomputable def phi (h : Fin k → ℝ) (D : Matrix (Fin k) (Fin k) ℝ)
    (A : Matrix (Fin n) (Fin k) ℝ) (p : ℝ) (u : Fin k → ℝ) : ℝ :=
  h ⬝ᵥ u - u ⬝ᵥ (D *ᵥ u) - lpPow p (A *ᵥ u)

/-- `φ⋆ = max_u φ(u)`. -/
noncomputable def phiStar (h : Fin k → ℝ) (D : Matrix (Fin k) (Fin k) ℝ)
    (A : Matrix (Fin n) (Fin k) ℝ) (p : ℝ) : ℝ :=
  sSup (Set.range (phi h D A p))

/-- `Ā := A/(8ζ)^{1/p}`. -/
noncomputable def scaledA (A : Matrix (Fin n) (Fin k) ℝ) (p ζ : ℝ) : Matrix (Fin n) (Fin k) ℝ :=
  ((8 * ζ) ^ (1 / p))⁻¹ • A

/-- `h̄ := h/ζ`. -/
noncomputable def scaledH (h : Fin k → ℝ) (ζ : ℝ) : Fin k → ℝ := ζ⁻¹ • h

/-- `A⊤W^{1−2/p}A`. -/
noncomputable def weightedGram (A : Matrix (Fin n) (Fin k) ℝ) (w : Fin n → ℝ) (p : ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Aᵀ * Matrix.diagonal (wPow w (1 - 2 / p)) * A

/-- `D̄ := (1/(8ζ))(D + (ζ/s)^{1−2/p}A⊤W^{1−2/p}A + hh⊤/(4ζ))` with `s = ∥w∥₁`. -/
noncomputable def scaledD (A : Matrix (Fin n) (Fin k) ℝ) (D : Matrix (Fin k) (Fin k) ℝ)
    (h : Fin k → ℝ) (w : Fin n → ℝ) (p ζ : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (1 / (8 * ζ)) • (D + (ζ / ∑ i, w i) ^ (1 - 2 / p) • weightedGram A w p +
    (1 / (4 * ζ)) • Matrix.vecMulVec h h)

/-- `λ_ξ := min{1/8, (1/(128ξ^p))^{1/(p−1)}}`. -/
noncomputable def lambdaXi (p ξ : ℝ) : ℝ := min (1 / 8) ((1 / (128 * ξ ^ p)) ^ (1 / (p - 1)))

/-- The left side `−h̄⊤u + u⊤D̄u` of the constraint of (19). -/
noncomputable def scaledConstraint (hbar : Fin k → ℝ) (Dbar : Matrix (Fin k) (Fin k) ℝ)
    (u : Fin k → ℝ) : ℝ :=
  -(hbar ⬝ᵥ u) + u ⬝ᵥ (Dbar *ᵥ u)

/-- `ρ := ½√(∥L^{−1}h̄∥₂² − 1/2)` (printed with `D̄^{−1/2}`, Lemma 11). -/
noncomputable def rhoOf (L : Matrix (Fin k) (Fin k) ℝ) (hbar : Fin k → ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (l2Norm (L⁻¹ *ᵥ hbar) ^ 2 - 1 / 2)

/-- The game matrix `M = ρĀL^{−⊤}`. -/
noncomputable def gameM (Abar : Matrix (Fin n) (Fin k) ℝ) (L : Matrix (Fin k) (Fin k) ℝ)
    (hbar : Fin k → ℝ) : Matrix (Fin n) (Fin k) ℝ :=
  rhoOf L hbar • (Abar * (L⁻¹)ᵀ)

/-- The game's linear term `c = −½ĀL^{−⊤}L^{−1}h̄`. -/
noncomputable def gameC (Abar : Matrix (Fin n) (Fin k) ℝ) (L : Matrix (Fin k) (Fin k) ℝ)
    (hbar : Fin k → ℝ) : Fin n → ℝ :=
  (-(1 / 2) : ℝ) • ((Abar * (L⁻¹)ᵀ) *ᵥ (L⁻¹ *ᵥ hbar))

/-- The game objective `h(x, y) = y⊤Mx − c⊤y` of (40); with `gameM`, `gameC` it is the objective
`y⊤(ρĀL^{−⊤})x + ½y⊤ĀL^{−⊤}L^{−1}h̄` of (21). -/
noncomputable def gameObj (M : Matrix (Fin n) (Fin k) ℝ) (c : Fin n → ℝ) (x : Fin k → ℝ)
    (y : Fin n → ℝ) : ℝ :=
  y ⬝ᵥ (M *ᵥ x) - c ⬝ᵥ y

/-- The recovery `ũ = L^{−⊤}(ρx̃ + ½L^{−1}h̄)` of Lemma 11 and p.25. -/
noncomputable def recover (L : Matrix (Fin k) (Fin k) ℝ) (hbar xt : Fin k → ℝ) : Fin k → ℝ :=
  (L⁻¹)ᵀ *ᵥ (rhoOf L hbar • xt + (1 / 2 : ℝ) • (L⁻¹ *ᵥ hbar))

end PNormReg


