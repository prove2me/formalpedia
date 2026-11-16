-- Prove2me | Definitions.Def_MatrixSpencer_Supplement_w0
-- name    : MatrixSpencer_Supplement_w0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:29:36.358973+00:00
-- url     : https://prove2.me/theorems/615aa3d7-fd52-4af8-adc1-f996ed7395f7
-- title:
--   The set $\Omega_0$, the weight $w_0$ and the Schur terms $\xi_\pm$
-- statement:
--   With $a(g)$, $b(g)$, $C(g)$ the pinching blocks, let
--   $$\Omega_0=\{g\in\mathbb R^n:\ |a(g)|<1,\ \|C(g)\|_{\mathrm{op}}<1\},$$
--   $$w_0(g)=(1-a(g)^2)^4\,\det(I_{d-1}-C(g)^2)^4\,\mathbf 1_{\Omega_0}(g),$$
--   and, for $g\in\Omega_0$,
--   $$\xi_+(g)=\frac{b(g)^\top(I+C(g))^{-1}b(g)}{1+a(g)},\qquad \xi_-(g)=\frac{b(g)^\top(I-C(g))^{-1}b(g)}{1-a(g)}.$$
--   The weight $w_0$ defines the tilted Gaussian measure $d\mu_0=(w_0/\mathbb E w_0)\,d\gamma_n$ of Theorem B.2, and $\xi_\pm$ are the Schur-complement terms produced by the off-diagonal block.
--
--   **Formalization Note** $\|\cdot\|_{\mathrm{op}}$ is the spectral norm. Off $\Omega_0$ the inverse and the divisions in $\xi_\pm$ return Lean's default values; they are never used, since $w_0=0$ there.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem B.2, pp.17–18 (PDF pp.19–20), eq. (B.14)

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_MatrixSpencer_Supplement_pinMat
open RBMSensitivity (E)
open Matrix
open scoped Matrix.Norms.L2Operator

namespace MatrixSpencer.Supplement

/-- **The set `Ω₀`, the weight `w₀` and the Schur terms `ξ±` of Theorem B.2.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…),
Theorem B.2, pp.17–18 (PDF pp.19–20): "the set Ω₀ = {g : |a(g)| < 1, ‖C(g)‖_op < 1}".

**Formalization Note.** `‖·‖` is the operator (spectral) norm (`Matrix.Norms.L2Operator`). -/
def Omega0 {n m : ℕ} (A : Fin n → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Set (E n) :=
  {g | |pinA A Q g| < 1 ∧ ‖pinC A Q g‖ < 1}

/-- The weight of the tilted Gaussian measure `µ₀` (Theorem B.2, p.17):
"w₀(g) = (1 − a(g)²)⁴ det(I_{d−1} − C(g)²)⁴ 1_{Ω₀}(g)". It vanishes off `Ω₀`. -/
noncomputable def w0 {n m : ℕ} (A : Fin n → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (g : E n) : ℝ :=
  open Classical in
  if g ∈ Omega0 A Q then (1 - pinA A Q g ^ 2) ^ 4 * (1 - pinC A Q g ^ 2).det ^ 4 else 0

/-- `ξ₊(g) = b(g)^⊤(I + C(g))⁻¹b(g) / (1 + a(g))`, eq. (B.14), p.18.

**Formalization Note.** The page defines it for `g ∈ Ω₀` only, where `I + C(g)` is invertible and
`1 + a(g) > 0`. Off `Ω₀` Lean's matrix inverse and division return junk values; they are never
read, because they are multiplied by `w₀ = 0` there. -/
noncomputable def xiPlus {n m : ℕ} (A : Fin n → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (g : E n) : ℝ :=
  (pinB A Q g ⬝ᵥ ((1 + pinC A Q g)⁻¹ *ᵥ pinB A Q g)) / (1 + pinA A Q g)

/-- `ξ₋(g) = b(g)^⊤(I − C(g))⁻¹b(g) / (1 − a(g))`, eq. (B.14), p.18. Same convention off `Ω₀`
as `xiPlus`. -/
noncomputable def xiMinus {n m : ℕ} (A : Fin n → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (g : E n) : ℝ :=
  (pinB A Q g ⬝ᵥ ((1 - pinC A Q g)⁻¹ *ᵥ pinB A Q g)) / (1 - pinA A Q g)

end MatrixSpencer.Supplement


