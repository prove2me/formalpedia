-- Prove2me | Definitions.Def_LiqPremiaEq_IsRiccatiSolOn
-- name    : LiqPremiaEq_IsRiccatiSolOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:58.514328+00:00
-- url     : https://prove2.me/theorems/1eac286d-4bf9-49dd-8d8f-c60edd14b4ce
-- title:
--   Solutions of the matrix Riccati system (4.8) on an interval
-- statement:
--   Fix $\gamma$, a symmetric positive definite cost matrix $\Lambda\in\mathbb R^{K\times K}$, $\alpha\in\mathbb R^{K\times D}$ and loadings $\xi\in\mathbb R^{(N-1)D\times D}$. Write
--
--   $$\sigma_H=\alpha+(c\otimes I_K)^\top H\in\mathbb R^{K\times D}.$$
--
--   A pair $F:\mathbb R\to\mathbb R^{K(N-1)\times K(N-1)}$, $H:\mathbb R\to\mathbb R^{K(N-1)\times D}$ **solves the Riccati system (4.8)** on a set $I\ni 0$ if $F(0)=0$, $H(0)=0$ and at every $\tau\in I$ (derivatives within $I$)
--
--   $$F'=\Gamma\otimes\sigma_H\sigma_H^\top-F\,(I_{N-1}\otimes\Lambda^{-1})\,F,\qquad H'=(\Gamma\otimes\sigma_H)\,\xi-F\,(I_{N-1}\otimes\Lambda^{-1})\,H.$$
--
--   The equilibrium of Theorem 4.5 is written explicitly in terms of $F$ and $H$; Lemma 4.4 is the global solvability of this system.
--
--   **Formalization Note** The set $I$ is $[0,T]$ in Lemma 4.4 and Theorem 4.5, and an initial interval $[0,T')$ in Corollaries 7.7, 7.8 and (7.13), where the paper uses the maximal interval of existence. $\sigma_H$ is `sigmaH`; the right-hand sides are `riccatiRhsF`, `riccatiRhsH`.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, eq. (4.8), p.8

import Mathlib
import Definitions.Def_LiqPremiaEq_Gam
import Definitions.Def_LiqPremiaEq_colKron
import Definitions.Def_LiqPremiaEq_IsLinMatODESol

open Matrix
open scoped Kronecker

namespace LiqPremiaEq

/-- The volatility matrix attached to `H`, `α + (c ⊗ I_K)ᵀ H ∈ ℝ^{K×D}`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.8), p.8 (and (7.20), p.22). -/
noncomputable def sigmaH {M K D : ℕ} (γ : Fin (M + 1) → ℝ) (α : Matrix (Fin K) (Fin D) ℝ)
    (H : Matrix (Fin M × Fin K) (Fin D) ℝ) : Matrix (Fin K) (Fin D) ℝ :=
  α + (colKron (cvec γ) (1 : Matrix (Fin K) (Fin K) ℝ))ᵀ * H

/-- The right-hand side of the `F`-equation of (4.8):
`Γ ⊗ (α + (c ⊗ I_K)ᵀH)(α + (c ⊗ I_K)ᵀH)ᵀ − F (I_{N−1} ⊗ Λ⁻¹) F`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.8), p.8. -/
noncomputable def riccatiRhsF {M K D : ℕ} (γ : Fin (M + 1) → ℝ) (Λ : Matrix (Fin K) (Fin K) ℝ)
    (α : Matrix (Fin K) (Fin D) ℝ) (F : Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ)
    (H : Matrix (Fin M × Fin K) (Fin D) ℝ) : Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ :=
  Gam γ ⊗ₖ (sigmaH γ α H * (sigmaH γ α H)ᵀ)
    - F * ((1 : Matrix (Fin M) (Fin M) ℝ) ⊗ₖ Λ⁻¹) * F

/-- The right-hand side of the `H`-equation of (4.8):
`(Γ ⊗ (α + (c ⊗ I_K)ᵀH)) ξ − F (I_{N−1} ⊗ Λ⁻¹) H`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.8), p.8.

**Formalization Note** `Γ ⊗ (α + (c ⊗ I_K)ᵀH)` has rows `Fin M × Fin K` and columns
`Fin M × Fin D`; it multiplies the stacked `ξ ∈ ℝ^{(N−1)D×D}` (`stackMat`). -/
noncomputable def riccatiRhsH {M K D : ℕ} (γ : Fin (M + 1) → ℝ) (Λ : Matrix (Fin K) (Fin K) ℝ)
    (α : Matrix (Fin K) (Fin D) ℝ) (ξ : Fin M → Matrix (Fin D) (Fin D) ℝ)
    (F : Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ) (H : Matrix (Fin M × Fin K) (Fin D) ℝ) :
    Matrix (Fin M × Fin K) (Fin D) ℝ :=
  (Gam γ ⊗ₖ sigmaH γ α H) * stackMat ξ - F * ((1 : Matrix (Fin M) (Fin M) ℝ) ⊗ₖ Λ⁻¹) * H

/-- `(F, H)` solves the matrix Riccati system (4.8) on the set `I ∋ 0`:
`F(0) = 0`, `H(0) = 0`, and at every `τ ∈ I`
`F′(τ) = Γ ⊗ (α + (c ⊗ I_K)ᵀH)(α + (c ⊗ I_K)ᵀH)ᵀ − F (I_{N−1} ⊗ Λ⁻¹) F`,
`H′(τ) = (Γ ⊗ (α + (c ⊗ I_K)ᵀH)) ξ − F (I_{N−1} ⊗ Λ⁻¹) H`,
with derivatives taken within `I`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.8), p.8.

**Formalization Note** Used with `I = [0, T]` (Lemma 4.4, Theorem 4.5) and `I = [0, T′)`
(Corollaries 7.7, 7.8 and (7.13), where the paper uses the maximal interval `[0, T_max)`). -/
def IsRiccatiSolOn {M K D : ℕ} (γ : Fin (M + 1) → ℝ) (Λ : Matrix (Fin K) (Fin K) ℝ)
    (α : Matrix (Fin K) (Fin D) ℝ) (ξ : Fin M → Matrix (Fin D) (Fin D) ℝ) (I : Set ℝ)
    (F : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ)
    (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ) : Prop :=
  F 0 = 0 ∧ H 0 = 0 ∧
    ∀ τ ∈ I, HasMatDerivWithinAt F (riccatiRhsF γ Λ α (F τ) (H τ)) I τ ∧
      HasMatDerivWithinAt H (riccatiRhsH γ Λ α ξ (F τ) (H τ)) I τ

end LiqPremiaEq


