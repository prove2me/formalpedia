-- Prove2me | Definitions.Def_DavidonVM_Termination_Delta
-- name    : DavidonVM_Termination_Delta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:11.365982+00:00
-- url     : https://prove2.me/theorems/5df9f1dd-4b76-42f6-85b3-a4f743b0a6cc
-- title:
--   The rank-one update (3) and the quantity Δ of (4)
-- statement:
--   For a real $n\times n$ matrix $H$, a coefficient $a\in\mathbb R$ and a vector $\nabla^{+}\in\mathbb R^n$ (the new gradient), the **rank-one update** (3) of the Appendix (p. 16) is
--   $$
--   H^{+}=H+a\,(H\nabla^{+})(H\nabla^{+})^{\mathsf T}.
--   $$
--
--   Given also the old gradient $\nabla$, put $S=-H\nabla$ (the step of (2)) and $D=\nabla^{+}-\nabla$ (the change of gradient). The quantity (4) that the coefficient $a$ is chosen to minimize is
--   $$
--   \Delta(a)=D^{\mathsf T}H^{+}D+S^{\mathsf T}(H^{+})^{-1}S-2\,S\cdot D .
--   $$
--   It vanishes when $S=H^{+}D$. Together with condition 1 on the determinant ratio, $\Delta$ determines $a$ through table (5).
--
--   **Formalization Note** $(H^{+})^{-1}$ is Mathlib's matrix inverse, which is the zero matrix when $H^{+}$ is singular; the statement that uses $\Delta$ (table (5)) only evaluates it at coefficients for which $\det H^{+}/\det H\ge R^{-1}>0$ with $H$ positive definite, so $H^{+}$ is invertible there. The paper writes $DH^{+}D$, $S(H^{+})^{-1}S$ without transposes.
-- source:
--   Davidon, Variable Metric Method for Minimization, SIAM J. Optim. 1(1) (1991), p. 16, Appendix (3) and (4)

import Mathlib
import Definitions.Def_DavidonVM_Termination_Method

namespace DavidonVM.Termination

open Matrix

/-- The rank-one update (3), p. 16, of `H` with coefficient `a` along `H ∇⁺`:
`H⁺ = H + a (H ∇⁺)(H ∇⁺)ᵀ`, where `gp = ∇⁺`. -/
def updateH {n : ℕ} (H : Mat n) (a : ℝ) (gp : Vec n) : Mat n :=
  H + a • vecMulVec (H *ᵥ gp) (H *ᵥ gp)

/-- Appendix (4), p. 16: `Δ = D H⁺ D + S (H⁺)⁻¹ S − 2 S · D` for one step from a point with
gradient `g = ∇`, new gradient `gp = ∇⁺`, step `S = −H∇`, gradient change `D = ∇⁺ − ∇` and
`H⁺ = updateH H a gp`. `(H⁺)⁻¹` is Mathlib's `Matrix.inv` (junk `0` if `H⁺` is singular). -/
noncomputable def Delta {n : ℕ} (H : Mat n) (a : ℝ) (gp g : Vec n) : ℝ :=
  (gp - g) ⬝ᵥ (updateH H a gp *ᵥ (gp - g))
    + (-(H *ᵥ g)) ⬝ᵥ ((updateH H a gp)⁻¹ *ᵥ (-(H *ᵥ g)))
    - 2 * ((-(H *ᵥ g)) ⬝ᵥ (gp - g))

end DavidonVM.Termination


