-- Prove2me | Definitions.Def_MatrixSpencer_curvature
-- name    : MatrixSpencer_curvature
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:14.415891+00:00
-- url     : https://prove2.me/theorems/ba8f3100-87d0-4b98-9560-5386ae8d4a5c
-- title:
--   The matrix curvature $\Theta_{ij}(W)$
-- statement:
--   For a positive definite matrix weight $W$, the matrix curvature
--   $$\Theta_{ij}(W)=(\partial_iW)W^{-1}(\partial_jW)-\partial_{ij}W .$$
--   For a scalar weight $W=e^{-\phi}$ it equals $W\,\partial_{ij}\phi$, so a lower bound on it generalizes a lower bound on the Hessian of the potential.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.1, p.7; Lemma A.1, p.13

import Mathlib
import Definitions.Def_MatrixSpencer_pdM
open RBMSensitivity (E)

namespace MatrixSpencer

/-- **The matrix curvature `Θᵢⱼ(W) = (∂ᵢW)W⁻¹(∂ⱼW) − ∂ᵢⱼW`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.1, p.7, and Lemma A.1, p.13. -/
noncomputable def curvature {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (W : E n → Matrix ι ι ℝ) (i j : Fin n) (x : E n) : Matrix ι ι ℝ :=
  pdM i W x * (W x)⁻¹ * pdM j W x - pdM i (pdM j W) x

end MatrixSpencer


