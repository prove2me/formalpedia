-- Prove2me | Definitions.Def_MatrixSpencer_series
-- name    : MatrixSpencer_series
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:07.96876+00:00
-- url     : https://prove2.me/theorems/03cddc3f-f0c1-4003-8c95-10afe1faed91
-- title:
--   The Gaussian matrix series $B(g)=\sum_i g_iM_i$
-- statement:
--   For matrices $M_1,\dots,M_n\in\mathbb R^{d\times d}$ and $g\in\mathbb R^n$, the matrix series
--   $$B(g)=\sum_{i=1}^n g_iM_i .$$
--   Under $g\sim\gamma_n$ it is a centered Gaussian matrix with matrix variance $\mathbb E B^2=\sum_i M_i^2$.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.1, p.6; §2.2, p.8

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace MatrixSpencer

/-- **The Gaussian matrix series `B(g) = ∑ᵢ gᵢMᵢ`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8: "Let B = ∑ⁿᵢ₌₁ gᵢMᵢ"; §2.1, p.6: "For a Gaussian matrix series X = ∑ⁿᵢ₌₁ gᵢAᵢ". -/
def series {n d : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℝ) (g : E n) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, g i • M i

end MatrixSpencer


