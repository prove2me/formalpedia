-- Prove2me | Definitions.Def_PinningSyncAudit_GeneralCoupling_correctedMatrix
-- name    : PinningSyncAudit_GeneralCoupling_correctedMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:50:47.082991+00:00
-- url     : https://prove2.me/theorems/93b81d23-b43e-43ff-82e7-f61c3d23543a
-- title:
--   Corrected matrix test for general inner coupling
-- statement:
--   Let $N,n\ge1$, let $G\in\mathbb R^{N\times N}$ and $K,\Gamma\in\mathbb R^{n\times n}$, let $c\in\mathbb R$, and let $\xi,d\in\mathbb R^N$. Write $\Xi=\operatorname{diag}(\xi)$ and $D=\operatorname{diag}(d)$. The corrected matrix is
--
--   $$
--   M_*=\Xi\otimes\frac{K\Gamma+\Gamma^TK^T}{2}
--   +\frac c2\big[(\Xi G)\otimes\Gamma+(G^T\Xi)\otimes\Gamma^T\big]
--   -c(\Xi D)\otimes\frac{\Gamma+\Gamma^T}{2}.
--   $$
--
--   This is the full symmetric part of the matrix determined by the quadratic expression before the last equality in (3.4). It provides the matrix hypothesis of the corrected Theorem 3.1. It is not the paper's literal (3.2). If $M_0$ denotes that printed matrix and $\widehat G=(\Xi G+G^T\Xi)/2$, then the correction is $M_*-M_0=\frac c4(\Xi G-G^T\Xi)\otimes(\Gamma-\Gamma^T)$. The printed test is false for general $\Gamma$; the exact directed-cycle counterexample is recorded with the goal theorem and in the mission description.
--
--   **Formalization Note** Matrix rows and columns use pairs $(i,a)\in\operatorname{Fin}(N)\times\operatorname{Fin}(n)$, with $(A\otimes B)_{(i,a),(j,b)}=A_{ij}B_{ab}$. This definition is a total finite matrix formula, also meaningful in zero dimensions; positivity, connectivity and gain constraints are hypotheses of the theorem, not part of the definition. No stability or convergence claim is included in the definition.
-- source:
--   Yu, Chen, Lü and Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51(2) (2013), 1395–1416, https://doi.org/10.1137/100781699, p. 1402, Theorem 3.1, (3.2) corrected using the pre-symmetrization expression in (3.4) (PDF p. 8); model (2.2), (2.5)–(2.8), pp. 1397–1398 (PDF pp. 3–4)

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace PinningSyncAudit.GeneralCoupling

open Matrix Kronecker

/-- Theorem 3.1, p. 1402 (PDF 8), corrected test: symmetrize the entire
coupling product. This is M_*, not the printed (3.2). In particular it retains
`(c / 4) • ((ΞG - GᵀΞ) ⊗ₖ (Γ - Γᵀ))` omitted from that display. -/
noncomputable def correctedMatrix {N n : ℕ}
    (K Γ : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (ξ d : Fin N → ℝ) :
    Matrix (Fin N × Fin n) (Fin N × Fin n) ℝ :=
  diagonal ξ ⊗ₖ ((1 / 2 : ℝ) • (K * Γ + Γᵀ * Kᵀ))
    + (c / 2) • ((diagonal ξ * G) ⊗ₖ Γ + (Gᵀ * diagonal ξ) ⊗ₖ Γᵀ)
    - c • ((diagonal ξ * diagonal d) ⊗ₖ ((1 / 2 : ℝ) • (Γ + Γᵀ)))

end PinningSyncAudit.GeneralCoupling


