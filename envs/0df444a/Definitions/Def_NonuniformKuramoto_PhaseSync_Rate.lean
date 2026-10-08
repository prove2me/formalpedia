-- Prove2me | Definitions.Def_NonuniformKuramoto_PhaseSync_Rate
-- name    : NonuniformKuramoto_PhaseSync_Rate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:03.686923+00:00
-- url     : https://prove2.me/theorems/d349a627-db05-4576-9bc3-4a71e0ce118b
-- title:
--   Laplacian L(a_ij), Euclidean norm, cos ∠(D1, 1), D_max, D_min and the phase-synchronization rate λ_ps (42)
-- statement:
--   For a nonnegative weight array $(a_{ij})$ on $n$ nodes, the **Laplacian** is the $n\times n$ matrix
--
--   $$L(a_{ij}) = \mathrm{diag}\Big(\sum_{j=1}^n a_{ij}\Big) - A .$$
--
--   For damping coefficients $D_1,\dots,D_n > 0$ write $D\mathbf 1 = (D_1,\dots,D_n)$ and $\mathbf 1 = (1,\dots,1)$, so that the cosine of the angle between them is
--
--   $$\cos\angle(D\mathbf 1,\mathbf 1) = \frac{\sum_i D_i}{\sqrt n\,\sqrt{\sum_i D_i^2}} ,$$
--
--   and let $D_{\max} = \max_i D_i$, $D_{\min} = \min_i D_i$. The Euclidean norm of $x \in \mathbb R^n$ is $\|x\|_2 = (\sum_i x_i^2)^{1/2}$. Finally, with $\lambda_2(L(P_{ij}))$ the second-smallest eigenvalue (the algebraic connectivity) of the Laplacian of a symmetric coupling matrix $P$ and $\mathrm{sinc}(x) = \sin(x)/x$, the **phase-synchronization rate** is
--
--   $$\lambda_{\mathrm{ps}} = \lambda_2(L(P_{ij}))\,\mathrm{sinc}(\gamma)\,\cos(\angle(D\mathbf 1,\mathbf 1))^2 / D_{\max} .$$
--
--   These quantities enter the rate statement of Theorem V.10 2) and the consensus form (44) of the phase dynamics.
--
--   **Formalization Note** The paper prints (42) with a leading minus sign; the proof pattern it refers to (Theorem V.1, p. 19) uses the rate as a positive decay exponent, so the rate is defined as the positive number above. $\lambda_2$ is the referenced platform definition `AlonMilman.PropertyT.lambda1` (second-smallest eigenvalue, with multiplicity, of a real symmetric matrix; value $0$ off symmetric matrices or for fewer than two nodes). $\|\cdot\|_2$ is written out because Mathlib's default norm on $\mathbb R^n$ as a function space is the sup norm. $D_{\max}$, $D_{\min}$ are an indexed supremum and infimum over the finite index set and are used only with $n \ge 2$. `Real.sinc` has $\mathrm{sinc}(0) = 1$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 4 (notation, Laplacian, angle ∠(x, y)), p. 5 (λ₂, sinc), p. 27, (42)

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_lambda1
import Definitions.Def_NonuniformKuramoto_CondII_Constants
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.PhaseSync

/-- `D_min = minᵢ Dᵢ` (p. 4). Used only with `2 ≤ n`, where the index set is nonempty. -/
noncomputable def Dmin {n : ℕ} (D : Fin n → ℝ) : ℝ := ⨅ i, D i

/-- The phase-synchronization rate (42) (p. 27), taken as the positive number
`λ_ps = λ₂(L(Pᵢⱼ)) · sinc(γ) · cos(∠(D𝟏, 𝟏))² / D_max`; the page prints it with a leading minus
sign, which is a slip (the proof uses it as a decay rate). `λ₂` is the second-smallest eigenvalue
of the symmetric matrix `L(Pᵢⱼ)` (`AlonMilman.PropertyT.lambda1`). -/
noncomputable def lambdaPS {n : ℕ} (D : Fin n → ℝ) (P : Fin n → Fin n → ℝ) (γ : ℝ) : ℝ :=
  AlonMilman.PropertyT.lambda1 (NonuniformKuramoto.CondI.lap P) * Real.sinc γ * NonuniformKuramoto.CondI.cosAngleD D ^ 2 / NonuniformKuramoto.CondII.Dmax D

end NonuniformKuramoto.PhaseSync


