-- Prove2me | Definitions.Def_JencovaRenyi_renyiDiv
-- name    : JencovaRenyi_renyiDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:33.722831+00:00
-- url     : https://prove2.me/theorems/ce8a914c-36ee-4a62-9cec-82948feb9032
-- title:
--   The sandwiched Rényi relative entropy $\tilde D_\alpha(\psi\|\varphi)$ for normal states
-- statement:
--   For $1<\alpha<\infty$ and normal states $\psi,\varphi$ on $\mathcal M$,
--   $$
--   \tilde D_\alpha(\psi\|\varphi) = \begin{cases} \dfrac{\alpha}{\alpha-1}\log\|h_\psi\|_{\alpha,\varphi} & \text{if } h_\psi\in L_\alpha(\mathcal M,\varphi),\\ \infty & \text{otherwise.}\end{cases}
--   $$
--   On finite-dimensional algebras this is the sandwiched Rényi relative entropy $\frac{1}{\alpha-1}\log\operatorname{Tr}[(\sigma^{\frac{1-\alpha}{2\alpha}}\rho\,\sigma^{\frac{1-\alpha}{2\alpha}})^\alpha]$ (Proposition 3.1).
--
--   **Formalization Note** Valued in `EReal` with the natural logarithm `ENNReal.log`. Since `ENNReal.log ⊤ = ⊤` and $\alpha/(\alpha-1)>0$, the value is $\infty$ exactly when $\|h_\psi\|_{\alpha,\varphi} = \infty$, i.e. $h_\psi\notin L_\alpha(\mathcal M,\varphi)$, as in (11).
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §3.1, (11), p.10

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual
import Definitions.Def_JencovaRenyi_lpNorm

open scoped ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sandwiched Rényi relative entropy (11) of Jenčová, arXiv:1609.08462v4, §3.1, p.10: for
`1 < α < ∞` and normal states `ψ, φ`,
`D̃_α(ψ‖φ) = α/(α−1) · log ‖h_ψ‖_{α,φ}` if `h_ψ ∈ L_α(M, φ)`, and `∞` otherwise.

**Formalization Note.** Valued in `EReal`, with the natural logarithm `ENNReal.log`. Since
`ENNReal.log ⊤ = ⊤` and the prefactor `α/(α−1)` is positive for `α > 1`, the value is `⊤`
exactly when `‖h_ψ‖_{α,φ} = ⊤`, i.e. `h_ψ ∉ L_α(M, φ)`, as in (11). -/
noncomputable def renyiDiv {A : StarSubalgebra ℂ (H →L[ℂ] H)} (S : StandardForm A) (α : ℝ)
    (ψ φ : Predual A) : EReal :=
  ((α / (α - 1) : ℝ) : EReal) * ENNReal.log (lpNorm S φ (ENNReal.ofReal α) ψ)

end JencovaRenyi


