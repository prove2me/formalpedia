-- Prove2me | Definitions.Def_RandomLPIPM_Supplement_condLaw
-- name    : RandomLPIPM_Supplement_condLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:51:41.601233+00:00
-- url     : https://prove2.me/theorems/32d3d887-4067-4c6b-afc4-d6ab813c3143
-- title:
--   The conditional law $\nu_x$, $d\nu_x/d\nu^0_x=J_x/\mathbb E_{\nu^0_x}J_x$
-- statement:
--   For $x\in M_\mu^\circ$ let $\nu_x$ be the probability measure on the fiber $F_x$ with density
--   $$\frac{d\nu_x}{d\nu^0_x}(W)=\frac{J_x(W)}{\mathbb E_{\nu^0_x}J_x},\qquad J_x(W)=\det(V^\top D_xV),$$
--   with respect to the reference law $\nu^0_x$, where $V$ is any orthonormal basis matrix of $W$ and $D_x=\mu X^{-2}$.
--
--   By Theorem 7.7, $(\nu_x)$ is the regular conditional distribution of the kernel of a Gaussian constraint matrix given its central point.
--
--   **Formalization Note** A measure on projector matrices, as for $\nu^0_x$. Since $D_x$ is positive definite, $J_x\ge0$; at points of $M_\mu^\circ$ the normaliser $\mathbb E_{\nu^0_x}J_x$ is finite and positive, so $\nu_x$ is a probability measure.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 7.7, (104), p.65

import Mathlib
import Definitions.Def_RandomLPIPM_Supplement_tilt
import Definitions.Def_RandomLPIPM_Supplement_refFiberLaw

open MeasureTheory

namespace RandomLPIPM.Supplement

/-- **The conditional law `ν_x` of the kernel.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 7.7 and (104), p.65: "Let `ν_x` be the
probability measure on `F_x` with `dν_x/dν⁰_x (W) = J_x(W)/E_{ν⁰_x} J_x`, `J_x(W) = det(VᵀD_xV)`".

`condLaw n k μ x` is the reference fiber law `ν⁰_x` (`refFiberLaw`) reweighted by the tilt
`J_x` (`tilt`) and normalised by its `ν⁰_x`-expectation.

**Formalization Note.** A measure on projector matrices (see `refFiberLaw`). `J_x ≥ 0` on
projectors (`D_x` is positive definite), so `ENNReal.ofReal` loses nothing; for `x ∈ M°_μ` the
normaliser `E_{ν⁰_x} J_x` is finite and positive (`J_x` is continuous and positive on the compact
fiber), so `ν_x` is a probability measure on `F_x`. -/
noncomputable def condLaw (n k : ℕ) (μ : ℝ) (x : Fin n → ℝ) : Measure (Fin n → Fin n → ℝ) :=
  (refFiberLaw n k μ x).withDensity fun P =>
    ENNReal.ofReal (tilt μ x P) / ∫⁻ P', ENNReal.ofReal (tilt μ x P') ∂refFiberLaw n k μ x

end RandomLPIPM.Supplement


