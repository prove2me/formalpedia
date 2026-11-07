-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_derivOp
-- name    : OptimalSpectrum_Entangled_derivOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:26.378983+00:00
-- url     : https://prove2.me/theorems/d9ddb426-6fa6-4cf0-a3ab-ba071b2cf446
-- title:
--   Derivative operator $D^{(r)}_p(H_1,\dots,H_r)$ of $A\mapsto\mathrm{tr}\,p(A)$ at $\sigma$
-- statement:
--   For a real polynomial $p$, a matrix $\sigma$ and Hermitian directions $H_1,\dots,H_r\in\mathbb C^{d\times d}$,
--
--   $$D^{(r)}_p(H_1,\dots,H_r)=\frac{\partial^r}{\partial t_1\cdots\partial t_r}\,\mathrm{tr}\Big(p\Big(\sigma+\sum_{j=1}^r t_jH_j\Big)\Big)\Big|_{t_1=\cdots=t_r=0}.$$
--
--   It is the coefficient of $t_1\cdots t_r$ in this polynomial, real and linear in each direction. The variance of the moment estimates is bounded through these derivatives (Lemma 7.3).
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.2, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_mixedPartial

namespace OptimalSpectrum.Entangled

/-- **Derivative operator `D_p^(r)` of `A ↦ tr p(A)` at `σ`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.2, printed p. 21 (PDF p. 23): "For 1 ⩽ r ⩽ k and Hermitian d × d matrices H₁, …, H_r,
define D_p^(r)(H₁, …, H_r) := ∂^r/∂t₁⋯∂t_r tr(p(σ + ∑_(j=1)^r t_j H_j))|_(t₁=⋯=t_r=0)."

**Formalization Note.** `p` is a real polynomial evaluated at a complex matrix (`Polynomial.aeval`);
the real part of the trace is taken, which is the trace itself on Hermitian arguments. The base point
`σ` is an argument. -/
noncomputable def derivOp {d : ℕ} (p : Polynomial ℝ) (σ : Matrix (Fin d) (Fin d) ℂ) (r : ℕ)
    (H : Fin r → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  mixedPartial r fun t => (Matrix.trace (Polynomial.aeval (σ + ∑ j, t j • H j) p)).re

end OptimalSpectrum.Entangled


