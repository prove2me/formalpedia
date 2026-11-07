-- Prove2me | Definitions.Def_PsdPermanent_phi
-- name    : PsdPermanent_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:44.166252+00:00
-- url     : https://prove2.me/theorems/32a6e3e4-bc3c-4799-a62b-f516c33f5cc6
-- title:
--   The objective $\phi_V(X)$ of the relaxation, Eq. (4)
-- statement:
--   For $V\in\mathbb C^{n\times d}$ with rows $v_i^\dagger$ and a $d\times d$ matrix $X$, the objective of the relaxation is
--   $$\phi_V(X)=\sum_{i=1}^n\log(v_i^\dagger Xv_i)+\log\det X-\operatorname{tr}X+d .$$
--   The sum is the product-of-linear-forms term; $\log\det X-\operatorname{tr}X+d$ is the entropy correction.
--
--   **Formalization Note** The three quantities $v_i^\dagger Xv_i$, $\det X$, $\operatorname{tr}X$ are positive reals for positive definite $X$ and nonzero rows, and Lean takes real parts. A zero row gives $\log 0$, which Lean reads as $0$, so statements about $\phi_V$ keep the nonzero-row hypothesis.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Eq. (4), p.5

import Mathlib
open Matrix

namespace PsdPermanent

/-- **The objective ϕ_V of the relaxation, Eq. (4).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Eq. (4), p.5:
ϕ_V(X) = ∑_{i=1}^n log(v_i† X v_i) + log det X − trX + d.

**Formalization Note.** `v_i†Xv_i = ((V * X * Vᴴ) i i).re` (§3's rows). For positive definite `X`
and nonzero rows all three of `(V * X * Vᴴ) i i`, `det X`, `trace X` are positive reals, so the real
parts lose nothing. `Real.log 0 = 0` makes a zero row contribute a junk `0`: every statement about
`phi` carries the paper's nonzero-row hypothesis. -/
noncomputable def phi {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, Real.log ((V * X * Vᴴ) i i).re + Real.log X.det.re - X.trace.re + d

end PsdPermanent


