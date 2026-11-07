-- Prove2me | Definitions.Def_SYKCavity_Bop
-- name    : SYKCavity_Bop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:34.691306+00:00
-- url     : https://prove2.me/theorems/0fed4497-0d2e-4547-84e9-25023d5b452c
-- title:
--   The real-time two-point operators $B(t)$ and their Hermitian combinations
-- statement:
--   For a real time $t$ and Section 3's Hamiltonian $H$,
--   $$B(t)=\frac1{2N}\sum_{i=1}^Ne^{-it\beta H}\psi_ie^{it\beta H}\psi_i-G_*(it)\,I,\qquad(5.1)$$
--   where $G_*(it)$ is the continuation of the saddle's positive-time branch, $G_*(z)=\int\frac{\cosh(x(1/2-z))}{2\cosh(x/2)}\mu_{*,\beta}(dx)$. For finitely many real times $t_l$ and complex coefficients $c_l$,
--   $$B=\sum_l\bigl(c_lB(t_l)+\bar c_l\,B(t_l)^\dagger\bigr)$$
--   is Hermitian, and every Hermitian linear combination of the $B(t_l)$ and their adjoints has this form.
--
--   These operators measure the deviation of the empirical two-point function from the saddle $G_*$; Theorem 9 bounds their thermal moments.
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (5.1), p.31

import Mathlib
import Definitions.Def_SYKCavity_Majorana
import Definitions.Def_SYKCavity_Saddle

namespace SYKCavity

/-!
# The real-time two-point operators `B(t)` of Theorem 9

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5): (5.1), p.31.

**Formalization Note.**
* `Bop β N J t = (1/(2N)) Σ_i e^{−itβH} ψ_i e^{itβH} ψ_i − G*(it) I` for a real time `t`, with Section
  3's Hamiltonian `H` (`Hgamma`), complex matrix exponentials, and `G*(it) = GstarC β (i t)`, the
  continuation of the saddle's positive-time branch (D.1) to `z = it`.
* `Bcomb β N J t c = Σ_l (c_l B(t_l) + c̄_l B(t_l)†)` for finitely many real times `t_l` and complex
  coefficients `c_l`. Every Hermitian linear combination of the `B(t_l)` and their adjoints has this
  form (`B = (B + B†)/2`), and every such sum is Hermitian.
-/

/-- `B(t) = (1/(2N)) Σ_i e^{−itβH} ψ_i e^{itβH} ψ_i − G*(it) I`, (5.1). -/
noncomputable def Bop (β : ℝ) (N : ℕ) (J : Quad N → ℝ) (t : ℝ) : MOp N :=
  ((2 * N : ℂ)⁻¹) • ∑ i : Fin N,
      NormedSpace.exp ((-(Complex.I * (t * β : ℝ))) • Hgamma N J) * psi N i *
        NormedSpace.exp ((Complex.I * (t * β : ℝ)) • Hgamma N J) * psi N i -
    GstarC β (Complex.I * t) • (1 : MOp N)

/-- The Hermitian combination `Σ_l (c_l B(t_l) + c̄_l B(t_l)†)`. -/
noncomputable def Bcomb (β : ℝ) (N : ℕ) (J : Quad N → ℝ) {L : ℕ} (t : Fin L → ℝ) (c : Fin L → ℂ) :
    MOp N :=
  ∑ l, (c l • Bop β N J (t l) + (starRingEnd ℂ (c l)) • (Bop β N J (t l)).conjTranspose)

end SYKCavity


