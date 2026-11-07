-- Prove2me | Definitions.Def_SpectrumLB_fAOp
-- name    : SpectrumLB_fAOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:39.479331+00:00
-- url     : https://prove2.me/theorems/d640c51e-a6f1-4345-8cc9-3fd987179e0d
-- title:
--   $f_a$ applied to an operator, $f_a(M)=\prod_i(1+a_iM)\,(1+M)^{-K}$
-- statement:
--   For positive integers $a_1,\dots,a_K$ and a square matrix $M$,
--
--   $$
--   f_a(M)=\Big(\prod_{i=1}^K(\mathbf 1+a_iM)\Big)(\mathbf 1+M)^{-K}.
--   $$
--
--   This is the operator meaning of $f_a(\widetilde J_t)$ in Proposition 3.5; all factors are functions of the single operator $M$ and commute.
--
--   **Formalization Note** The inverse is Mathlib's matrix inverse. At $M=\widetilde J_t$ it is a true inverse, because $\mathbf 1+\widetilde J_t=\frac1d(d+J_t)$ is invertible (Proposition 3.2).
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Proposition 3.5, Eq. (3.11), p. 14

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **`f_a` applied to an operator: `f_a(M) = ∏_i (1 + a_i M) · (1 + M)^{−K}`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Proposition 3.5, Eq. (3.11), p. 14 ("E[X^{⊗n}] = ν_a^n · ∏_{t=1}^n f_a(J̃_t)").

**Formalization Note.** The factors `1 + a_i M` and `(1 + M)⁻¹` are polynomials/inverses in one operator and
commute. `⁻¹` is Mathlib's matrix inverse; at `M = J̃_t` it is a true inverse because `1 + J̃_t = d⁻¹(d + J_t)`
is invertible (Proposition 3.2). -/
noncomputable def fAOp {K : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (a : Fin K → ℕ)
    (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (List.ofFn fun i : Fin K => (1 + (a i : ℂ) • M)).prod * ((1 + M)⁻¹) ^ K

end SpectrumLB


