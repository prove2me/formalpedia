-- Prove2me | Definitions.Def_PsdPermanent_logProductPotential
-- name    : PsdPermanent_logProductPotential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:48.030824+00:00
-- url     : https://prove2.me/theorems/962c5d7b-1844-4e2f-a9be-98debf25cb09
-- title:
--   The potential $U(z)=\sum_i\log|v_i^\dagger z|^2$
-- statement:
--   For $V\in\mathbb C^{n\times d}$ with rows $v_i^\dagger$, the potential of the permanent is
--   $$U(z)=\sum_{i=1}^n\log|v_i^\dagger z|^2,$$
--   with values in $\mathbb R\cup\{-\infty\}$; it is $-\infty$ exactly where some $v_i^\dagger z$ vanishes.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), proof of Theorem 7, p.7

import Mathlib
open Matrix

namespace PsdPermanent

/-- **The potential U of the permanent.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), proof of Theorem 7, p.7: "U(z) = ∑_{i=1}^n log|v_i† z|²".

**Formalization Note.** `v_i†z = (V *ᵥ z) i`, §3's rows. `EReal`-valued, with value `⊥` exactly on the union of
the hyperplanes `v_i†z = 0`: this is the paper's `U : C^d → R ∪ {−∞}`, with `ENNReal.log 0 = ⊥`, and not a
junk `Real.log 0 = 0`. -/
noncomputable def logProductPotential {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) (z : Fin d → ℂ) : EReal :=
  ∑ i, ENNReal.log (ENNReal.ofReal (Complex.normSq ((V *ᵥ z) i)))

end PsdPermanent


