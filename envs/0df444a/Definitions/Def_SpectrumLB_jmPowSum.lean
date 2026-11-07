-- Prove2me | Definitions.Def_SpectrumLB_jmPowSum
-- name    : SpectrumLB_jmPowSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:25.556197+00:00
-- url     : https://prove2.me/theorems/2fb17efa-2903-44b9-97fc-8f8e6846406c
-- title:
--   Jucys–Murphy power sum $\mathcal P_m=\sum_t\widetilde J_t^{\,m}$, Eq. (2.10)
-- statement:
--   The $m$-th Jucys–Murphy power sum is
--
--   $$
--   \mathcal P_m=\sum_{t=1}^n\widetilde J_t^{\,m},\qquad\widetilde J_t=\tfrac1d J_t ,
--   $$
--
--   an operator on $(\mathbb C^d)^{\otimes n}$. Since $\log f_b/f_a$ is a power series whose first nonzero term has degree $k$ (Proposition 5.3), the log-likelihood ratio of the two hard ensembles is controlled by the power sums $\mathcal P_m$, $m\ge k$ (Lemmas 6.3, 6.4).
--
--   **Formalization Note** At $d=0$ the scalar $1/d$ is $0$ in Lean; the tensor space is then zero for $n\ge1$, so nothing changes.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §2.1, Eq. (2.10), p. 13

import Mathlib
import Definitions.Def_SpectrumLB_jm

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Jucys–Murphy power sum `𝒫_m`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §2.1, Eq. (2.10), p. 13: "𝒫_k := Σ_{i∈[n]} J̃_i^k", with `J̃_t = (1/d) J_t` ((2.7)).

`jmPowSum d n m = Σ_{t} (d⁻¹ J_t)^m` on `(ℂ^d)^{⊗n}`.

**Formalization Note.** At `d = 0` the scalar `d⁻¹` is `0` in Lean; the space `(ℂ^0)^{⊗n}` is then zero
for `n ≥ 1`, so no instance changes. -/
noncomputable def jmPowSum (d n m : ℕ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ t : Fin n, ((d : ℂ)⁻¹ • jm d t) ^ m

end SpectrumLB


