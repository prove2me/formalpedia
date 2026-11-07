-- Prove2me | Definitions.Def_SpectrumLB_jmPowSumCirc
-- name    : SpectrumLB_jmPowSumCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:25.451361+00:00
-- url     : https://prove2.me/theorems/6c0df2bd-babd-463e-82a7-91a091d3de11
-- title:
--   Power sum without identity terms, $\mathcal P^{\circ}_m=\mathcal P_m-\eta_m\mathbf 1$
-- statement:
--   Let $\eta_m$ be the component of $\mathcal P_m$ on the identity permutation, $\eta_m=A_{m,\varnothing}/d^m$. The power sum with its identity terms removed is
--
--   $$
--   \mathcal P^{\circ}_m=\mathcal P_m-\eta_m\,\mathbf 1 .
--   $$
--
--   Removing the scalar part isolates the fluctuating part of $\mathcal P_m$, whose second moment under the average state is small (Lemma 6.3).
--
--   **Formalization Note** $\eta_m$ is read off the group-algebra element $\sum_t J_t^m$, because for $n>d$ the operator $\mathcal P_m$ does not determine its permutation coefficients.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §6, p. 24

import Mathlib
import Definitions.Def_SpectrumLB_jmPowSum
import Definitions.Def_SpectrumLB_jmCoeff

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Power sum with identity terms removed, `𝒫°_m = 𝒫_m − η_m 1`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, §6, p. 24: "let 𝒫°_j := 𝒫_j − η_j 1, where η_j is the component of 𝒫_j associated with the identity
permutation, i.e., we have removed all identity terms from 𝒫_j".

`jmPowSumCirc d n m = 𝒫_m − (A_{m,∅} / d^m) · 1`, where `A_{m,∅} = jmCoeff n m 1`.

**Formalization Note.** `η_m = A_{m,∅}/d^m` is the identity coefficient of `𝒫_m = d^{−m} Σ_t J_t^m` read in
the group algebra (reading R7). -/
noncomputable def jmPowSumCirc (d n m : ℕ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  jmPowSum d n m - ((jmCoeff n m 1 : ℂ) / (d : ℂ) ^ m) • (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)

end SpectrumLB


