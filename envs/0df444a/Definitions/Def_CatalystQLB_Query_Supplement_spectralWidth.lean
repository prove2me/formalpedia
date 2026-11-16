-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_spectralWidth
-- name    : CatalystQLB_Query_Supplement_spectralWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:00:24.102278+00:00
-- url     : https://prove2.me/theorems/a7699bcc-5b2f-4e6d-b0bd-9abd61c64457
-- title:
--   Spectral width $L(H)=\lambda_{\max}(H)-\lambda_{\min}(H)$
-- statement:
--   For a Hermitian operator $H$, the **spectral width** is the difference between its largest and smallest eigenvalues:
--   $$L(H) := \lambda_{\max}(H)-\lambda_{\min}(H)\ \ge 0 .$$
--   For the catalyst Hamiltonian $H_C=\sum_{i=1}^{\ell}\Delta|1\rangle\langle1|_{C_i}$ of Appendix C, $L(H_C)=\ell\Delta$.
--
--   **Formalization Note** The maximum and minimum of Mathlib's eigenvalue list of the Hermitian matrix (with multiplicity), over the finite nonempty basis index type. It is not the operator norm.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Appendix C.3, p.96 (PDF 99)

import Mathlib

open scoped Matrix

namespace CatalystQLB.Query.Supplement

/-- The **spectral width** `L(H) := λ_max(H) − λ_min(H)` of a Hermitian operator (Arora,
Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of
Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Appendix C.3, p.96 (PDF 99)).

**Formalization Note** `hH.eigenvalues` lists the (real) eigenvalues of `H` with multiplicity;
`⨆`/`⨅` over the finite nonempty index type are their maximum and minimum (for the catalyst
register `Qubits ℓ` is never empty). It is not `‖H‖`. -/
noncomputable def spectralWidth {m : Type} [Fintype m] [DecidableEq m] (H : Matrix m m ℂ)
    (hH : H.IsHermitian) : ℝ :=
  (⨆ i, hH.eigenvalues i) - ⨅ i, hH.eigenvalues i

end CatalystQLB.Query.Supplement


