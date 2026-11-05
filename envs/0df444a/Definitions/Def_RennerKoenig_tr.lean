-- Prove2me | Definitions.Def_RennerKoenig_tr
-- name    : RennerKoenig_tr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:48.286195+00:00
-- url     : https://prove2.me/theorems/cd36fa51-cdff-44e6-a490-dbedbef2efff
-- title:
--   The trace $\operatorname{tr} T$
-- statement:
--   The trace of an operator $T$ on a complex Hilbert space $K$ is
--
--   $$
--   \operatorname{tr}T=\sum_i\langle b_i,T\,b_i\rangle
--   $$
--
--   for a Hilbert basis $(b_i)_i$ of $K$. All the paper's quantities are traces of trace-class operators.
--
--   **Formalization Note** This is the published `operatorTrace` in the basis `chosenBasis K`. On trace-class operators the series converges absolutely and does not depend on the basis.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.2, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_RennerKoenig_chosenBasis

open QAlgorithms.Papers.Independent.Dependency50.P13

namespace RennerKoenig

/-- **The trace** `tr T = ∑ᵢ ⟨bᵢ, T bᵢ⟩`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.2, p.3.

**Formalization Note** The published `operatorTrace` in `chosenBasis K`. It is used only on
trace-class operators, where the series is absolutely summable and independent of the basis. -/
noncomputable def tr {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (T : K →L[ℂ] K) : ℂ :=
  operatorTrace (chosenBasis K) T

end RennerKoenig


