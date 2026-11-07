-- Prove2me | Definitions.Def_QPSpinParisi_En
-- name    : QPSpinParisi_En
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:06:27.434185+00:00
-- url     : https://prove2.me/theorems/3ffd2c02-6ac7-472a-a1fa-d7ead39d9105
-- title:
--   The maximal energy $E^\star_{n,\mathrm{prod}}$, (2.2)
-- statement:
--   The rescaled maximal energy over product states:
--   $$E^\star_{n,\mathrm{prod}}=\frac1{\sqrt n}\max_{|\phi\rangle\in S^n_{\mathrm{prod}}}\langle\phi|H_n|\phi\rangle.$$
--   This is the random variable whose limit Theorem 1 identifies.
--
--   **Formalization Note** The maximum is a real supremum of a nonempty compact set, and Lemma 3.1 records that it is attained.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.2), p.3 (PDF p.3)

import Mathlib
import Definitions.Def_QPSpinParisi_ham
import Definitions.Def_QPSpinParisi_ProdStates
import Definitions.Def_QPSpinParisi_energy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The rescaled maximal product-state energy `E⋆_{n,prod} = n^{-1/2} max_{|ϕ⟩ ∈ S^n_prod} ⟨ϕ|H_n|ϕ⟩`
(Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.2), p.3, PDF p.3).

**Formalization Note** The set is nonempty and compact, so the real `sSup` is the printed maximum; `lemma_3_1`
records that it is attained. -/
noncomputable def En (c : ℕ → ℝ) (n : ℕ) (α : Idx n → ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * sSup (energy (ham c n α) '' ProdStates n)

end QPSpinParisi


