-- Prove2me | Definitions.Def_QPSpinParisi_prodKet
-- name    : QPSpinParisi_prodKet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:45.764639+00:00
-- url     : https://prove2.me/theorems/949d65a3-1846-469d-aa28-e355e24d383a
-- title:
--   The product vector $|\phi(1)\rangle\otimes\dots\otimes|\phi(n)\rangle$
-- statement:
--   The tensor product of $n$ one-qubit vectors, whose amplitude at a bit string $x$ is the product $\prod_j\phi_j(x_j)$ of single-qubit amplitudes.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The product vector `|ϕ(1)⟩ ⊗ ⋯ ⊗ |ϕ(n)⟩` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3, PDF p.3), with amplitude at the bit string `x`
equal to the product of the single-qubit amplitudes. -/
def prodKet {n : ℕ} (φ : Fin n → Bool → ℂ) : QAlgorithms.Qubits n → ℂ :=
  fun x => ∏ j : Fin n, φ j (x j)

end QPSpinParisi


