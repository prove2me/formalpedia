-- Prove2me | Definitions.Def_QPSpinParisi_ProdStates
-- name    : QPSpinParisi_ProdStates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:05.000749+00:00
-- url     : https://prove2.me/theorems/51a9fc62-2e4a-486b-b1ea-a47d70d4a029
-- title:
--   The product states $S^n_{\mathrm{prod}}$
-- statement:
--   The set of product states on $n$ qubits:
--   $$S^n_{\mathrm{prod}}=\{|\phi(1)\rangle\otimes\dots\otimes|\phi(n)\rangle:\ |\phi(i)\rangle\in S^1\ \text{for all } i\}.$$
--   It is the feasible set of the optimization problem (2.2).
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_QPSpinParisi_prodKet
import Definitions.Def_QPSpinParisi_IsUnitQubit

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The set `S^n_prod` of product states on `n` qubits (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3, PDF p.3). -/
def ProdStates (n : ℕ) : Set (QAlgorithms.Qubits n → ℂ) :=
  {ψ | ∃ φ : Fin n → Bool → ℂ, (∀ j, IsUnitQubit (φ j)) ∧ ψ = prodKet φ}

end QPSpinParisi


