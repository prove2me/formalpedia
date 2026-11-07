-- Prove2me | Definitions.Def_QPSpinParisi_ham
-- name    : QPSpinParisi_ham
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:33.898212+00:00
-- url     : https://prove2.me/theorems/09bb99b9-257f-4a35-80d1-cd633579747f
-- title:
--   The mixed $p$-spin Hamiltonian $H_n$, (2.1)
-- statement:
--   The quantum mixed $p$-spin Hamiltonian on $n$ qubits is
--   $$H_n=\sum_{p\ge2}c_pH_{n,p},\qquad H_{n,p}=N_{n,p}^{-1/2}\sum_{\bar i\in I^n_p}\sum_{\bar a\in\{1,2,3\}^p}\alpha[\bar i,\bar a]\,P^{\bar a}_{\bar i}.$$
--   This is the random Hamiltonian of the mission. Its coefficients are the Gaussian vector $\alpha$.
--
--   **Formalization Note** The double sum over $p$ and the tuples is one sum over indices, so the sum over $p$ stops at $p=n$, as in (3.1) and (3.5).
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.1), p.3 (PDF p.3)

import Mathlib
import Definitions.Def_QPSpinParisi_coef
import Definitions.Def_QPSpinParisi_pauliStr

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The mixed `p`-spin Hamiltonian `H_n = ∑_{p≥2} c_p H_{n,p}`, with
`H_{n,p} = N_{n,p}^{-1/2} ∑_ī ∑_ā α[ī, ā] P^ā_ī` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.1), p.3, PDF p.3).

**Formalization Note** The double sum over `p` and over tuples is one sum over `Idx n`. The sum over `p` stops at
`p = n`, since a `p`-local string needs `p` distinct sites (compare (3.1) and (3.5)). -/
noncomputable def ham (c : ℕ → ℝ) (n : ℕ) (α : Idx n → ℝ) :
    Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ :=
  ∑ i : Idx n, ((coef c i * α i : ℝ) : ℂ) • pauliStr i

end QPSpinParisi


