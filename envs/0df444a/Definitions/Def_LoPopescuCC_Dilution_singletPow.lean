-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_singletPow
-- name    : LoPopescuCC_Dilution_singletPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:11.21493+00:00
-- url     : https://prove2.me/theorems/a525c94b-8106-499a-8996-e7acdd4b03e5
-- title:
--   $d$ singlets $\Phi^{d}$
-- statement:
--   The singlet is $\Phi=(|01\rangle-|10\rangle)/\sqrt2$, one qubit held by Alice and one by Bob. The state $\Phi^{d}$ of $d$ singlets, with Alice's $d$ halves collected in a string $x\in\{0,1\}^d$ and Bob's in a string $y\in\{0,1\}^d$, has amplitudes
--
--   $$
--   \Phi^{d}(x,y)=\begin{cases}2^{-d/2}\,(-1)^{\#\{i\,:\,x_i=1\}} & \text{if } y_i=1-x_i \text{ for all } i,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   Singlets are the unit of entanglement: $\Phi^{d}$ has $2^d$ equal Schmidt coefficients and entropy of entanglement $d$.
--
--   **Formalization Note** $\Phi^0$ is the scalar $1$.
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Eq. (8), p. 4 and Eq. (9), p. 5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace LoPopescuCC.Dilution

/-- **`d` singlets `Φ^d`** (Lo, Popescu, arXiv:quant-ph/9902045v2, Eq. (8), p. 4: "where Φ denotes
a singlet state"; Eq. (9), p. 5): the vector `((|01⟩ − |10⟩)/√2)^{⊗d}`, with Alice's `d` halves in
the first index and Bob's in the second. Its amplitude at `(x, y)` is
`2^{−d/2} (−1)^{#{i : x_i = 1}}` when `y` is the bitwise complement of `x`, and `0` otherwise.

**Formalization Note** The bit `true` is `|1⟩`, and the sign is the one of the singlet with Alice's
bit first. `singletPow 0` is the scalar `1`. -/
noncomputable def singletPow (d : ℕ) : EuclideanSpace ℂ (QAlgorithms.Qubits d × QAlgorithms.Qubits d) :=
  WithLp.toLp 2 fun z =>
    if ∀ i, z.2 i = !z.1 i then
      ((Real.sqrt (2 ^ d))⁻¹ : ℂ) * (-1) ^ (Finset.univ.filter fun i => z.1 i = true).card
    else 0

end LoPopescuCC.Dilution


