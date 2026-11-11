-- Prove2me | Definitions.Def_StabTestMem_cliffordAvg
-- name    : StabTestMem_cliffordAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:14.654459+00:00
-- url     : https://prove2.me/theorems/f2695276-9adb-4589-b2fc-dda293c25bcf
-- title:
--   Expectation over a uniformly random Clifford
-- statement:
--   For a real function $f$ on unitaries, $\mathbb E_C[f(C)]=|\mathcal C_n|^{-1}\sum_{C\in\mathcal C_n}f(C)$, the average over a uniformly random element of the (finite) $n$-qubit Clifford group $\mathcal C_n$. The paper's tester applies a uniformly random Clifford before each partial Bell difference sample.
--
--   **Formalization Note** Written with `Nat.card` and `finsum` over the subgroup; since the Clifford group is finite this is the uniform average.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Proposition 4.11, p. 34; Algorithm 6

import Definitions.Def_StabTestMem_cliffordGroup

namespace StabTestMem

open QAlgorithms

/-- **Expectation over a uniformly random Clifford, `E_C[f(C)]`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Proposition 4.11, p. 34
("Let C be a random Clifford"), and Algorithm 6 (the tester applies a uniformly random Clifford).

`cliffordAvg f = |𝒞_n|⁻¹ Σ_{C ∈ 𝒞_n} f(C)` over the Clifford group `𝒞_n` = `cliffordGroup n`.

**Formalization Note.** Written with `Nat.card` and `finsum` over the subgroup. The Clifford group
is finite, so this is the uniform average; (for an infinite group both would be the junk value 0,
which does not occur). -/
noncomputable def cliffordAvg {n : ℕ} (f : Matrix.unitaryGroup (Qubits n) ℂ → ℝ) : ℝ :=
  (Nat.card (cliffordGroup n) : ℝ)⁻¹ * ∑ᶠ C : cliffordGroup n, f C

end StabTestMem


