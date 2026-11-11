-- Prove2me | Definitions.Def_StabTestMem_pbsElem
-- name    : StabTestMem_pbsElem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:24.273512+00:00
-- url     : https://prove2.me/theorems/c52ef1b3-5ef9-48f2-9aba-b48c78374ff0
-- title:
--   POVM element of partial Bell sampling, Eq. (25)
-- statement:
--   **Partial Bell sampling** (Algorithm 1) acts on two copies of a $(k+m)$-qubit state: it Bell-samples the two $k$-qubit prefixes (one stored in the $k$-qubit memory) and measures both suffixes in the computational basis, returning $(a,z_0\oplus z_1)$. The POVM element of outcome $(a,r)$, $a\in\mathbb F_2^{2k}$, $r\in\mathbb F_2^m$, is
--
--   $$E_{a,r}=|\Phi_a\rangle\langle\Phi_a|\otimes\sum_{x\in\mathbb F_2^m}|x,x+r\rangle\langle x,x+r|,\qquad |\Phi_a\rangle=2^{-k/2}\sum_{y\in\mathbb F_2^k}(-1)^{y\cdot a_Z}|y,y+a_X\rangle,$$
--
--   with $|\Phi_a\rangle$ on the two prefixes and the projector on the two suffixes.
--
--   **Formalization Note** Rows and columns are indexed by (copy 1, copy 2); prefix and suffix as in `concat`. The element is invariant under exchanging the copies.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Algorithm 1 and Eq. (25), p. 18

import Definitions.Def_CutRankSched_Pauli
import Definitions.Def_QAlgorithms_Defs_Basic

namespace StabTestMem

open QAlgorithms

/-- **The POVM element of partial Bell sampling (Algorithm 1) for outcome `(a, r)`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026),
Algorithm 1 and Eq. (25), p. 18: "To the outcome (a, r) we can associate the POVM aspect
|Φ_a⟩⟨Φ_a| ⊗ Σ_x |x, x + r⟩⟨x, x + r|, where |Φ_a⟩ = 2^{−k/2} Σ_y (−1)^{y·a_Z} |y, y + a_X⟩ is a
Bell state on the first k qubits."

The operator acts on two copies of a `(k + m)`-qubit register (copy 1, copy 2). Writing `p_i`
for the prefix (first `k` qubits) and `s_i` for the suffix (last `m` qubits) of copy `i`, its
entry in row `((p₁ s₁), (p₂ s₂))`, column `((p₁' s₁'), (p₂' s₂'))` is
`[p₂ = p₁ ⊕ a_X] [p₂' = p₁' ⊕ a_X] 2^{−k} (−1)^{a_Z·p₁ + a_Z·p₁'} · [s₁ = s₁'] [s₂ = s₂'] [s₂ = s₁ ⊕ r]`,
i.e. `|Φ_a⟩⟨Φ_a|` on the two prefixes tensored with the diagonal projector `Σ_x |x, x + r⟩⟨x, x + r|`
on the two suffixes.

**Formalization Note.** Prefix = wires `0, …, k − 1` (`Fin.castAdd`), suffix = wires
`k, …, k + m − 1` (`Fin.natAdd`), the layout of `concat`. The paper's `m = n − k`. The element is
symmetric under exchanging the two copies, so the order of memory and fresh copy in Algorithm 1
does not matter. -/
noncomputable def pbsElem {k m : ℕ} (a : CutRankSched.Pauli k) (r : Fin m → ZMod 2) :
    Matrix (Qubits (k + m) × Qubits (k + m)) (Qubits (k + m) × Qubits (k + m)) ℂ :=
  Matrix.of fun Y Y' =>
    let pre : Qubits (k + m) → Fin k → ZMod 2 := fun y j => if y (Fin.castAdd m j) then 1 else 0
    let suf : Qubits (k + m) → Fin m → ZMod 2 := fun y j => if y (Fin.natAdd k j) then 1 else 0
    if pre Y.2 = pre Y.1 + a.1 ∧ pre Y'.2 = pre Y'.1 + a.1 ∧
        suf Y.1 = suf Y'.1 ∧ suf Y.2 = suf Y'.2 ∧ suf Y.2 = suf Y.1 + r then
      ((2 : ℂ) ^ k)⁻¹ * (-1 : ℂ) ^ (∑ j, pre Y.1 j * a.2 j + ∑ j, pre Y'.1 j * a.2 j).val
    else 0

end StabTestMem


