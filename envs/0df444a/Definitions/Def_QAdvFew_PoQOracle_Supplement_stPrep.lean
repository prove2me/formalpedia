-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_stPrep
-- name    : QAdvFew_PoQOracle_Supplement_stPrep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:15:50.792561+00:00
-- url     : https://prove2.me/theorems/79877aa0-60b5-443b-a093-61bb14f6b936
-- title:
--   State preparation unitaries
-- statement:
--   For a pure state $|\phi\rangle$ on $k$ qubits, the **state preparation unitary** (Definition 3.19) acts on a flag qubit and $k$ qubits and swaps $|0\rangle|0\rangle$ with $|1\rangle|\phi\rangle$:
--
--   $$
--   S_{|\phi\rangle}=I-|1\rangle\langle1|\otimes|\phi\rangle\langle\phi|-|0\rangle\langle0|\otimes|0\rangle\langle0|+|0\rangle\langle1|\otimes|0\rangle\langle\phi|+|1\rangle\langle0|\otimes|\phi\rangle\langle0| .
--   $$
--
--   For a mixed state $\sigma$ on $n$ qubits with a fixed purification $|\phi\rangle\in\mathcal H(\{0,1\}^n)\otimes\mathcal H(\{0,1\}^m)$ and $U\in U(2^m)$, the **random state preparation** map (Definitions 3.20–3.21) is $S^U_\sigma=S_{(I\otimes U)|\phi\rangle}$.
--
--   These are the building blocks of the oracles $\mathrm{SG}_t$, $\mathrm{Expand}_t$, $\mathrm{Mix}_t$ of §5.1 and of $S=\{S^{U_t}_{\sigma_t}\}$ in Appendix A.
--
--   **Formalization Note** The identity $S^U_\sigma=C_US_\sigma C_U^\dagger$ printed in Definition 3.21 is a property of this operator, not part of its definition.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definitions 3.19–3.21, p. 16 (PDF p. 18)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_Layout

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

/-- The **state preparation unitary** `S_{|ϕ⟩}` for a pure state `|ϕ⟩` on `k` qubits (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
Definition 3.19, p. 16 (PDF p. 18): "the map which swaps `|0⟩|0⟩` and `|1⟩|ϕ⟩` defined by
`S_{|ϕ⟩} = I − |1⟩⟨1| ⊗ |ϕ⟩⟨ϕ| − |0⟩⟨0| ⊗ |0⟩⟨0| + |0⟩⟨1| ⊗ |0⟩⟨ϕ| + |1⟩⟨0| ⊗ |ϕ⟩⟨0|`"), on
`1 + k` qubits: the first qubit is the flag, the last `k` the register. Entry `(y, z)` with
`y = (a, r)`, `z = (b, s)` is the printed operator's matrix element, term by term.

**Formalization Note** It is unitary when `|ϕ⟩` is a unit vector. -/
noncomputable def stPrep {k : ℕ} (ϕ : QState k) : Matrix (Bits (1 + k)) (Bits (1 + k)) ℂ :=
  fun y z =>
    let a := (lft y) 0
    let b := (lft z) 0
    let r : Bits k := rgt y
    let s : Bits k := rgt z
    (if y = z then 1 else 0)
      - (if a = true ∧ b = true then ϕ r * star (ϕ s) else 0)
      - (if a = false ∧ b = false ∧ r = (fun _ => false) ∧ s = (fun _ => false) then 1 else 0)
      + (if a = false ∧ b = true ∧ r = (fun _ => false) then star (ϕ s) else 0)
      + (if a = true ∧ b = false ∧ s = (fun _ => false) then ϕ r else 0)

/-- `(I ⊗ U)|ϕ⟩` for `|ϕ⟩` on `n + m` qubits and `U` on the last `m`. -/
noncomputable def applyRight {n m : ℕ} (U : Matrix (Bits m) (Bits m) ℂ) (ϕ : QState (n + m)) :
    QState (n + m) :=
  fun z => ∑ p : Bits m, U (rgt z) p * ϕ (Fin.append (lft z) p)

/-- The **random state preparation** map `S^U_σ` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Definitions 3.20–3.21, p. 16 (PDF p. 18):
"Fix any purification `|ϕ⟩ ∈ H({0,1}^n) ⊗ H({0,1}^m)` with `σ = Tr_B(|ϕ⟩⟨ϕ|_{AB})`. Let
`S_σ = S_{|ϕ⟩}` … Let `U ∈ U(2^m)`. We define `S^U_σ = S_{(I ⊗ U)|ϕ⟩} = C_U S_σ C_U^†`"), given
the purification `|ϕ⟩` itself: `S_{(I ⊗ U)|ϕ⟩}` on `1 + (n + m)` qubits.

**Formalization Note** The second printed form `C_U S_σ C_U^†` is an identity about this operator,
not part of the definition. -/
noncomputable def stPrepU {n m : ℕ} (ϕ : QState (n + m)) (U : Matrix (Bits m) (Bits m) ℂ) :
    Matrix (Bits (1 + (n + m))) (Bits (1 + (n + m))) ℂ :=
  stPrep (applyRight U ϕ)

end QAdvFew.PoQOracle.Supplement


