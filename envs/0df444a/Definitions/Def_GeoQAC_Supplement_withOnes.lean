-- Prove2me | Definitions.Def_GeoQAC_Supplement_withOnes
-- name    : GeoQAC_Supplement_withOnes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:18:01.020254+00:00
-- url     : https://prove2.me/theorems/dbab4cb2-b9ec-4892-a976-130bf84cddf8
-- title:
--   A data register tensored with an all-ones workspace
-- statement:
--   For a vector $|\phi\rangle$ on $n$ data qubits placed at given positions, $|\phi\rangle\otimes|1^{m}\rangle$ is the vector that carries $\phi$ on the data qubits and $|1\rangle$ on every other qubit: its amplitude at a configuration $y$ is $\phi(y|_{\mathrm{data}})$ if $y$ is $1$ on every workspace qubit, and $0$ otherwise.
--
--   It states the exact simulation of Theorem 3.1, whose workspace starts and ends in $|1^{n^2}\rangle$.
--
--   **Formalization Note** The data placement is any injective map into the qubits.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.1, p.13

import Mathlib

namespace GeoQAC.Supplement

/-!
# A data register tensored with an all-ones workspace

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.1, p.13: the vector
`|ϕ⟩ ⊗ |1^{n²}⟩` on the `(n+1) × n` grid, the `n` data qubits carrying `ϕ` and the other `n²` qubits
in `|1⟩`.

**Formalization Note.** The data qubits sit at an injective placement `data : Fin n ↪ V`; every
other qubit is workspace. The entry at a configuration `y` is `ϕ(y ∘ data)` if `y` is `1` on every
workspace qubit and `0` otherwise.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `|ϕ⟩` on the data qubits `data`, tensored with `|1⟩` on every other qubit (Theorem 3.1, p.13). -/
def withOnes {n : ℕ} (data : Fin n ↪ V) (ϕ : (Fin n → Bool) → ℂ) : (V → Bool) → ℂ :=
  fun y => if ∀ v, (∀ i, data i ≠ v) → y v = true then ϕ (fun i => y (data i)) else 0

end GeoQAC.Supplement


