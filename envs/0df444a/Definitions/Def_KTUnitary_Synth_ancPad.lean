-- Prove2me | Definitions.Def_KTUnitary_Synth_ancPad
-- name    : KTUnitary_Synth_ancPad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:22.079401+00:00
-- url     : https://prove2.me/theorems/69bd73d0-84b3-43c3-869d-ce7892d4c481
-- title:
--   Appending zero ancillas $|\psi\rangle\mapsto|\psi\rangle|0^a\rangle$
-- statement:
--   For $n\le N$ and an $n$-qubit vector $\psi$, the $N$-qubit vector $|\psi\rangle|0^{a}\rangle$ with $a=N-n$: $\psi$ on the first $n$ wires and $|0\rangle$ on the last $a$ wires. Its entry at a basis state $z$ is $\psi(z_0\cdots z_{n-1})$ when all ancilla bits of $z$ are $0$, and $0$ otherwise.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 5.1, p. 16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

open Classical in
/-- **Appending zero ancillas: `|ψ⟩ ↦ |ψ⟩|0^a⟩`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 5.1, p. 16). For `n ≤ N` and
an `n`-qubit vector `ψ`, the `N`-qubit vector with `ψ` on wires `0, …, n − 1` and `|0⟩` on the
`a = N − n` ancilla wires `n, …, N − 1`: its entry at `z` is `ψ(z₀ ⋯ z_{n−1})` if every ancilla bit of
`z` is `0`, and `0` otherwise.

**Formalization Note** The input occupies the first `n` wires and the ancillas the last `N − n`. -/
noncomputable def ancPad {n N : ℕ} (h : n ≤ N) (ψ : Bits n → ℂ) : Bits N → ℂ :=
  fun z => if ∀ q : Fin N, n ≤ q.val → z q = false then ψ (fun r => z (Fin.castLE h r)) else 0

end KTUnitary.Synth


