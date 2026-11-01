-- Prove2me | Definitions.Def_BaconThesis_WeakUniv_dfsProj
-- name    : BaconThesis_WeakUniv_dfsProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:39.874345+00:00
-- url     : https://prove2.me/theorems/79c86f4f-773c-4eb7-ab79-092c7c0a68e9
-- title:
--   Definition 8.5.1 — the projector onto $\mathrm{DFS}_n(h)$
-- statement:
--   Weak collective decoherence on $n$ qubits supports the decoherence-free subspaces $\mathrm{DFS}_n(h)$, $0\le h\le n$, where $\mathrm{DFS}_n(h)$ is spanned by the computational basis states $|x\rangle$ of Hamming weight $H(x)=h$; its dimension is $\binom nh$. The projector onto it is the diagonal matrix
--   $$
--   P_h=\sum_{x:\,H(x)=h}|x\rangle\langle x|.
--   $$
--   An operator $X$ acts on $\mathrm{DFS}_n(h)$ only, with zero rows and columns at all other basis states, exactly when $P_hXP_h=X$. Appendix B labels the same subspace by $K=n-2h$, the number of zeros minus the number of ones.
--
--   **Formalization Note** For $h>n$ the projector is $0$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Definition 8.5.1 and eq. (8.35), p.115 (PDF p.132); eq. (B.2), p.234 (PDF p.251)

import Mathlib

namespace BaconThesis.WeakUniv

/-- **The projector onto the weak collective decoherence DF subspace `DFS_n(h)`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
Definition 8.5.1, p.115 (PDF p.132): "Weak collective decoherence on n qubits supports DF subspaces
labeled by the integer 0 ≤ h ≤ n, DFS_n(h). DFS_n(h) is spanned by basis states in the
computational basis |i⟩ which have Hamming weight H(i) equal to h." Appendix B, p.234 (PDF p.251),
labels the same subspace by `K = n − 2h` (eq. (B.2)).

`dfsProj n h` is the orthogonal projector onto `DFS_n(h)`: the diagonal matrix with entry `1` at
the basis states `|x⟩` with exactly `h` ones and `0` elsewhere. An operator `X` acts on `DFS_n(h)`
only ("with zeroes in the rows and columns corresponding to the other DFSs", p.235) exactly when
`dfsProj n h * X * dfsProj n h = X`.

**Formalization Note.** Basis states are `x : Fin n → Fin 2`; the Hamming weight is the number of
`m : Fin n` with `x m = 1`. For `h > n` the projector is `0`. -/
def dfsProj (n h : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.diagonal fun x => if (Finset.univ.filter fun m => x m = 1).card = h then 1 else 0

end BaconThesis.WeakUniv


