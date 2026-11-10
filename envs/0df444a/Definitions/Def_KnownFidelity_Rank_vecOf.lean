-- Prove2me | Definitions.Def_KnownFidelity_Rank_vecOf
-- name    : KnownFidelity_Rank_vecOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:44.461416+00:00
-- url     : https://prove2.me/theorems/738f0b71-5b19-435f-a036-47da836c67f2
-- title:
--   Vectorization $\mathrm{vec}(G)=\sum_{i,j}G_{ij}|i\rangle|j\rangle$
-- statement:
--   For $G\in\mathbb C^{d\times s}$,
--
--   $$\mathrm{vec}(G)=\sum_{i,j}G_{ij}\,|i\rangle|j\rangle\in\mathbb C^d\otimes\mathbb C^s .$$
--
--   The first tensor factor is the system and the second is the purifying register; a matrix $A$ with $\|A\|_F=1$ represents a purification of $AA^*$.
--
--   **Formalization Note** $\mathbb C^d\otimes\mathbb C^s$ is indexed by pairs (system index first).
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §2.1, Eq. (7), p. 4 (PDF p. 6)

import Mathlib

namespace KnownFidelity.Rank

/-- **Vectorization** `vec(G) = Σ_{i,j} G_ij |i⟩|j⟩`.
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §2.1, Eq. (7), printed p. 4 (PDF p. 6): "Our vectorization convention is:
vec(G) = Σ_{i,j} G_ij |i⟩|j⟩ … The first tensor factor is the system and the second is the
purifying register."

**Formalization Note.** `ℂ^d ⊗ ℂ^s` is indexed by `Fin d × Fin s` (system index first), and
`vec(G)_{(i,j)} = G_ij`. Only the first identity of (7) is used. -/
def vecOf {d s : ℕ} (G : Matrix (Fin d) (Fin s) ℂ) : Fin d × Fin s → ℂ :=
  fun p => G p.1 p.2

end KnownFidelity.Rank


