-- Prove2me | Definitions.Def_QStateSearch_Supplement_sec5Oracle
-- name    : QStateSearch_Supplement_sec5Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:19:26.683201+00:00
-- url     : https://prove2.me/theorems/949d06ff-b5ba-4baa-b6da-f5d7433ca2b3
-- title:
--   The Section 5 oracle $U_n=I-2b_n|\psi_n\rangle\langle\psi_n|$
-- statement:
--   For bits $b_n\in\{0,1\}$ and $n$-qubit vectors $\psi_n\in\mathbb C^{2^n}$, the quantum oracle $U=(U_n)_{n\ge1}$ with
--   $$U_n=I_{2^n}-2b_n|\psi_n\rangle\langle\psi_n| ,$$
--   so $U_n=I$ when $b_n=0$ and $U_n=R_{\psi_n}$ (the published reflection) when $b_n=1$. Labels are ignored, and a call on $0$ qubits is the identity.
--
--   Deciding whether $0^n$ is in the associated language means deciding whether $U_n$ is the identity or a reflection.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 5, p.14

import Mathlib
import Definitions.Def_QStateSearch_refl
import Definitions.Def_QStateSearch_Supplement_qIdx
import Definitions.Def_QStateSearch_Supplement_QOracle

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- The **oracle of Section 5**: for bits `b_n` and `n`-qubit vectors `ψ_n ∈ ℂ^{2^n}`, the
sequence `U = (U_n)_{n ≥ 1}` with
`U_n = I_{2^n} − 2 b_n |ψ_n⟩⟨ψ_n|`, i.e. `U_n = I` when `b_n = 0` and `U_n = R_{ψ_n}` when
`b_n = 1` (the base mission's published `QStateSearch.refl`, reindexed from `[2^n]` to
`{0,1}^n` by `qIdx`). The label of an oracle call is ignored; an oracle call on `0` qubits is
the identity.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 5, p.14: "For each n ≥ 1, choose a bit b_n ∈ {0, 1} and an n-qubit pure state |ψ_n⟩.
Define the n-qubit unitary U_n = I_{2^n} − 2b_n|ψ_n⟩⟨ψ_n| … Thus U_n = I_{2^n} when b_n = 0,
while U_n = R_{ψ_n} when b_n = 1. The quantum oracle is the family U = (U_n)_{n≥1}." -/
noncomputable def sec5Oracle (b : ℕ → Bool) (ψ : (n : ℕ) → EuclideanSpace ℂ (Fin (2 ^ n))) :
    QOracle := fun _ k =>
  if 1 ≤ k ∧ b k = true then (QStateSearch.refl (ψ k)).submatrix (qIdx k) (qIdx k) else 1

end QStateSearch.Supplement


