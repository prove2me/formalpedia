-- Prove2me | Definitions.Def_HorodeckiBoundKey_repetitionDecoder
-- name    : HorodeckiBoundKey_repetitionDecoder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:18.44083+00:00
-- url     : https://prove2.me/theorems/25cd8b25-4a55-4084-8cfa-42c2fa8501b0
-- title:
--   One party's recurrence-branch operator $J^\dagger\otimes\mathbb 1$
-- statement:
--   Let $J:\mathbb C^2\to(\mathbb C^2)^{\otimes n}$ be the isometry $J|i\rangle = |i\,i\cdots i\rangle$. One party's operator $J^\dagger\otimes\mathbb 1$ acts on its $n$ key qubits and $n$ shields: it maps $|i\cdots i\rangle\otimes|s\rangle$ to $|i\rangle\otimes|s\rangle$ and annihilates every other key string; the shields pass unchanged.
--
--   This is the Kraus operator of the successful branch of the recurrence protocol of [23] without twirling, in which bilateral CNOTs from the first pair onto the other $n-1$ pairs are followed by measurement of the targets, all outcomes being $0$. Applied by both parties to $n$ copies of the state (11) it produces the state (12) with probability $N$.
--
--   **Formalization Note** Matrix rows are $(a, s')$ (one key bit, the $n$ shields), columns $(x, s)$ ($n$ key bits, the $n$ shields); the entry is $1$ exactly when every $x_i = a$ and $s = s'$. The other agreeing-outcome branches of the protocol give the same normalized state; the paper's $N$ is the probability of this branch.
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.3, eq. (12) ("apply the recurrence distillation protocol of [23] without the twirling step")

import Mathlib

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.3 ("apply the
recurrence distillation protocol of [23] without the twirling step"): one party's operator
`J† ⊗ 𝟙` of the successful branch of that protocol on `n` copies. Here `J : ℂ² → (ℂ²)^{⊗n}`,
`J|i⟩ = |i…i⟩`, so `J†` maps `|i…i⟩` to `|i⟩` and every other basis vector to `0`; the party's
`n` shields pass unchanged.

**Formalization Note.** This is the Kraus operator of the branch in which every measured
target pair gives outcome `0` on both sides (bilateral CNOTs from the first pair onto the other
`n − 1` pairs, then measurement of the targets). Its success probability on `ρ^{⊗n}` is the
normalization `N` of (12); the branches with other agreeing outcomes yield the same normalized
state. As a matrix: rows `(a, s′) ∈ Fin 2 × (Fin n → S)`, columns
`(x, s) ∈ (Fin n → Fin 2) × (Fin n → S)`, entry `1` iff every `xᵢ = a` and `s = s′`. -/
def repetitionDecoder (n : ℕ) (S : Type*) [DecidableEq S] :
    Matrix (Fin 2 × (Fin n → S)) ((Fin n → Fin 2) × (Fin n → S)) ℂ :=
  fun a x => if (∀ i, x.1 i = a.1) ∧ x.2 = a.2 then 1 else 0

end HorodeckiBoundKey


