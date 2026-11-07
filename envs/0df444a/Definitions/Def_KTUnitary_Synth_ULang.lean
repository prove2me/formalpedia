-- Prove2me | Definitions.Def_KTUnitary_Synth_ULang
-- name    : KTUnitary_Synth_ULang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:31.016097+00:00
-- url     : https://prove2.me/theorems/42c1f8a6-4940-4112-9280-667cce75e887
-- title:
--   Unitary language
-- statement:
--   A **unitary language** is a sequence $\mathcal U=\{U_n\}_{n\in\mathbb N}$ of unitaries, $U_n\in\mathbb C^{2^n\times 2^n}$ acting on $n$ qubits. The set of all unitary languages is $\mathsf{unitaryALL}$.
--
--   A helper builds a unitary language from explicit matrices $M_n$: its $n$-th member is $M_n$ when $M_n$ is unitary and the identity otherwise. All uses in this mission (the unitary embedding of a language, the phase encoding, the column language) supply unitary matrices.
--
--   **Formalization Note** The basis states of $n$ qubits are the bit vectors `Bits n = Fin n → Bool` ($0$ is $|0\rangle$).
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.9, p. 16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Unitary language** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.9, p. 16): "A unitary language is a collection of
unitaries `𝒰 = {U_n}_{n ∈ ℕ}` with `U_n ∈ ℂ^{2^n × 2^n}`." "Throughout, `unitaryALL` denotes the set
of all unitary languages": in Lean, `Set.univ : Set ULang`.

**Formalization Note** The basis of `n` qubits is indexed by `Bits n = Fin n → Bool` (`false` is
`|0⟩`), so `U_n` is a unitary matrix indexed by `Bits n`. -/
abbrev ULang := (n : ℕ) → Matrix.unitaryGroup (Bits n) ℂ

open Classical in
/-- The unitary language whose `n`-th member is the matrix `M n` when `M n` is unitary, and the
identity otherwise. Used to define unitary languages by explicit formulas (`emb`, `phaseEnc`,
`UColumn`); for those, every `M n` is unitary and the identity branch is never taken (checked for
`emb` and `phaseEnc` in the mission's verification files). -/
noncomputable def ULang.ofMatrices (M : (n : ℕ) → Matrix (Bits n) (Bits n) ℂ) : ULang :=
  fun n => if h : M n ∈ Matrix.unitaryGroup (Bits n) ℂ then ⟨M n, h⟩ else 1

end KTUnitary.Synth


