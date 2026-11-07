-- Prove2me | Definitions.Def_KarpLiptonOM_IsLexFirstCircuit
-- name    : KarpLiptonOM_IsLexFirstCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:23.083312+00:00
-- url     : https://prove2.me/theorems/055d9f30-8740-4245-adb1-2cbf6d74a20a
-- title:
--   Lexicographically first circuit code computing $L$ on $\{0,1\}^n$
-- statement:
--   For a language $L$ and $n, s \in \mathbb N$, the string $w$ is the **canonical circuit** $C_n$ if
--   1. $w$ encodes a circuit with $n$ inputs and at most $s$ gates that computes $L$ on $\{0,1\}^n$, and
--   2. no lexicographically smaller string encodes such a circuit.
--
--   All candidate strings have the same length $\ell(n, s)$, so lexicographic order is the usual order on binary strings of that length.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.3.9 and its proof, p.28

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_KarpLiptonOM_circuitCode

namespace KarpLiptonOM

/-- `w` is the lexicographically first string of length `ℓ(n, s)` that encodes a circuit with `n`
inputs and at most `s` gates computing `L` on `{0,1}ⁿ` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Lemma A.3.9 and its proof, p.28:
"`C_n` the lexicographically first string of length `ℓ(n)` that encodes a circuit computing `L` on
`{0,1}ⁿ`"). -/
def IsLexFirstCircuit (L : Set (List Bool)) (n s : ℕ) (w : List Bool) : Prop :=
  let E : List Bool → Prop := fun v => ∃ C : Circuit n, C.gates.length ≤ s ∧ circuitCode n s C = v ∧
    ∀ x : List Bool, x.length = n → (C.eval x = true ↔ x ∈ L)
  E w ∧ ∀ v, E v → ¬ v < w

end KarpLiptonOM


