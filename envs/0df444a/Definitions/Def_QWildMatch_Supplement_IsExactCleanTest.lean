-- Prove2me | Definitions.Def_QWildMatch_Supplement_IsExactCleanTest
-- name    : QWildMatch_Supplement_IsExactCleanTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:19:17.132453+00:00
-- url     : https://prove2.me/theorems/9ff9b633-69eb-4717-9215-c5155be66acf
-- title:
--   Exact clean reversible implementation of a start-indexed test
-- statement:
--   Let $f(T,s)$ be a Boolean test of a text $T$ of length $n$ and a start $s\le n$. An oracle circuit $\mathcal C$ on $\lceil\log_2(n+2)\rceil+1+a$ wires (a start register, one output bit and $a$ ancillas), whose only black box is the text oracle $O_T$, is an **exact clean implementation** of $f$ if for every text $T$, every start $s\le n$ and every bit $z$,
--   $$\mathcal C^{O_T}\,|s\rangle|z\rangle|0^a\rangle=|s\rangle|z\oplus f(T,s)\rangle|0^a\rangle$$
--   exactly.
--
--   This is Definition 3.2 (clean text oracle) with zero error, for the fixed-start test of Theorem 4.1. The circuit is chosen before the text, so it is uniform over texts; by linearity the equation extends to every superposition of starts and output bits; the ancillas are returned to $0$.
--
--   **Formalization Note** Circuits are the published `QAlgorithms.OracleCircuit` lists of gates and oracle calls (plain, inverse or controlled).
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…1f96), Definition 3.2, p.4; Theorem 4.1, last sentence, p.5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QWildMatch_Supplement_textOracleGate

namespace QWildMatch.Supplement

open QAlgorithms

open Classical in
/-- An **exact, clean** reversible implementation of a start-indexed Boolean test `f T s` (Zhao, Chen, Li,
Kong, Peng, Yu, Yue, STOC 2027 submission (file sha256 9e87a9dd…), Definition 3.2, p.4, with zero error;
Theorem 4.1, last sentence, p.5). The oracle circuit `c` runs on `idxBits n + 1 + anc` wires: the start
register (`idxBits n` bits, value `s`), one output bit `z`, and `anc` ancillas initialized to `0`. Its
single black box is the text-oracle gate `O_T` on `idxBits n + w` wires. For every text `T`, every start
`s ≤ n` and every `z`, the circuit with `O_T` plugged in maps `|s⟩|z⟩|0…0⟩` to
`|s⟩|z ⊕ [f T s]⟩|0…0⟩` exactly.

**Formalization Note** The circuit is fixed before the text: `T` enters only through the black box, which
is the "uniform" of Theorem 4.1. Exactness is an equality of vectors on basis states, hence by linearity on
every superposition of starts and output bits; the ancillas return to `0` ("clean"). Calls may be plain,
inverse or controlled, as `OracleStep` allows. -/
def IsExactCleanTest {Sym : Type} {S : Set Gate} {n w anc : ℕ} (enc : Sym → (Fin w → Bool))
    (c : OracleCircuit S (fun _ : Fin 1 => idxBits n + w) (idxBits n + 1 + anc))
    (f : (Fin n → Sym) → ℕ → Prop) : Prop :=
  ∀ (T : Fin n → Sym) (s : ℕ), s ≤ n → ∀ z : Bool,
    act (OracleCircuit.unitary c (fun _ => textOracleGate (a := idxBits n) enc T))
        (ket (Fin.append (Fin.append (natToBits (idxBits n) s) (fun _ : Fin 1 => z))
          (fun _ : Fin anc => false))) =
      ket (Fin.append (Fin.append (natToBits (idxBits n) s) (fun _ : Fin 1 => xor z (decide (f T s))))
          (fun _ : Fin anc => false))

end QWildMatch.Supplement


