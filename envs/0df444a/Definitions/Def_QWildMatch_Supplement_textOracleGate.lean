-- Prove2me | Definitions.Def_QWildMatch_Supplement_textOracleGate
-- name    : QWildMatch_Supplement_textOracleGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:18:44.687535+00:00
-- url     : https://prove2.me/theorems/c2f1d9f3-a431-4ef7-a85b-dd8de226c01a
-- title:
--   The text oracle $O_T$ as a gate on a binary index register
-- statement:
--   For a text $T\in\Sigma^n$ and an injective encoding $\mathrm{enc}:\Sigma\to\{0,1\}^w$, the text oracle
--   $$O_T:\ |j,z\rangle\mapsto|j,\,z\oplus\mathrm{enc}(T[j])\rangle$$
--   is realized as a gate on $a+w$ qubits: the first $a$ qubits hold the index $j$ in binary (most significant bit first) and the last $w$ hold the target $z$. Indices $j\ge n$, which a binary register can hold, are left unchanged. Also defined is $\mathrm{idxBits}(n)=\lceil\log_2(n+2)\rceil\ge1$, the width of a register holding $0,\dots,n$.
--
--   This is the black box of the gate-level statement of Theorem 4.1 (its last sentence): a reversible circuit reads the text only through this gate.
--
--   **Formalization Note** The gate is the permutation matrix of the map above; it is its own inverse, so an inverse call is charged as one query (§3, p.4).
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…1f96), §3, p.4 (the text oracle O_T); Theorem 4.1, p.5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit

namespace QWildMatch.Supplement

open QAlgorithms

/-- The number of bits of an index register holding `0, …, n`: `⌈log₂(n + 2)⌉`, which is at least `1`
(Zhao, Chen, Li, Kong, Peng, Yu, Yue, STOC 2027 submission (file sha256 9e87a9dd…), §3, p.4; Theorem 4.1,
p.5). -/
def idxBits (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

/-- The text oracle `O_T : |j, z⟩ ↦ |j, z ⊕ T[j]⟩` as a gate on `a + w` qubits (Zhao et al., STOC 2027
submission (file sha256 9e87a9dd…), §3, p.4), for the gate-level reading of Theorem 4.1's last sentence
(p.5). The first `a` wires hold the index `j` in binary, most significant bit first (`bitsToNat`), the
last `w` wires hold the target `z`; a symbol is written as the bit string `enc (T j)`.

**Formalization Note** An index `j ≥ n` (the binary register holds values up to `2^a − 1`) is answered by
the identity, as the base mission's `textOracle` answers its extra index `none` by `0`. The matrix is the
permutation matrix of `x ↦ f x`: entry `(y, x)` is `1` exactly when `y = f x`. Over `Bool`, `z ⊕ enc(T j)`
is `xor`, so the gate is its own inverse. -/
def textOracleGate {Sym : Type} {n a w : ℕ} (enc : Sym → (Fin w → Bool)) (T : Fin n → Sym) :
    Matrix (Qubits (a + w)) (Qubits (a + w)) ℂ :=
  Matrix.of fun y x =>
    if y = (if h : bitsToNat (fun i : Fin a => x (Fin.castAdd w i)) < n then
        Fin.append (fun i : Fin a => x (Fin.castAdd w i))
          (fun i : Fin w => xor (x (Fin.natAdd a i))
            (enc (T ⟨bitsToNat (fun i : Fin a => x (Fin.castAdd w i)), h⟩) i))
      else x) then 1 else 0

end QWildMatch.Supplement


