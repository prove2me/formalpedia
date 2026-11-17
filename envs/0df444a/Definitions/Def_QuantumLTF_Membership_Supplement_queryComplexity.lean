-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_queryComplexity
-- name    : QuantumLTF_Membership_Supplement_queryComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:32:58.54196+00:00
-- url     : https://prove2.me/theorems/496ab89d-1d11-4108-93d8-fe6d5bf106a3
-- title:
--   Bounded-error quantum query complexity $Q_n(\mathcal A)$ of learning Majority
-- statement:
--   For a promise $\mathcal A$ on subsets of $[n]$, $Q_n(\mathcal A)$ is the least $T\in\mathbb N$ for which some quantum algorithm with oracle access to $f_A$, using at most $T$ queries, outputs $A$ with error probability at most $1/3$ for every $A\in\mathcal A$ (Definition 2.2).
--
--   An algorithm is an oracle circuit on any number $m$ of qubits started in $|0^m\rangle$. Its gates are arbitrary unitaries of any arity, since query complexity charges only queries. Its calls to the Majority bit oracle may be plain, inverse or controlled, and each call counts as one query. After the circuit, all qubits are measured in the computational basis; the output is the indicator vector of $A$, read on $n$ designated qubits.
--
--   **Formalization Note** Defined as an infimum over $\mathbb N$. For the paper's promises ($|A|=k$, $1\le|A|\le k$; all sets nonempty) the set of admissible $T$ is nonempty: $f_A$ determines a nonempty $A$ (it is the union of the minimal sets $S$ with $f_A(S)=1$), so querying every $S$ classically suffices. The infimum is therefore never the junk value of an empty set.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Definition 2.2, p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_Supplement_majOracle

namespace QuantumLTF.Membership.Supplement

open QAlgorithms

/-- **`Q_n(𝒜)`: bounded-error quantum query complexity of learning Majority.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331,
Definition 2.2, p. 16 (PDF p. 17): given oracle access to `f_A` for an unknown `A` in the promise
`𝒜`, output `A` with error probability at most `1/3`. `Q_n(𝒜)` is the least `T` such that some oracle
circuit with at most `T` queries to the Majority oracle, started in `|0…0⟩` and measured in the
computational basis, outputs `A` (the indicator bits of `A` on the designated wires `out`) with
probability at least `2/3` for every `A ∈ 𝒜`.

**Formalization Note.** Query complexity charges only queries, so the gate set is every unitary gate,
of any arity (`{g | g.IsUnitary}`), and the number `m` of wires is free. Controlled and inverse calls
are allowed and each counts as one query (`queryCount`). The promise is a predicate `P` on
`Finset (Fin n)`; the paper's promises `|A| = k` and `1 ≤ |A| ≤ k` consist of nonempty sets. The set
of admissible `T` is nonempty for such promises (`f_A` determines a nonempty `A`: `A` is the union of
the minimal sets `S` with `f_A(S) = 1`, so `2ⁿ` queries suffice), so `sInf` is not the junk `0` of
the empty set. -/
noncomputable def queryComplexity (n : ℕ) (P : Finset (Fin n) → Prop) : ℕ :=
  sInf {T : ℕ | ∃ (m : ℕ) (c : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) m)
    (out : Fin n ↪ Fin m), c.queryCount 0 ≤ T ∧
    ∀ A : Finset (Fin n), P A →
      open Classical in
      probEvent (act (c.unitary fun _ => majOracle A) (zeroKet m))
        (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 2 / 3}

end QuantumLTF.Membership.Supplement


