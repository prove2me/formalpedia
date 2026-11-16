-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_decodeSupports
-- name    : ArbLindbladLearn_Supplement_decodeSupports
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:14:07.743926+00:00
-- url     : https://prove2.me/theorems/6d1f5ce1-463f-473f-94a5-19125318c893
-- title:
--   Candidate supports $(\hat{\mathcal S}_H,\hat{\mathcal S}_D)$ output by a halted learner
-- statement:
--   The support-learning algorithm (Algorithm 1) outputs two candidate sets: $\hat{\mathcal S}_H$, a set of nonidentity Pauli labels, and $\hat{\mathcal S}_D$, a set of ordered pairs of nonidentity labels. This definition reads them from the final configuration of a halted run of the learner's machine.
--
--   At the halt pointer $p$, the integer cells $p$ and $p+1$ hold counts $K_H$ and $K_D$. Then follow $K_H$ labels of $n$ cells each (letters $0=I,1=X,2=Y,3=Z$), and after them $K_D$ ordered pairs of labels of $2n$ cells each. $\hat{\mathcal S}_H$ is the set of valid nonidentity labels named, and $\hat{\mathcal S}_D$ the set of valid pairs whose two labels are both nonidentity (Algorithm 1 removes the identity label). A run that has not halted outputs two empty sets.
--
--   The output size $|\hat{\mathcal S}_H|+|\hat{\mathcal S}_D|$ of Theorem 3.8 is the sum of the sizes of the two sets.
--
--   **Formalization Note** Labels are parsed with the published `parseLabel`; an out-of-range letter invalidates a record. Repeated records are counted once.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Algorithm 1 (output), p.23; Theorem 3.8, p.24

import Mathlib
import Definitions.Def_ArbLindbladLearn_decode

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- The candidate supports `(Ŝ_H, Ŝ_D)` output by a halted learner (output of Algorithm 1, p.23, and
Theorem 3.8, p.24, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…)).

Layout at the halt pointer `p`: integer cells `p`, `p + 1` hold the counts `K_H`, `K_D`.
Hamiltonian candidate `j < K_H` is a label in the integer cells `p + 2 + jn, …, p + 2 + jn + n − 1`;
dissipative candidate `k < K_D` is an ordered pair of labels `a`, `b` in the `2n` integer cells
starting at `p + 2 + K_H n + 2kn` (`a` first). Labels are read by the published `parseLabel`
(letters `0 = I, 1 = X, 2 = Y, 3 = Z`; an out-of-range letter makes the record invalid). `Ŝ_H` is the
set of valid nonidentity labels named, `Ŝ_D` the set of valid pairs with both labels nonidentity
(Algorithm 1, line 16, removes the identity label). A machine that has not halted outputs `(∅, ∅)`.

**Formalization Note** The output size `|Ŝ_H| + |Ŝ_D|` of Theorem 3.8 is the sum of the two
`Finset` cardinalities, so repeated records are counted once. -/
def decodeSupports (n : ℕ) (s : MState) : Finset (Pauli n) × Finset (Pauli n × Pauli n) := by
  classical
  exact match s.output with
  | none => (∅, ∅)
  | some p =>
    let KH : ℕ := (s.intMem p).toNat
    let KD : ℕ := (s.intMem (p + 1)).toNat
    let hBase : ℕ → ℤ := fun j => p + 2 + (j : ℤ) * n
    let dBase : ℕ → ℤ := fun k => p + 2 + (KH : ℤ) * n + (k : ℤ) * (2 * n)
    ((Finset.range KH).biUnion fun j =>
        match parseLabel n s.intMem (hBase j) with
        | some a => if a ≠ 0 then {a} else ∅
        | none => ∅,
      (Finset.range KD).biUnion fun k =>
        match parseLabel n s.intMem (dBase k), parseLabel n s.intMem (dBase k + n) with
        | some a, some b => if a ≠ 0 ∧ b ≠ 0 then {(a, b)} else ∅
        | _, _ => ∅)

end ArbLindbladLearn.Supplement


