-- Prove2me | Definitions.Def_LindbladStructLearn_recordPair
-- name    : LindbladStructLearn_recordPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:49:52.764703+00:00
-- url     : https://prove2.me/theorems/5379f925-f10d-4eed-8c40-df3bc2b652e8
-- title:
--   Pair of Paulis named by an output record
-- statement:
--   An output record at integer address $b$ holds a size $s$, the sites $i_1 < \dots < i_s$ (0-based, in $[0,n)$) in the next $k$ cells, and the letters of $P_1$ and $P_2$ on those sites in the following $2k$ cells; both Paulis are the identity off the listed sites. The record is valid when $0 \le s \le k$, the sites are strictly increasing in range and the letters lie in $0..3$; then it names the pair $(P_1,P_2)$.
--
--   **Formalization Note** The sparse support encoding keeps the output within the runtime of Theorem 1.1; writing $2n$ letters per pair would not.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1, p.4; Lemma 2.10, p.18

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The pair of Paulis named by an output record (output ABI of the learner, Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 1.1
and Lemma 2.10). A record at integer address `b` holds `s` (cell `b`), the sites `i₁ < … < i_s`
(cells `b+1 … b+k`, 0-based qubits), the letters of `P₁` (cells `b+1+k …`) and of `P₂`
(cells `b+1+2k …`) on those sites; it is valid when `0 ≤ s ≤ k`, the sites are strictly increasing
in `[0, n)` and the letters in `0..3`.

**Formalization Note** A sparse support encoding: writing `2n` letters per pair would cost more than
the runtime of Theorem 1.1 allows. Off the listed sites both Paulis are `I`. -/
def recordPair (n k : ℕ) (im : ℤ → ℤ) (b : ℤ) : Option (Pauli n × Pauli n) := by
  classical
  exact
  let s := im b
  let site : ℕ → ℤ := fun r => im (b + 1 + r)
  let l1 : ℕ → ℤ := fun r => im (b + 1 + k + r)
  let l2 : ℕ → ℤ := fun r => im (b + 1 + 2 * k + r)
  if 0 ≤ s ∧ s ≤ k ∧
      (∀ r < s.toNat, 0 ≤ site r ∧ site r < n ∧ 0 ≤ l1 r ∧ l1 r ≤ 3 ∧ 0 ≤ l2 r ∧ l2 r ≤ 3) ∧
      (∀ r, r + 1 < s.toNat → site r < site (r + 1)) then
    some (fun i => if h : ∃ r, r < s.toNat ∧ site r = (i : ℤ) then
              ⟨(l1 (Nat.find h)).toNat % 4, Nat.mod_lt _ (by norm_num)⟩ else 0,
          fun i => if h : ∃ r, r < s.toNat ∧ site r = (i : ℤ) then
              ⟨(l2 (Nat.find h)).toNat % 4, Nat.mod_lt _ (by norm_num)⟩ else 0)
  else none

end LindbladStructLearn


