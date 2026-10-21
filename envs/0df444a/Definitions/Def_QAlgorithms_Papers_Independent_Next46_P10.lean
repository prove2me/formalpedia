-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P10
-- name    : QAlgorithms_Papers_Independent_Next46_P10
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:01:41.400297+00:00
-- url     : https://prove2.me/theorems/9a40e74a-3081-4939-88f1-4ab215baf633
-- title:
--   Definitions for A Practical Quantum Algorithm for the Schur Transform
-- statement:
--   The objects the formalized statements of *A Practical Quantum Algorithm for the Schur Transform* (arXiv:1709.07119) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `prefixBottomCount`: PDF p.13, the tableau insertion description preceding (26): the number of lower-row insertions among the first `k` boxes. A false bit means upper row, and a true bit means lower row.
--   - `IsTableauWord`: PDF pp.4,13: a standard tableau with at most two rows, recorded by the row receiving each successive entry 1,...,n. Every prefix must have at least as many upper-row as lower-row entries. Empty rows are allowed.
--   - `TwoRowTableau`: PDF pp.4,11,13, (11), (21), (26): all standard tableaux of shape (n-m,m). This is the full multiplicity-label set, rather than a bound supplied as an assumption.
--   - `QubitSchurLabel`: PDF pp.4,11--13: a Schur basis label consists of a standard two-row tableau p and a state s in the corresponding spin-j irrep, where 2j = n - 2 * hammingWeight p and s = 0,...,2j (spin projection j-s). The ambient Fin(n+1) only makes the finite label type explicit; the predicate restricts s to precisely its own irrep.
--   - `seqSize`: PDF p.13, (26): chosen multiplicity-register allocation, for n >= 2. Its total-function value below that domain is not a physical space claim.
--   - `parSize`: PDF p.13, (24): the number of bits needed for all floor(n/2)+1 shapes.
--   - `statSize`: PDF p.13, (25): the number of bits needed for the largest irrep, of shape (n,0) and dimension n+1.
--   - `totalSize`: PDF pp.10,14, (20), (27): actual allocated wires, summed in register order seq, par, stat, before simplifying the expression.
--   - `ancillaSize`: PDF p.14, (27): ancillary overhead computed from the allocation, rather than defined to be the expression asserted in the theorem.
--   - `seqWord`: PDF pp.11,13 permits a calculable, noncanonical order of the copies. Fix that order by retaining the row choices for entries 2,...,n-1. For a fixed final shape, entry 1 is in the upper row and the final entry's row is recovered from the total lower-row count. Unused words are ghosts. The branch merely totalizes the definition for n < 2.
--   - `labelEncoding`: PDF pp.10--13, (20), (24)--(26): a fixed encoding in register order seq, par, stat. Shape index is the lower-row length; state index is s. The theorem supplies all range bounds before using the finite-bit conversions, so their modular totalization does not identify valid labels. This definition makes no assertion about a routing circuit or clean ancillas.
-- source:
--   A Practical Quantum Algorithm for the Schur Transform, arXiv:1709.07119v6, https://arxiv.org/abs/1709.07119v6

import Definitions.Def_QAlgorithms_Defs_Basic

/-!
Statements from Kirby--Strauch, arXiv:1709.07119v6.
Only the exact encoding-space node is stated in this draft. The unit's HARD.md
and GAPS.json record the other seven main nodes. No claim about a compiled
Schur circuit is replaced by a purely numerical gate-count inequality.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P10

attribute [local instance] Classical.propDecidable

/-- PDF p.13, the tableau insertion description preceding (26): the number
of lower-row insertions among the first `k` boxes. A false bit means upper
row, and a true bit means lower row. -/
def prefixBottomCount {n : ℕ} (p : Qubits n) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i => i.val < k ∧ p i = true).card

/-- PDF pp.4,13: a standard tableau with at most two rows, recorded by the
row receiving each successive entry 1,...,n. Every prefix must have at least
as many upper-row as lower-row entries. Empty rows are allowed. -/
def IsTableauWord {n : ℕ} (p : Qubits n) : Prop :=
  ∀ k : Fin (n + 1), 2 * prefixBottomCount p k.val ≤ k.val

/-- PDF pp.4,11,13, (11), (21), (26): all standard tableaux of shape
(n-m,m). This is the full multiplicity-label set, rather than a bound
supplied as an assumption. -/
abbrev TwoRowTableau (n m : ℕ) :=
  {p : Qubits n // IsTableauWord p ∧ hammingWeight p = m}

/-- PDF pp.4,11--13: a Schur basis label consists of a standard two-row
tableau p and a state s in the corresponding spin-j irrep, where
2j = n - 2 * hammingWeight p and s = 0,...,2j (spin projection j-s).
The ambient Fin(n+1) only makes the finite label type explicit; the
predicate restricts s to precisely its own irrep. -/
abbrev QubitSchurLabel (n : ℕ) :=
  {a : Qubits n × Fin (n + 1) //
    IsTableauWord a.1 ∧ a.2.val < n - 2 * hammingWeight a.1 + 1}

/-- PDF p.13, (26): chosen multiplicity-register allocation, for n >= 2.
Its total-function value below that domain is not a physical space claim. -/
def seqSize (n : ℕ) : ℕ := n - 2

/-- PDF p.13, (24): the number of bits needed for all floor(n/2)+1 shapes. -/
def parSize (n : ℕ) : ℕ := Nat.clog 2 (n / 2 + 1)

/-- PDF p.13, (25): the number of bits needed for the largest irrep, of
shape (n,0) and dimension n+1. -/
def statSize (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

/-- PDF pp.10,14, (20), (27): actual allocated wires, summed in register
order seq, par, stat, before simplifying the expression. -/
def totalSize (n : ℕ) : ℕ := seqSize n + (parSize n + statSize n)

/-- PDF p.14, (27): ancillary overhead computed from the allocation,
rather than defined to be the expression asserted in the theorem. -/
def ancillaSize (n : ℕ) : ℕ := totalSize n - n

/-- PDF pp.11,13 permits a calculable, noncanonical order of the copies.
Fix that order by retaining the row choices for entries 2,...,n-1.
For a fixed final shape, entry 1 is in the upper row and the final entry's
row is recovered from the total lower-row count. Unused words are ghosts.
The branch merely totalizes the definition for n < 2. -/
def seqWord {n : ℕ} (p : Qubits n) : Qubits (seqSize n) :=
  fun i => if h : i.val + 1 < n then p ⟨i.val + 1, h⟩ else false

/-- PDF pp.10--13, (20), (24)--(26): a fixed encoding in register order
seq, par, stat. Shape index is the lower-row length; state index is s.
The theorem supplies all range bounds before using the finite-bit
conversions, so their modular totalization does not identify valid labels.
This definition makes no assertion about a routing circuit or clean ancillas. -/
def labelEncoding {n : ℕ} (a : QubitSchurLabel n) : Qubits (totalSize n) :=
  Fin.append (seqWord a.val.1)
    (Fin.append (natToBits (parSize n) (hammingWeight a.val.1))
      (natToBits (statSize n) a.val.2.val))

/-- Sanity: an all-upper-row word has no lower-row insertions. -/
example (n k : ℕ) : prefixBottomCount (fun _ : Fin n => false) k = 0 := by
  simp [prefixBottomCount]

/-- Sanity: the single-row tableau is admissible at every size. -/
example (n : ℕ) : IsTableauWord (fun _ : Fin n => false) := by
  intro k
  simp [prefixBottomCount]

/-- Sanity: two qubits have allocation (seq,par,stat) = (0,1,2). -/
example : seqSize 2 = 0 ∧ parSize 2 = 1 ∧ statSize 2 = 2 ∧
    totalSize 2 = 3 ∧ ancillaSize 2 = 1 := by decide

/-- Sanity: four qubits have allocation (2,2,3), total 7, overhead 3. -/
example : seqSize 4 = 2 ∧ parSize 4 = 2 ∧ statSize 4 = 3 ∧
    totalSize 4 = 7 ∧ ancillaSize 4 = 3 := by decide

/-- Sanity: at two qubits there is no internal tableau row choice. -/
example (p q : Qubits 2) : seqWord p = seqWord q := by
  funext i
  exact Fin.elim0 i

end QAlgorithms.Papers.Independent.Next46.P10


