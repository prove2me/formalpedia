-- Prove2me | Definitions.Def_QAlgorithms_Nannicini_Ch07a_Model
-- name    : QAlgorithms_Nannicini_Ch07a_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:46:33.053004+00:00
-- url     : https://prove2.me/theorems/1087486e-4fb3-4de8-b3d8-26571966448b
-- title:
--   Nannicini Ch07a: supporting definitions
-- statement:
--   Nannicini, Chapter 7 (part a): iterative refinement and operations on block-encodings
--
--   ## QAlgorithms.Nannicini.oneTwoQubitGateSet
--
--   This set consists exactly of gates whose natural arity is one or two and whose complex square matrix on strings of that arity belongs to the corresponding unitary group. Both conditions are required; no finite generating collection is specified.
--
--   ## QAlgorithms.Nannicini.sparseRowSupport
--
--   For any natural number $q$, arbitrary complex $2^q$ by $2^q$ matrix $A$, and valid row index $i$, this finite set consists exactly of column indices $j$ such that $A_{ij}\ne0$. No sparsity assumption is imposed; $q=0$ gives a one-by-one matrix.
--
--   ## QAlgorithms.Nannicini.sparseColSupport
--
--   For any natural number $q$, arbitrary complex $2^q$ by $2^q$ matrix $A$, and valid column index $j$, this finite set consists exactly of row indices $i$ such that $A_{ij}\ne0$. It may be empty or the entire index set; no sparsity assumption is imposed.
--
--   ## QAlgorithms.Nannicini.sparseRowIndex
--
--   For any natural number $q$, arbitrary complex $2^q$ by $2^q$ matrix $A$, valid row $i$, and natural number $k$, form the set of columns where row $i$ is nonzero. If $k$ is strictly smaller than its cardinality, return the natural-number value of its $k$th element in increasing column order, counting from zero; otherwise return $k+2^q$. An empty row always uses the latter branch, whose result lies outside the valid column range.
--
--   ## QAlgorithms.Nannicini.sparseColIndex
--
--   For any natural number $q$, arbitrary complex $2^q$ by $2^q$ matrix $A$, valid column $j$, and natural number $l$, form the set of rows where column $j$ is nonzero. If $l$ is strictly smaller than its cardinality, return the natural-number value of its $l$th element in increasing row order, counting from zero; otherwise return $l+2^q$. An empty column always uses the latter branch, whose result lies outside the valid row range.
--
--   ## QAlgorithms.Nannicini.sparseOracleArity
--
--   For any natural numbers $q,p$, this function on labels $0,1,2$ assigns arity $(q+1)+(q+1)$ to zero and one and arity $q+q+p$ to two. Zero values of $q$ or $p$ are allowed.
--
--   ## QAlgorithms.Nannicini.sparseOracles
--
--   For natural numbers $q,p$, arbitrary complex square matrices $O_r,O_c$ on $2q+2$ wires, and an arbitrary complex square matrix $O_A$ on $2q+p$ wires, this dependent family returns $O_r$ at label zero, $O_c$ at label one, and $O_A$ at label two, with those respective arities. No unitarity or other matrix property is required.
--
--   ## QAlgorithms.Nannicini.OracleStep.IsUseOf
--
--   For any gate set $S$, natural numbers $r,n$, arity assignment on $r$ oracle labels, selected label $k$ and Boolean adjoint flag, this Boolean function is false on ordinary gate steps and true on a query exactly when both its label equals $k$ and its adjoint flag equals the supplied flag. The optional control and injective wire assignment do not affect this test. A selected label exists only when $r>0$.
--
--   ## QAlgorithms.Nannicini.OracleStep.IsControlledQuery
--
--   For any gate set $S$, natural numbers $r,n$, and arity assignment on $r$ oracle labels, this Boolean function is false on an ordinary gate step and true on a query exactly when its optional control wire is present. The label, adjoint flag, and query wires do not affect the test; a present control is already required by the step type to lie outside the query-wire image.
--
--   ## QAlgorithms.Nannicini.sparseBERegEquiv
--
--   For any natural numbers $q,m$, this equivalence splits a bit string of length $(q+3+m)+q$ into the nested pair $((u,v),w)$, taking the first $q+3$ bits for $u$, the next $m$ for $v$, and the last $q$ for $w$. Its inverse concatenates the three registers in that order; $v$ or $w$ may be empty.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Nannicini/Ch07a.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_BlockEncoding
/-!
# Nannicini, Chapter 7 (part a): iterative refinement and operations on block-encodings

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages): Proposition 7.9 (p.158), Proposition 7.14 (p.160), Proposition 7.18 (pp.161–162),
Lemma 7.20 (p.163), Proposition 7.21 (p.164, stated in corrected form: the cost of the final
rotation and the encoding of the entries are explicit parameters).

Block-encodings are the frozen `IsBlockEncoding` (Defs. 7.10–7.11, auxiliary register first,
spectral norm). An auxiliary register made of several sub-registers is a product type in the
source's register order (Rem. 7.15: `|·⟩_a |·⟩_b |·⟩_q`), its all-zero state the pair of zero
strings.
-/

namespace QAlgorithms.Nannicini





/-- The gate set "one and two-qubit gates" of Nannicini Prop. 7.21 (p.164): every unitary
gate on one or two qubits. -/
def oneTwoQubitGateSet : Set Gate :=
  {g | (g.arity = 1 ∨ g.arity = 2) ∧ g.IsUnitary}

/-- The column indices of the nonzero entries of row `i` of `A` (Nannicini p.164). -/
noncomputable def sparseRowSupport {q : ℕ} (A : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ)
    (i : Fin (2 ^ q)) : Finset (Fin (2 ^ q)) :=
  open Classical in Finset.univ.filter fun j => A i j ≠ 0

/-- The row indices of the nonzero entries of column `j` of `A` (Nannicini p.164). -/
noncomputable def sparseColSupport {q : ℕ} (A : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ)
    (j : Fin (2 ^ q)) : Finset (Fin (2 ^ q)) :=
  open Classical in Finset.univ.filter fun i => A i j ≠ 0

/-- Nannicini p.164, `r_ik`: the index of the `k`-th (zero-based, increasing order) nonzero
entry of row `i` of `A`, or `k + 2^q` if row `i` has no `k`-th nonzero entry (Example 7.23,
p.166: row 0 with nonzeros in columns 1, 2 gives `r_{0,2} = 2 + 4`). -/
noncomputable def sparseRowIndex {q : ℕ} (A : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ)
    (i : Fin (2 ^ q)) (k : ℕ) : ℕ :=
  if h : k < (sparseRowSupport A i).card then
    ((sparseRowSupport A i).orderEmbOfFin rfl ⟨k, h⟩ : ℕ)
  else k + 2 ^ q

/-- Nannicini p.164, `c_ℓj`: the index of the `ℓ`-th (zero-based, increasing order) nonzero
entry of column `j` of `A`, or `ℓ + 2^q` if column `j` has no `ℓ`-th nonzero entry. -/
noncomputable def sparseColIndex {q : ℕ} (A : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ)
    (j : Fin (2 ^ q)) (l : ℕ) : ℕ :=
  if h : l < (sparseColSupport A j).card then
    ((sparseColSupport A j).orderEmbOfFin rfl ⟨l, h⟩ : ℕ)
  else l + 2 ^ q

/-- The arities of the three oracles of Nannicini Prop. 7.21 (p.164): `O_r` and `O_c` act on
two `(q + 1)`-qubit registers, `O_A` on two `q`-qubit index registers and a `p`-qubit value
register. -/
def sparseOracleArity (q p : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => (q + 1) + (q + 1)
  | ⟨1, _⟩ => (q + 1) + (q + 1)
  | ⟨_ + 2, _⟩ => q + q + p

/-- The oracle family `(O_r, O_c, O_A)` of Nannicini Prop. 7.21, indexed by `0, 1, 2`. -/
def sparseOracles {q p : ℕ} (Or Oc : Matrix (Qubits ((q + 1) + (q + 1))) (Qubits ((q + 1) + (q + 1))) ℂ)
    (OA : Matrix (Qubits (q + q + p)) (Qubits (q + q + p)) ℂ) :
    (k : Fin 3) → Matrix (Qubits (sparseOracleArity q p k)) (Qubits (sparseOracleArity q p k)) ℂ
  | ⟨0, _⟩ => Or
  | ⟨1, _⟩ => Oc
  | ⟨_ + 2, _⟩ => OA

/-- A step that queries oracle `k`, as the oracle itself (`adj = false`) or as its adjoint
(`adj = true`). -/
def OracleStep.IsUseOf {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ} (k : Fin r) (adj : Bool) :
    OracleStep S a n → Bool
  | .gate _ => false
  | .query k' adj' _ _ _ => decide (k' = k ∧ adj' = adj)

/-- A controlled oracle query. -/
def OracleStep.IsControlledQuery {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ} :
    OracleStep S a n → Bool
  | .gate _ => false
  | .query _ _ c _ _ => c.isSome

/-- The register order `(auxiliary q + 3 qubits, workspace m qubits, system q qubits)` of a
`(q + 3 + m) + q`-qubit circuit. -/
def sparseBERegEquiv (q m : ℕ) : Qubits ((q + 3 + m) + q) ≃ (Qubits (q + 3) × Qubits m) × Qubits q :=
  (qubitsAppendEquiv (q + 3 + m) q).trans ((qubitsAppendEquiv (q + 3) m).prodCongr (Equiv.refl _))


end QAlgorithms.Nannicini


