-- Prove2me | Definitions.Def_SingleInteraction_Supplement_LocalHam
-- name    : SingleInteraction_Supplement_LocalHam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:04:12.981198+00:00
-- url     : https://prove2.me/theorems/465b0e0f-e704-4687-8fba-37ff3e48e058
-- title:
--   $k$-Local Hamiltonian instances (Definition 6, Lemma 57)
-- statement:
--   A **$k$-Local Hamiltonian instance** on $n$ qubits is a list of $M$ terms $H_1,\dots,H_M$, each a Hermitian matrix acting on an ordered list of at most $k$ distinct qubits (and as the identity elsewhere), with entries given as Gaussian binary rationals, together with thresholds $a,b$; its Hamiltonian is $H=\sum_{i=1}^MH_i$. It satisfies the assumptions of Lemma 57 at exponent $c$ when
--   $$M\le(n+1)^c,\qquad\|H_i\|\le(n+1)^c,\qquad\text{every entry has at most }(n+1)^c\text{ bits.}$$
--   An accuracy $\varepsilon>0$ is admissible when it has at most $(n+1)^c$ bits and $1/\varepsilon\le(n+1)^c$.
--
--   This is the input of the universal reduction, Theorem 58.
--
--   **Formalization Note** A term on qubits $(v_1,\dots,v_j)$ is a $2^j\times2^j$ table of rows; the row index of a basis state is its binary value with $v_1$ most significant. The gap $b-a$ is not part of this validity: Theorem 58 assumes $0<\varepsilon\le(b-a)/4$ instead.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 6, pp.17–18; Lemma 57, p.50; Theorem 58, p.52

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_SingleInteraction_onTuple

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-!
# k-Local Hamiltonian instances (Definition 6, Lemma 57)

Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version,
sha256 19ddc444…), Definition 6, p.17: "A set of `m = poly(n)` Hermitian matrices `H1, . . . , Hm`
acting on a system of `n` qubits. Each term `Hi` acts nontrivially on at most `k` qubits, satisfies
the operator norm bound `∥Hi∥ ≤ poly(n)` and its entries are specified by `poly(n)` bits. […]
Additionally, the input includes two real numbers `a` and `b`"; Lemma 57, p.50 (`M = poly(n)`,
`∥Hi∥ ≤ B = poly(n)`).

**Formalization Note**
* A term is an ordered list `(v1, …, vj)` of `j ≤ k` distinct qubits in `{0, …, n−1}` and a
  `2^j × 2^j` matrix of Gaussian binary rationals (pairs `(re, im)`), given as a list of rows. The
  row/column index of a basis state `s` of the `j` qubits is `Σ_i s_i 2^{j−1−i}` (qubit `v1` most
  significant); the term acts on the system as that matrix on `(v1, …, vj)` (`onTuple`) and as the
  identity elsewhere.
* Validity at exponent `c`: at most `(n+1)^c` terms, each Hermitian with operator norm at most
  `(n+1)^c` and every entry of at most `(n+1)^c` bits (positive denominators). The thresholds `a, b`
  are binary rationals with positive denominators; their gap is not part of `LHValid` (Theorem 58's
  promise clause assumes `0 < ε ≤ (b−a)/4` instead).
* "`ε` specified with `poly(n)` bits, `1/ε = O(poly(n))`" is `EpsValid c n ε`. -/

/-- A `k`-Local Hamiltonian instance: `n`, the terms, and the thresholds `a, b`. -/
structure LHInstance where
  n : ℕ
  terms : List (List ℕ × List (List (BinaryRational × BinaryRational)))
  a : BinaryRational
  b : BinaryRational

/-- Equivalence used to build the code. -/
def lhInstanceEquiv : LHInstance ≃
    ℕ × (List (List ℕ × List (List (BinaryRational × BinaryRational))) ×
      (BinaryRational × BinaryRational)) where
  toFun x := (x.n, x.terms, x.a, x.b)
  invFun y := ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨a, b, c, d⟩; rfl

/-- The code of an instance (`n` in unary). -/
def lhCodec : Codec LHInstance :=
  BinaryEncoding.equiv (pair unary (pair (BinaryEncoding.list (pair (BinaryEncoding.list natural)
    (BinaryEncoding.list (BinaryEncoding.list (pair binaryRationalCodec binaryRationalCodec)))))
    (pair binaryRationalCodec binaryRationalCodec))) lhInstanceEquiv

/-- The value `re + im·i` of a Gaussian binary rational. -/
def gaussValue (e : BinaryRational × BinaryRational) : ℂ :=
  (e.1.value : ℂ) + (e.2.value : ℂ) * Complex.I

/-- The row/column index `Σ_i s_i 2^{j−1−i}` of a basis state of `j` qubits. -/
def basisIndex {j : ℕ} (s : Fin j → Fin 2) : ℕ :=
  ∑ i : Fin j, (s i : ℕ) * 2 ^ (j - 1 - (i : ℕ))

/-- The local matrix of a term on its own qubits. -/
def termMatrix (l : List ℕ) (rows : List (List (BinaryRational × BinaryRational))) :
    Matrix (Fin l.length → Fin 2) (Fin l.length → Fin 2) ℂ :=
  fun s t => gaussValue ((rows.getD (basisIndex s) []).getD (basisIndex t) (⟨0, 1⟩, ⟨0, 1⟩))

/-- The term acting on the `n`-qubit system (`0` if a qubit index is out of range). -/
noncomputable def lhTerm (n : ℕ) (term : List ℕ × List (List (BinaryRational × BinaryRational))) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  if hl : ∀ q : Fin term.1.length, term.1.get q < n then
    onTuple (termMatrix term.1 term.2) (fun q => ⟨term.1.get q, hl q⟩)
  else 0

/-- `H = Σ_i H_i`. -/
noncomputable def lhHam (x : LHInstance) : Matrix (Fin x.n → Fin 2) (Fin x.n → Fin 2) ℂ :=
  (x.terms.map (lhTerm x.n)).sum

/-- Validity of a `k`-Local Hamiltonian instance at exponent `c` (Definition 6, Lemma 57). -/
def LHValid (k c : ℕ) (x : LHInstance) : Prop :=
  x.terms.length ≤ (x.n + 1) ^ c ∧
    (∀ term ∈ x.terms,
      term.1.length ≤ k ∧ (∀ v ∈ term.1, v < x.n) ∧ term.1.Nodup ∧
      term.2.length = 2 ^ term.1.length ∧ (∀ row ∈ term.2, row.length = 2 ^ term.1.length) ∧
      (termMatrix term.1 term.2).IsHermitian ∧
      SYKEdge.opNorm (termMatrix term.1 term.2) ≤ ((x.n : ℝ) + 1) ^ c ∧
      ∀ row ∈ term.2, ∀ e ∈ row, 0 < e.1.denominator ∧ 0 < e.2.denominator ∧
        (binaryRationalCodec.encode e.1).length ≤ (x.n + 1) ^ c ∧
        (binaryRationalCodec.encode e.2).length ≤ (x.n + 1) ^ c) ∧
    0 < x.a.denominator ∧ 0 < x.b.denominator

/-- `ε > 0` with at most `(n+1)^c` bits and `1/ε ≤ (n+1)^c`. -/
def EpsValid (c n : ℕ) (ε : BinaryRational) : Prop :=
  0 < ε.denominator ∧ 0 < (ε.value : ℝ) ∧ (binaryRationalCodec.encode ε).length ≤ (n + 1) ^ c ∧
    (ε.value : ℝ)⁻¹ ≤ ((n : ℝ) + 1) ^ c

end Supplement

end SingleInteraction


