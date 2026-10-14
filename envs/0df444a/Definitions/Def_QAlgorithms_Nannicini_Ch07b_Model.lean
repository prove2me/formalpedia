-- Prove2me | Definitions.Def_QAlgorithms_Nannicini_Ch07b_Model
-- name    : QAlgorithms_Nannicini_Ch07b_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:51:31.199216+00:00
-- url     : https://prove2.me/theorems/b7530a7d-7494-4106-95e9-49aa2ffc473c
-- title:
--   Nannicini Ch07b: supporting definitions
-- statement:
--   Nannicini, Chapter 7 (second part): block-encodings, Gibbs states, trace estimation
--
--   ## QAlgorithms.Nannicini.traceNorm
--
--   For any finite index type with decidable equality and arbitrary complex square matrix $A$ indexed by it, this is $\sum_{k=0}^{N-1}\sqrt{\lambda_k(A^*A)}$, where $N$ is the index cardinality. The eigenvalue function used here returns Hermitian eigenvalues with the library enumeration reversed for a Hermitian matrix and zero otherwise; $A^*A$ is Hermitian. Square root is the total real square root, returning zero on negative inputs. An empty index type gives sum zero, and no unitarity or invertibility assumption is imposed.
--
--   ## QAlgorithms.Nannicini.qramOp
--
--   For all natural numbers $b,r$ and maps $M$ from $b$-bit to $r$-bit strings, this complex square matrix on $b+r$ wires sends $|j,z\rangle$ to $|j,z\mathbin{\oplus}M(j)\rangle$. Its row $(j',z')$, column $(j,z)$ entry is one exactly when $j'=j$ and $z'=z\mathbin{\oplus}M(j)$, and zero otherwise, with the first $b$ bits the address and final $r$ the target. Either register can be empty.
--
--   ## QAlgorithms.Nannicini.ArithOp
--
--   This instruction type consists of rational constants; binary addition, subtraction, multiplication, and division with two natural operand indices; unary square root and arccosine with one natural operand index; and complex argument with two natural operand indices. No bounds or operand-domain conditions are part of the type.
--
--   ## QAlgorithms.Nannicini.ArithOp.value
--
--   Given a finite real list, let $v_i$ denote its zero-based entry at natural index $i$, with zero returned outside the list. A rational constant evaluates to its real coercion; other operation values are $v_i+v_j$, $v_i-v_j$, $v_iv_j$, $v_i/v_j$, $\sqrt{v_i}$, $\arccos(v_i)$, and the principal argument of $v_i+\mathrm{i}v_j$, respectively. All are total operations: division by zero, negative-input square root, and argument of zero give zero, while arccosine is $\pi$ below $-1$ and zero above $1$. No index bounds or operand assumptions are required.
--
--   ## QAlgorithms.Nannicini.arithExec
--
--   For any finite arithmetic program and real input list, execute operations in list order, evaluating each on the full current list and appending its single result. All inputs and intermediate results remain present, and unavailable operand indices read zero, including indices of future results. An empty program returns the input and no well-formedness condition is imposed.
--
--   ## QAlgorithms.Nannicini.matrixInput
--
--   For any natural number $d$ and complex $d$ by $d$ matrix $A$, this list enumerates rows in increasing order and columns within each row in increasing order, appending $\operatorname{Re}A_{ij}$ then $\operatorname{Im}A_{ij}$ for each entry. Its length is $2d^2$ and it is empty for $d=0$.
--
--   ## QAlgorithms.Nannicini.qramMatrixWords
--
--   For natural numbers $b,r,d$, a finite arithmetic program, an address map from $b$-bit strings to natural numbers, and a complex $d$ by $d$ matrix $A$, execute the program on the alternating real and imaginary parts of $A$'s entries in increasing row and column order. For each address, read the resulting list at its assigned zero-based index with missing entries zero; take natural-number floor, which gives zero on negative inputs; and encode the result modulo $2^r$ in $r$ bits, most significant first. No address bounds or accuracy condition is imposed; for $r=0$ every word is empty.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Nannicini/Ch07b.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Adiabatic
/-!
# Nannicini, Chapter 7 (second part): block-encodings, Gibbs states, trace estimation

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §7.2.4. Block-encodings are the frozen `IsBlockEncoding` (Def. 7.11, auxiliary
register first). A register of `m + k` qubits is split into its first `m` and last `k` qubits by
`qubitsAppendEquiv m k`. `Õ(g)` (Def. 1.11, p.11) is unfolded as `C · g · polylog`, with the
constants `C, c` quantified before every parameter.
-/

namespace QAlgorithms.Nannicini




/-- Nannicini p.170, Definition 7.31 (trace norm): `‖A‖_Tr = Tr √(A†A)`, the sum of the singular
values of `A`, i.e. of the square roots of the eigenvalues of the Hermitian matrix `A†A`. -/
noncomputable def traceNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  ∑ k, Real.sqrt (ascEigenvalues (A.conjTranspose * A) k)


/-- Nannicini p.128, Definition 5.39 (QRAM), for the statement of Prop. 7.29 (chunk-local copy of
the object of the Cor. 5.45 chunk, which a chunk may not import): for stored words
`M_j ∈ {0,1}^r`, `U_QRAM |j⟩|y⟩ = |j⟩|y ⊕ M_j⟩` for all addresses `j ∈ {0,1}^b`,
`y ∈ {0,1}^r`. Address register first. Its size in the sense of Def. 5.39 is `2^b · r`. -/
noncomputable def qramOp (b r : ℕ) (M : Qubits b → Qubits r) :
    Matrix (Qubits (b + r)) (Qubits (b + r)) ℂ :=
  Matrix.reindex (qubitsAppendEquiv b r).symm (qubitsAppendEquiv b r).symm (xorOracle M)

/-- One classical arithmetic operation: the cost model for "`Õ(d²)` classical arithmetic
operations to initialize the QRAM data structures" of Nannicini p.168, Prop. 7.29, which the
source does not define (chunk-local copy of the model of the Cor. 5.45 chunk). A program is a
straight-line program over the reals: each instruction reads earlier values by index and appends
one new value; each counts as one operation. The operations are those of the preprocessing of
Cor. 5.45 (p.124, p.129–130), run for the `d` columns and the vector of column norms (p.168–169):
`+, −, ×, ÷, √, arccos`, the argument of a complex number, and rational constants. -/
inductive ArithOp where
  | const (c : ℚ)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  | div (i j : ℕ)
  | sqrt (i : ℕ)
  | arccos (i : ℕ)
  | arg (i j : ℕ)

/-- The value an instruction appends, given the values computed so far (an out-of-range index
reads `0`; `t / 0 = 0` as in Lean). `arg i j` is the argument of `vals[i] + i·vals[j]`. -/
noncomputable def ArithOp.value (vals : List ℝ) : ArithOp → ℝ
  | .const c => (c : ℝ)
  | .add i j => vals.getD i 0 + vals.getD j 0
  | .sub i j => vals.getD i 0 - vals.getD j 0
  | .mul i j => vals.getD i 0 * vals.getD j 0
  | .div i j => vals.getD i 0 / vals.getD j 0
  | .sqrt i => Real.sqrt (vals.getD i 0)
  | .arccos i => Real.arccos (vals.getD i 0)
  | .arg i j => Complex.arg ⟨vals.getD i 0, vals.getD j 0⟩

/-- All values of a straight-line program run on an input list (inputs first, then one value per
instruction). The cost of the program is its length. -/
noncomputable def arithExec (Prog : List ArithOp) (input : List ℝ) : List ℝ :=
  Prog.foldl (fun vals g => vals ++ [g.value vals]) input

/-- The classical description of `A ∈ ℂ^{d×d}` given to the preprocessing: row by row, the list
`Re a_00, Im a_00, Re a_01, Im a_01, …`. -/
noncomputable def matrixInput {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : List ℝ :=
  (List.ofFn fun i => (List.ofFn fun j => [(A i j).re, (A i j).im]).flatten).flatten

/-- The QRAM contents written by the classical preprocessing (Rem. 5.40: classical write): word
`j` is the `r`-bit binary expansion (most significant bit first) of the integer part of the
program value with index `addr j`. Storing a value is not an arithmetic operation. -/
noncomputable def qramMatrixWords (b r : ℕ) (Prog : List ArithOp) (addr : Qubits b → ℕ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : Qubits b → Qubits r :=
  fun j => natToBits r ⌊(arithExec Prog (matrixInput A)).getD (addr j) 0⌋₊


end QAlgorithms.Nannicini


