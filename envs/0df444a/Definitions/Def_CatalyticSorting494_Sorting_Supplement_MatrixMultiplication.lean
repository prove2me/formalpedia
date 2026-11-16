-- Prove2me | Definitions.Def_CatalyticSorting494_Sorting_Supplement_MatrixMultiplication
-- name    : CatalyticSorting494_Sorting_Supplement_MatrixMultiplication
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:18:02.852377+00:00
-- url     : https://prove2.me/theorems/2b643ee5-486e-4181-977f-bf708995cb36
-- title:
--   Definition 4.10 — the matrix multiplication exponent $\omega$ (complex circuits with division), and matrix encodings
-- statement:
--   An **arithmetic circuit with division** over $\mathbb C$ in the $2n^2$ indeterminates $a_{ij},b_{jk}$ ($i,j,k\in[n]$) is a sequence of gates, each a constant $c\in\mathbb C$, an indeterminate, or the sum, difference, product or quotient of two earlier gates; no gate divides by the zero rational function. Each gate computes a rational function in $\mathbb C(a_{ij},b_{jk})$. Its **size** is its number of gates. It **multiplies $n\times n$ matrices** if for all $i,k$ some gate computes $\sum_j a_{ij}b_{jk}$. The **matrix multiplication exponent** is
--
--   $$\omega=\inf\bigl\{r\in\mathbb R:\ \exists A\ \forall n\ge1\ \text{some circuit of size}\le A\,n^r\ \text{multiplies } n\times n \text{ matrices}\bigr\}.$$
--
--   The set is nonempty ($r=3$, schoolbook) and bounded below, so the infimum is a genuine real number.
--
--   For the algorithmic statement, a pair $X,Y$ of $n\times n$ matrices with natural entries at most $(n+1)^p$ is written on the input tape as a unary field width $L$, then $n$ and the entry width $b=\lfloor\log_2 (n+1)^p\rfloor+1$ in binary fields of width $L$, then the entries of $X$ and of $Y$ in row-major order as $b$-bit fields. The required output is the integer product $XY$, entries in row-major order as fields of $\lfloor\log_2(n(n+1)^{2p})\rfloor+1$ bits, which suffices since every entry is at most $n(n+1)^{2p}$.
--
--   $\omega$ is the exponent of Theorem 1.4.
--
--   **Formalization Note** Rational functions live in the fraction field of $\mathbb C[a_{ij},b_{jk}]$. The published `OAI_MatrixMultiplication_Arithmetic_omega` and `LinSysAmp_omegaAlg` are not reused: they have no division gates and count operations, while Definition 4.10 allows division (footnote 12) and counts size; the values agree only by Strassen's division-elimination theorem. Binary fields are least significant bit first, as in the base mission.
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Definition 4.10 with footnote 12, printed p.18 (PDF p.19); matrix input of Theorem 1.4, printed p.3 (PDF p.4)

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine

namespace CatalyticSorting494.Sorting.Supplement

open CatalyticSorting494.Sorting

/-- The `2n²` indeterminates: `inl (i, j)` is the entry `a_{ij}` of the first matrix and
`inr (j, k)` the entry `b_{jk}` of the second. -/
abbrev MatVar (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

/-- Rational functions over `ℂ` in the `2n²` indeterminates. -/
abbrev MatRatFunc (n : ℕ) := FractionRing (MvPolynomial (MatVar n) ℂ)

/-- A gate of an arithmetic circuit over `ℂ` with division gates (Definition 4.10, footnote 12):
a constant, an input indeterminate, or `+`, `−`, `×`, `÷` of two earlier gates, named by position. -/
inductive DivGate (n : ℕ) where
  | const (c : ℂ)
  | input (v : MatVar n)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  | div (i j : ℕ)

namespace DivGate

variable {n : ℕ}

/-- The gates a gate reads. -/
def args : DivGate n → List ℕ
  | const _ => []
  | input _ => []
  | add i j => [i, j]
  | sub i j => [i, j]
  | mul i j => [i, j]
  | div i j => [i, j]

/-- The rational function computed by a gate, given those of the earlier gates. -/
noncomputable def value (vals : List (MatRatFunc n)) : DivGate n → MatRatFunc n
  | const c => algebraMap (MvPolynomial (MatVar n) ℂ) (MatRatFunc n) (MvPolynomial.C c)
  | input v => algebraMap (MvPolynomial (MatVar n) ℂ) (MatRatFunc n) (MvPolynomial.X v)
  | add i j => vals.getD i 0 + vals.getD j 0
  | sub i j => vals.getD i 0 - vals.getD j 0
  | mul i j => vals.getD i 0 * vals.getD j 0
  | div i j => vals.getD i 0 / vals.getD j 0

end DivGate

/-- A non-uniform arithmetic circuit over `ℂ` with division gates for `n × n` matrix multiplication:
its gates in topological order, and for each entry `(i, k)` of the product the gate computing it. -/
structure DivCircuit (n : ℕ) where
  gates : List (DivGate n)
  output : Fin n → Fin n → ℕ

namespace DivCircuit

variable {n : ℕ}

/-- The rational functions computed by all gates, in order. -/
noncomputable def values (C : DivCircuit n) : List (MatRatFunc n) :=
  C.gates.foldl (fun vals g => vals ++ [g.value vals]) []

/-- The size of the circuit: its number of gates. -/
def size (C : DivCircuit n) : ℕ := C.gates.length

/-- A well-formed circuit: every gate reads only strictly earlier gates, no gate divides by the
zero rational function, and every output names a gate. -/
structure Valid (C : DivCircuit n) : Prop where
  args_lt : ∀ (k : ℕ) (g : DivGate n), C.gates[k]? = some g → ∀ a ∈ g.args, a < k
  div_ne_zero : ∀ (k i j : ℕ), C.gates[k]? = some (DivGate.div i j) → C.values.getD j 0 ≠ 0
  output_lt : ∀ i k, C.output i k < C.gates.length

/-- The circuit multiplies `n × n` matrices: for all `i, k`, its output gate for `(i, k)` computes
`∑ⱼ a_{ij} b_{jk}` as a rational function of the `2n²` indeterminates. -/
def ComputesProduct (C : DivCircuit n) : Prop :=
  C.Valid ∧ ∀ i k : Fin n, C.values.getD (C.output i k) 0 =
    algebraMap (MvPolynomial (MatVar n) ℂ) (MatRatFunc n)
      (∑ j : Fin n, MvPolynomial.X (Sum.inl (i, j)) * MvPolynomial.X (Sum.inr (j, k)))

end DivCircuit

/-- `n × n` complex matrices can be multiplied by arithmetic circuits of size `O(n^r)`: one constant
`A` with a circuit of size at most `A · n^r` for every `n ≥ 1`. -/
def MatMulAdmissible (r : ℝ) : Prop :=
  ∃ A : ℝ, ∀ n : ℕ, 1 ≤ n → ∃ C : DivCircuit n, C.ComputesProduct ∧ (C.size : ℝ) ≤ A * (n : ℝ) ^ r

/-- The matrix multiplication exponent `ω` (Definition 4.10): the infimum of all real `r` such that
`n × n` matrices over `ℂ` can be multiplied by arithmetic circuits (with division gates) of size
`O(n^r)`. The set is nonempty (the schoolbook circuit gives `r = 3`) and bounded below (a circuit
for `n ≥ 1` has at least one gate, so `r < 0` is impossible), so the infimum is the genuine one. -/
noncomputable def omega : ℝ := sInf {r : ℝ | MatMulAdmissible r}

/-- The entries of a matrix in row-major order, each as a binary field of width `b`, least
significant bit first. -/
def rowMajorBits {n : ℕ} (b : ℕ) (X : Matrix (Fin n) (Fin n) ℕ) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j => natBits b (X i j)

/-- The field width for entries in `{0, …, (n + 1)^p}`. -/
def entryWidth (n p : ℕ) : ℕ := Nat.log 2 ((n + 1) ^ p) + 1

/-- The field width for entries of a product of two such matrices, which lie in
`{0, …, n (n + 1)^{2p}}`. -/
def productWidth (n p : ℕ) : ℕ := Nat.log 2 (n * (n + 1) ^ (2 * p)) + 1

/-- The content of the input tape for the pair `(X, Y)` of `n × n` matrices with entries in
`{0, …, (n + 1)^p}`: a field width `L` in unary, then `n` and the entry width `b` in binary fields of
width `L`, then the entries of `X` and of `Y` in row-major order, each as `b` bits. -/
def encodeMatrices (n p : ℕ) (X Y : Matrix (Fin n) (Fin n) ℕ) : List Bool :=
  let b := entryWidth n p
  let L := Nat.log 2 (n + b) + 1
  List.replicate L true ++ [false] ++ natBits L n ++ natBits L b ++ rowMajorBits b X ++
    rowMajorBits b Y

/-- The required output: the entries of the integer product `X Y` in row-major order, each as
`productWidth n p` bits. -/
def productOutput (n p : ℕ) (X Y : Matrix (Fin n) (Fin n) ℕ) : List Bool :=
  rowMajorBits (productWidth n p) (X * Y)

end CatalyticSorting494.Sorting.Supplement


