-- Prove2me | Definitions.Def_QAlgorithms_Nannicini_Ch05c_Model
-- name    : QAlgorithms_Nannicini_Ch05c_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:45:02.569025+00:00
-- url     : https://prove2.me/theorems/0d2458d7-2444-4ba5-a825-87950a6e3b92
-- title:
--   Nannicini Ch05c: supporting definitions
-- statement:
--   Nannicini, Chapter 5 (part c): encoding an arbitrary vector in a quantum state
--
--   ## QAlgorithms.Nannicini.uncontrolledStep
--
--   For any gate set $S$, natural numbers $r,n$, and arity assignment $a$ on $r$ oracle labels, this predicate on circuit steps is true for every ordinary gate step and true for a query step exactly when its optional control wire is absent. The label, adjoint flag, and injective assignment of query wires do not otherwise affect the predicate.
--
--   ## QAlgorithms.Nannicini.qramUnitary
--
--   For all natural numbers $a,q$ and every map $M$ from $a$-bit to $q$-bit strings, this complex matrix on $a+q$ wires sends $|j,z\rangle$ to $|j,z\mathbin{\oplus}M(j)\rangle$, with the first $a$ bits the address and final $q$ bits the target, and XOR coordinatewise. Its row $(j',z')$, column $(j,z)$ entry is one exactly when $j'=j$ and $z'=z\mathbin{\oplus}M(j)$, and zero otherwise. Either register may be empty.
--
--   ## QAlgorithms.Nannicini.ArithInstr
--
--   This instruction type consists of a rational constant; addition, subtraction, multiplication, or division with two natural-number operand indices; square root or arccosine with one such index; and complex argument with two such indices. No operand bounds or numerical-domain conditions are imposed.
--
--   ## QAlgorithms.Nannicini.ArithInstr.value
--
--   Given a finite real list, let $v_i$ be its zero-based entry at natural index $i$, defaulting to zero outside the list. The value of a rational constant is its real coercion; the other instruction values are $v_i+v_j$, $v_i-v_j$, $v_iv_j$, $v_i/v_j$, $\sqrt{v_i}$, $\arccos(v_i)$, and the principal argument of $v_i+\mathrm{i}v_j$, respectively. These operations are total: division by zero, square root of a negative input, and argument of zero return zero, while arccosine is $\pi$ below $-1$ and zero above $1$. No index or operand preconditions are assumed.
--
--   ## QAlgorithms.Nannicini.arithRun
--
--   For any finite instruction program and finite real input list, execute instructions in their listed order, evaluating each on the entire current list and appending its single real result. Operand indices are zero-based and read zero when not currently present, including references to unavailable future values. The output retains all inputs and intermediate results; an empty program returns the input.
--
--   ## QAlgorithms.Nannicini.complexInput
--
--   For any natural number $d$ and complex vector $x$ with $d$ coordinates, this real list is $[\operatorname{Re}x_0,\operatorname{Im}x_0,\ldots,\operatorname{Re}x_{d-1},\operatorname{Im}x_{d-1}]$ in increasing coordinate order. Its length is $2d$, and it is empty for $d=0$.
--
--   ## QAlgorithms.Nannicini.qramWords
--
--   For natural numbers $a,q,d$, a finite arithmetic program $P$, an address map from $a$-bit strings to natural numbers, and a complex $d$-coordinate vector $x$, execute $P$ on the alternating list of real and imaginary parts of $x$. At each address read the final list at its assigned zero-based index, defaulting to zero if absent; take natural-number floor, which maps negative inputs to zero; and encode the result modulo $2^q$ as a $q$-bit string with most significant bit first. There are no address bounds or precision assumptions; $q=0$ gives the unique empty word.
--
--   ## QAlgorithms.Nannicini.IsQuantumMembershipOracle
--
--   For natural numbers $d,m,k$, any set $K$ in real $d$-dimensional Euclidean space, an encoding of $m$-bit strings into that space, real $\delta$, and complex square matrix $O$ on $m+(k+1)$ wires, this requires that $O$ be unitary and that for every address $p$ there exist a complex vector $\phi$ on $(k+1)$-bit strings such that applying $O$ to the basis vector $p$ followed by $k+1$ false bits gives amplitude $\phi(z)$ at $(p,z)$ and zero at all basis strings with different address. It also requires $1-\delta\le\sum_{z:\,(z_0=\mathrm{true}\ \leftrightarrow\ \operatorname{enc}(p)\in K)}|\phi(z)|^2$. No sign or range assumption on $\delta$, or structural assumption on $K$ or the encoding, is made; a first ancillary bit exists even for $k=0$. Norm one for $\phi$ is not separately asserted, though the unitary action and equality imply it.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Nannicini/Ch05c.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_GradientMethods
/-!
# Nannicini, Chapter 5 (part c): encoding an arbitrary vector in a quantum state

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §5.2: Proposition 5.36 (p.125) and Corollary 5.37 (p.126); and, as corrected
statements, Theorem 5.33 (p.123, §5.1.4) and Corollary 5.45 (p.130, §5.3.2).

Conventions. The amplitude encoding `|amp(x)⟩ = ∑_j x_j/‖x‖ |j⟩` on `n = ⌈log d⌉` qubits
(Def. 5.34) is `padState n (normalizedVec x)`, the index `j` being read from the qubits most
significant bit first (`bitsToNat`). Algorithm 4 (p.126) is the frozen `alg4Unitary`: the binary
tree values `N(k, j)` are `ampTreeValue`, line 2 and line 5 are the steps `alg4Step n x k`
(`k = 0` is the initialization `|ψ₁⟩`, wire `k` is the fresh qubit of iteration `k`, controlled
by the first `k` wires), and line 7 is the sign diagonal with `sign(x_j) = −1` if `x_j < 0` and
`+1` otherwise.
-/

namespace QAlgorithms.Nannicini



/-- An oracle-circuit step that is a gate, or a query (possibly the adjoint) that is **not**
controlled by another wire. The QRAM of Def. 5.39 and the membership oracle of Thm. 5.33 are
called as given; the source never grants controlled access. -/
def uncontrolledStep {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ} : OracleStep S a n → Prop
  | .gate _ => True
  | .query _ _ c _ _ => c = none

/-- Nannicini p.128, Definition 5.39 (QRAM): for stored words `M_j ∈ {0,1}^q`,
`U_QRAM |j⟩|y⟩ = |j⟩|y ⊕ M_j⟩` for all `j ∈ {0,1}^a`, `y ∈ {0,1}^q`. The address register is the
first `a` qubits, the data register the last `q`; `⊕` is bitwise XOR (the additive group of
`Qubits q`). Its size in the sense of Def. 5.39 is `2^a · q`. The data is a parameter
(Rem. 5.41: a QRAM is a family of unitaries indexed by its contents). -/
noncomputable def qramUnitary (a q : ℕ) (M : Qubits a → Qubits q) :
    Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ :=
  Matrix.reindex (qubitsAppendEquiv a q).symm (qubitsAppendEquiv a q).symm (xorOracle M)

/-- One classical arithmetic operation (cost model for the "Õ(d) classical arithmetic operations"
of Nannicini p.130, Cor. 5.45 and Rem. 5.44, which the source does not define). A program is a
straight-line program over the reals: each instruction reads earlier values by index and appends
one new value. The operations are the ones the preprocessing of p.124 and p.129–130 performs:
the squared moduli `|x_j|²` and subtree sums of the tree of Fig. 5.6, normalization by `‖x‖`,
the rotation angles `2 arccos √(N(k+1,2j)/N(k)…)` and the phases of the complex entries
(Cor. 5.37's proof), plus rational constants for fixed-point scaling. Each counts as one
operation. -/
inductive ArithInstr where
  | const (c : ℚ)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  | div (i j : ℕ)
  | sqrt (i : ℕ)
  | arccos (i : ℕ)
  | arg (i j : ℕ)

/-- The value an instruction appends, given the values computed so far (an out-of-range index
reads `0`; `t / 0 = 0` as in Lean). `arg i j` is the argument of the complex number
`vals[i] + i·vals[j]`. -/
noncomputable def ArithInstr.value (vals : List ℝ) : ArithInstr → ℝ
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
noncomputable def arithRun (P : List ArithInstr) (input : List ℝ) : List ℝ :=
  P.foldl (fun vals g => vals ++ [g.value vals]) input

/-- The classical description of `x ∈ ℂ^d` given to the preprocessing: the list
`Re x_0, Im x_0, Re x_1, Im x_1, …`. -/
noncomputable def complexInput {d : ℕ} (x : Fin d → ℂ) : List ℝ :=
  (List.ofFn fun j => [(x j).re, (x j).im]).flatten

/-- The QRAM contents written by the classical preprocessing (Rem. 5.40: classical write): word
`j` is the `q`-bit binary expansion (most significant bit first) of the integer part of the
program value with index `addr j`. Storing a value is not counted as an arithmetic operation. -/
noncomputable def qramWords (a q : ℕ) (P : List ArithInstr) (addr : Qubits a → ℕ) {d : ℕ}
    (x : Fin d → ℂ) : Qubits a → Qubits q :=
  fun j => natToBits q ⌊(arithRun P (complexInput x)).getD (addr j) 0⌋₊


/-- A unitary implementing `MEM_{0,δ}(K)` in superposition (the object of Nannicini p.123,
Thm. 5.33, which the source does not define). Points are given in an `m`-qubit register through
an encoding `enc` of bit strings as points of `ℝ^d`; the oracle has an answer qubit (the first
qubit of its second register) and `k` workspace qubits, which start in `|0⟩`. On each basis
point `|p⟩` it leaves the point register unchanged and leaves the answer qubit holding the
correct membership answer `[enc p ∈ K]` with probability at least `1 − δ`. With precision `0`,
the two assertions of Def. 5.22 (p.119), `x ∈ B₂(K, 0) = K` and `x ∉ B₂(K, −0) = K`, are exact
membership; `δ` is the failure probability of Def. 5.22. -/
def IsQuantumMembershipOracle {d m k : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (enc : Qubits m → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (O : Matrix (Qubits (m + (k + 1))) (Qubits (m + (k + 1))) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup (Qubits (m + (k + 1))) ℂ ∧
    ∀ p : Qubits m, ∃ φ : EuclideanSpace ℂ (Qubits (k + 1)),
      act O (ket (Fin.append p fun _ => false)) =
          WithLp.toLp 2 (fun z => if (qubitsAppendEquiv m (k + 1) z).1 = p then
            φ (qubitsAppendEquiv m (k + 1) z).2 else 0) ∧
        1 - δ ≤ (open Classical in probEvent φ fun z => (z 0 = true ↔ enc p ∈ K))


end QAlgorithms.Nannicini


