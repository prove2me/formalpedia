-- Prove2me | Definitions.Def_QAlgorithms_Defs_Basic
-- name    : QAlgorithms_Defs_Basic
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:23:51.038367+00:00
-- url     : https://prove2.me/theorems/fbb4aeb6-18d3-44ee-8e68-ea79055cc950
-- title:
--   Registers, states, measurement (shared definition layer)
-- statement:
--   Registers, states, measurement (shared definition layer)
--
--   ### QAlgorithms.Qubits
--
--   For a natural number $n$, $\mathrm{Qubits}(n)$ is the set of all functions $\{0,1,\dots,n-1\} \to \{\mathrm{false},\mathrm{true}\}$, i.e. bit strings $b = (b_0, b_1, \dots, b_{n-1})$ of length $n$. It has $2^n$ elements. These strings serve as the labels of the computational-basis states of $n$ qubits.
--
--   When $n = 0$, $\mathrm{Qubits}(0)$ has exactly one element, the empty string.
--
--   ### QAlgorithms.bitsToNat
--
--   For a natural number $n$ (implicit) and a bit string $b = (b_0,\dots,b_{n-1}) \in \mathrm{Qubits}(n)$, $\mathrm{bitsToNat}(b)$ is the natural number
--
--   $$
--   \mathrm{bitsToNat}(b) \;=\; \sum_{i=0}^{n-1} [\,b_i = \mathrm{true}\,]\cdot 2^{\,n-1-i}.
--   $$
--
--   So $b$ is read as a binary numeral with $b_0$ as the **most** significant bit and $b_{n-1}$ as the least significant bit (big-endian).
--
--   The exponent $n-1-i$ is computed in natural-number arithmetic. Since $0 \le i \le n-1$, it never truncates. For $n = 0$ the sum is empty and the value is $0$. The result always lies in $\{0, \dots, 2^n - 1\}$.
--
--   ### QAlgorithms.bitsEquivFin
--
--   For each natural number $n$, $\mathrm{bitsEquivFin}(n)$ is an explicit bijection
--
--   $$
--   \mathrm{Qubits}(n) \;\xrightarrow{\ \sim\ }\; \{0, 1, \dots, 2^n - 1\}.
--   $$
--
--   It is built as a composite of three steps:
--
--   1. Reverse the order of the positions: position $j$ is moved to position $n-1-j$.
--   2. Identify $\mathrm{false}$ with the digit $0$ and $\mathrm{true}$ with the digit $1$.
--   3. Send a digit vector $(d_0,\dots,d_{n-1})$ to $\sum_i d_i\, 2^i$, where position $0$ is least significant.
--
--   Unfolding these steps, a string $b$ is sent to
--
--   $$
--   \sum_{j=0}^{n-1} [\,b_j=\mathrm{true}\,]\, 2^{\,n-1-j}.
--   $$
--
--   This is the same big-endian reading as $\mathrm{bitsToNat}$, with $b_0$ the most significant bit, but now packaged as a bijection onto $\{0,\dots,2^n-1\}$. For $n=0$ it maps the empty string to $0$, which is the only element of $\{0\}$.
--
--   ### QAlgorithms.natToBits
--
--   For natural numbers $n$ and $k$, $\mathrm{natToBits}(n,k) \in \mathrm{Qubits}(n)$ is defined as follows:
--
--   - First reduce $k$ modulo $2^n$.
--   - Then apply the inverse of the bijection $\mathrm{bitsEquivFin}(n)$ to the result $k \bmod 2^n$.
--
--   Concretely, the result is the unique $b = (b_0,\dots,b_{n-1})$ with
--
--   $$
--   \sum_{j=0}^{n-1} [\,b_j=\mathrm{true}\,]\,2^{\,n-1-j} = k \bmod 2^n.
--   $$
--
--   That is, $b$ is the $n$-bit big-endian binary expansion of $k \bmod 2^n$, with $b_0$ the most significant bit.
--
--   Edge cases:
--
--   - Values $k \ge 2^n$ are silently wrapped around: only the low $n$ bits of $k$ are kept.
--   - For $n=0$ the result is the empty string for every $k$.
--
--   ### QAlgorithms.ket
--
--   Let $\iota$ be any type with decidable equality (no finiteness is required by the definition), and let $i \in \iota$. Then $\mathrm{ket}(i)$, written $|i\rangle$, is the standard basis vector $e_i$ in the complex $\ell^2$-space $\mathbb{C}^{\iota}$, whose norm is the Euclidean (2-)norm. Its coordinates are
--
--   $$
--   |i\rangle_j \;=\; \begin{cases} 1 & j = i,\\ 0 & j \ne i.\end{cases}
--   $$
--
--   ### QAlgorithms.zeroKet
--
--   For a natural number $n$, $\mathrm{zeroKet}(n)$ is the vector $|0\cdots 0\rangle \in \mathbb{C}^{\mathrm{Qubits}(n)}$. This is the standard basis vector indexed by the all-$\mathrm{false}$ bit string of length $n$: it has coordinate $1$ at that string and $0$ at every other string.
--
--   For $n=0$ the space is one-dimensional, indexed by the empty string, and $\mathrm{zeroKet}(0)$ is its unique basis vector $1$.
--
--   ### QAlgorithms.IsState
--
--   Let $\iota$ be a finite type and let $\psi \in \mathbb{C}^{\iota}$ be a vector with the Euclidean norm. The predicate $\mathrm{IsState}(\psi)$ holds exactly when
--
--   $$
--   \|\psi\|_2 = \Big(\sum_{j \in \iota} |\psi_j|^2\Big)^{1/2} = 1.
--   $$
--
--   That is, $\psi$ is a unit vector. No condition modulo global phase is imposed.
--
--   If $\iota$ is empty, the only vector is $0$, which has norm $0$. So no state exists in that case.
--
--   ### QAlgorithms.act
--
--   Let $\iota$ be a finite type, let $A$ be a complex $\iota \times \iota$ matrix, and let $\psi \in \mathbb{C}^{\iota}$. Then $\mathrm{act}(A,\psi)$ is the ordinary matrix–vector product $A\psi \in \mathbb{C}^{\iota}$, with coordinates
--
--   $$
--   (A\psi)_j = \sum_{k \in \iota} A_{j,k}\,\psi_k .
--   $$
--
--   No unitarity or other condition is required of $A$.
--
--   ### QAlgorithms.tensorVec
--
--   Let $\iota$ and $\kappa$ be arbitrary types, and let $\psi \in \mathbb{C}^{\iota}$ and $\varphi \in \mathbb{C}^{\kappa}$. Then $\mathrm{tensorVec}(\psi,\varphi)$ is the product vector $\psi \otimes \varphi \in \mathbb{C}^{\iota \times \kappa}$, indexed by pairs $(a,b)$ with $a\in\iota$ and $b\in\kappa$, with coordinates
--
--   $$
--   (\psi\otimes\varphi)_{(a,b)} = \psi_a\,\varphi_b .
--   $$
--
--   ### QAlgorithms.prob
--
--   Let $\iota$ be a finite type with decidable equality, let $\psi \in \mathbb{C}^{\iota}$, and let $z \in \iota$. Then
--
--   $$
--   \mathrm{prob}(\psi, z) \;=\; \big|\langle z \mid \psi\rangle\big|^2 \;=\; |\psi_z|^2 .
--   $$
--
--   Here the inner product is conjugate-linear in its first argument, so $\langle z|\psi\rangle = \psi_z$.
--
--   This is a real number in $[0,\infty)$. It is **not** required that $\psi$ be a unit vector. If $\psi$ is not normalized, the values $\mathrm{prob}(\psi,z)$ need not sum to $1$.
--
--   ### QAlgorithms.probEvent
--
--   Let $\iota$ be a finite type with decidable equality, let $\psi \in \mathbb{C}^{\iota}$, and let $P$ be a decidable predicate on $\iota$. Then
--
--   $$
--   \mathrm{probEvent}(\psi, P) \;=\; \sum_{z \in \iota,\ P(z)} |\psi_z|^2 ,
--   $$
--
--   the sum of $\mathrm{prob}(\psi,z)$ over all basis labels $z$ satisfying $P$.
--
--   - If no $z$ satisfies $P$, the value is $0$.
--   - If $\psi$ is not normalized, the value is not a probability in the usual sense; it can exceed $1$.
--
--   ### QAlgorithms.marginalFst
--
--   Let $\iota$ and $\kappa$ be finite types with decidable equality, let $\psi \in \mathbb{C}^{\iota\times\kappa}$ be a vector on the product index set, and let $a \in \iota$. Then
--
--   $$
--   \mathrm{marginalFst}(\psi, a) \;=\; \sum_{b \in \kappa} \mathrm{prob}\big(\psi,(a,b)\big) \;=\; \sum_{b\in\kappa} |\psi_{(a,b)}|^2 .
--   $$
--
--   This is the total squared amplitude on basis labels whose first component equals $a$.
--
--   - No normalization of $\psi$ is assumed.
--   - If $\kappa$ is empty, the value is $0$.
--
--   ### QAlgorithms.orderedProd
--
--   Let $\iota$ be any finite index type with decidable equality, let $t$ be a natural number, and let $U_0, U_1, \dots, U_{t-1}$ be a family of complex square matrices indexed by $\iota \times \iota$ (indexed by $\{0, \dots, t-1\}$). The definition takes the list $[U_0, U_1, \dots, U_{t-1}]$, reverses it, and multiplies the entries left to right. The result is
--
--   $$
--   \operatorname{orderedProd}(U) \;=\; U_{t-1}\, U_{t-2} \cdots U_1\, U_0 .
--   $$
--
--   So $U_0$ is the rightmost factor; it acts first on a column vector. When $t = 0$ the list is empty and the result is the identity matrix on $\iota$.
--
--   ### QAlgorithms.specNorm
--
--   Let $\Bbbk$ be either $\mathbb{R}$ or $\mathbb{C}$ (any "RCLike" field). Let $m$ and $n$ be finite index types, with decidable equality on $n$. For a matrix $A \in \Bbbk^{m \times n}$, $\operatorname{specNorm}(A)$ is the real number given by the $\ell^2$ operator norm. That is, $A$ is regarded as a linear map from $\Bbbk^n$ to $\Bbbk^m$, both carrying the Euclidean norm, and
--
--   $$
--   \operatorname{specNorm}(A) \;=\; \sup_{v \neq 0} \frac{\|Av\|_2}{\|v\|_2}.
--   $$
--
--   This equals the largest singular value of $A$. It is $0$ when $A = 0$, and also when $m$ or $n$ is empty, since the matrix space is then trivial.
--
--   ### QAlgorithms.frobNorm
--
--   Let $m$ and $n$ be finite index types. For a complex matrix $X \in \mathbb{C}^{m \times n}$, $\operatorname{frobNorm}(X)$ is the real number given by the Frobenius norm:
--
--   $$
--   \operatorname{frobNorm}(X) \;=\; \Big(\sum_{i \in m}\sum_{j \in n} |X_{ij}|^2\Big)^{1/2}.
--   $$
--
--   It is $0$ if $m$ or $n$ is empty.
--
--   ### QAlgorithms.hammingWeight
--
--   Let $\iota$ be a finite type and let $x : \iota \to \{\text{false}, \text{true}\}$ be a Boolean-valued function. Its Hamming weight is the natural number
--
--   $$
--   \operatorname{hammingWeight}(x) \;=\; \#\{\, i \in \iota : x_i = \text{true} \,\},
--   $$
--
--   the number of indices at which $x$ is true. It is $0$ if $\iota$ is empty.
--
--   ### QAlgorithms.dotBits
--
--   Fix $n \in \mathbb{N}$. Here an $n$-bit string is a function $\{0, \dots, n-1\} \to \{\text{false}, \text{true}\}$; this is the type written $\mathrm{Qubits}(n)$.
--
--   For two such strings $i$ and $j$, $\operatorname{dotBits}(i, j)$ is the Boolean obtained in two steps:
--
--   1. For each position $k$, form the conjunction $i_k \wedge j_k$.
--   2. Sum these values over all $k \in \{0, \dots, n-1\}$, using the addition on Booleans from their Boolean-ring structure, which is exclusive-or.
--
--   So
--
--   $$
--   \operatorname{dotBits}(i,j) \;=\; \bigoplus_{k=0}^{n-1} (i_k \wedge j_k),
--   $$
--
--   which is true exactly when the number of positions $k$ with $i_k = j_k = \text{true}$ is odd. Identifying true with $1$, this is the inner product $i \cdot j \bmod 2$. For $n = 0$ the sum is empty and the value is false.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Basic.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Mathlib

/-!
# Registers, states, measurement (shared definition layer)

Sources: R. de Wolf, *Quantum Computing: Lecture Notes* (PDF pages cited as "de Wolf p.N"),
and A. Childs, *Lecture Notes on Quantum Algorithms* ("Childs p.N").

Conventions fixed once here and used by every statement of the run:

* An `n`-qubit register has computational-basis index set `Qubits n = Fin n → Bool`. Wire
  `i : Fin n` is the source's qubit `i + 1`; wire `0` is the most significant bit
  (de Wolf p.44: `|k⟩ = |k₁ … kₙ⟩`, `k₁` most significant).
* States are vectors of `EuclideanSpace ℂ ι`; being a state (unit norm) is the predicate
  `IsState`, carried as a hypothesis wherever the source says "state" (trap Q1).
* Operators are matrices `Matrix ι ι ℂ`; unitaries are members of `Matrix.unitaryGroup ι ℂ`;
  the tensor product of operators is `Matrix.kronecker` (`A ⊗ₖ B` acts on `ι × κ`, `A` on the
  first factor). A product index `ι × κ` is a two-register state space, first factor = first
  register.
* The amplitude `⟨i|ψ⟩` is `inner ℂ (ket i) ψ` (Mathlib's inner product is conjugate-linear in
  its first argument), which equals the coordinate `ψ i`.
-/

namespace QAlgorithms

open scoped ComplexConjugate

/-- de Wolf p.26 (§2.1), p.44 (§4.5); Childs p.9 (§1.2). The computational-basis index set of an
`n`-qubit register: bit strings `Fin n → Bool`. Wire `i` is the source's qubit `i + 1`, and wire
`0` is the most significant bit (see `bitsToNat`). -/
abbrev Qubits (n : ℕ) := Fin n → Bool

/-- de Wolf p.44 (§4.5): the integer `k = k₁ … kₙ` written by an `n`-bit string, most significant
bit first: wire `i` carries the weight `2^(n-1-i)`. (The subtraction is exact since `i < n`.)
Mathlib's `finFunctionFinEquiv` is little-endian, the opposite convention, and is not used
directly. -/
def bitsToNat {n : ℕ} (b : Qubits n) : ℕ :=
  ∑ i : Fin n, if b i then 2 ^ (n - 1 - (i : ℕ)) else 0

/-- de Wolf p.44 (§4.5): the bijection `{0,1}ⁿ ≃ {0, …, 2ⁿ - 1}` whose forward map is
`bitsToNat` (most significant bit first; see `bitsEquivFin_apply`). Built from Mathlib's
little-endian `finFunctionFinEquiv` by reversing the wire order. -/
def bitsEquivFin (n : ℕ) : Qubits n ≃ Fin (2 ^ n) :=
  ((Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin n)) finTwoEquiv.symm)).trans
    finFunctionFinEquiv

/-- de Wolf p.44 (§4.5): the `n`-bit most-significant-bit-first expansion of `k mod 2ⁿ`
(the inverse of `bitsToNat` on `{0, …, 2ⁿ - 1}`). -/
def natToBits (n k : ℕ) : Qubits n :=
  (bitsEquivFin n).symm ⟨k % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- de Wolf p.26 (§2.1): the computational basis state `|i⟩`. -/
noncomputable def ket {ι : Type*} [DecidableEq ι] (i : ι) : EuclideanSpace ℂ ι :=
  EuclideanSpace.single i 1

/-- de Wolf p.30 (§2.4.1): the `n`-qubit zero state `|0ⁿ⟩`. -/
noncomputable def zeroKet (n : ℕ) : EuclideanSpace ℂ (Qubits n) :=
  ket (fun _ : Fin n => false)

/-- de Wolf p.26 (§2.1), Childs p.9 (§1.1): `ψ` is a (pure) quantum state, i.e. a unit vector.
Every "state" hypothesis of a statement is `IsState` (trap Q1). -/
def IsState {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) : Prop :=
  ‖ψ‖ = 1

/-- de Wolf p.26 (§2.1): the vector `A ψ` obtained by applying the operator (matrix) `A` to `ψ`
(matrix–vector product, repackaged as a vector of `EuclideanSpace`). -/
noncomputable def act {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (Matrix.mulVec A (WithLp.ofLp ψ))

/-- de Wolf p.26 (§2.1), p.170 (§18.1): the tensor product `ψ ⊗ φ` of a state of the first
register and a state of the second, `(ψ ⊗ φ)(i, j) = ψ(i) φ(j)`. -/
noncomputable def tensorVec {ι κ : Type*} (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 (fun p => ψ p.1 * φ p.2)

/-- de Wolf p.26 (§2.1), p.36 (§3.2): the probability `|⟨z|ψ⟩|²` of outcome `z` when the state
`ψ` is measured in the computational basis (meaningful for `IsState ψ`). -/
noncomputable def prob {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (z : ι) :
    ℝ :=
  ‖inner ℂ (ket z) ψ‖ ^ 2

/-- de Wolf p.111 (§12.1), Childs p.106 (§21.2): the probability that a computational-basis
measurement of the whole register gives an outcome satisfying `P` (for instance: a designated
output qubit reads `b`, or the outcome lies in an accepting set). -/
noncomputable def probEvent {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι)
    (P : ι → Prop) [DecidablePred P] : ℝ :=
  ∑ z ∈ Finset.univ.filter P, prob ψ z

/-- de Wolf p.36 (§3.2): the probability that measuring only the first register of a
two-register state gives `a` (equivalently: measure both registers and discard the second
outcome). -/
noncomputable def marginalFst {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (ψ : EuclideanSpace ℂ (ι × κ)) (a : ι) : ℝ :=
  ∑ b : κ, prob ψ (a, b)

/-- Childs p.15 (Lemma 2.2): the ordered product `U_t ⋯ U_2 U_1` of `t` operators, where the
source's `U_1` is `U 0` and acts first; the empty product (`t = 0`) is the identity. -/
def orderedProd {ι : Type*} [Fintype ι] [DecidableEq ι] {t : ℕ} (U : Fin t → Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (List.ofFn U).reverse.prod

/-- Childs p.10 (§1.3, (1.4)), de Wolf p.47 (§4 exercise 4), p.112 (§12.1): the spectral
(operator) norm `‖A‖ = max_{‖v‖ = 1} ‖A v‖`, the largest singular value. Defined as the norm of
Mathlib's L2-operator norm structure on matrices (`Matrix.instL2OpNormedAddCommGroup`, a scoped
instance), named here so that statements never pick up another matrix norm by accident. -/
noncomputable def specNorm {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : ℝ :=
  @Norm.norm (Matrix m n 𝕜) (Matrix.instL2OpNormedAddCommGroup).toNorm A

/-- Childs p.118 (§23.2): the Frobenius norm `‖X‖_F = (Σ_{a,b} |X_{ab}|²)^{1/2}`, the norm of
Mathlib's (scoped) `Matrix.frobeniusNormedAddCommGroup`. -/
noncomputable def frobNorm {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) : ℝ :=
  @Norm.norm (Matrix m n ℂ) (Matrix.frobeniusNormedAddCommGroup).toNorm X

/-- de Wolf p.65 (§7.1), Childs p.107 (§21.3): the Hamming weight `|x|`, the number of positions
where `x` is `1` (for a search input: the number of solutions). -/
def hammingWeight {ι : Type*} [Fintype ι] (x : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

/-- de Wolf p.26 (§2.1, (2.1)), p.35 (§3.1): the inner product `i · j = Σ_k i_k j_k mod 2` of two
bit strings, as a bit. The sum is in `Bool` with Mathlib's Boolean-ring structure (`+` is xor,
`*` is and). Bitwise xor `i ⊕ j` of bit strings is the addition `i + j` of the Pi group
`Fin n → Bool`. -/
def dotBits {n : ℕ} (i j : Qubits n) : Bool :=
  ∑ k : Fin n, (i k && j k)

/-! ### Sanity tests -/

theorem bitsEquivFin_apply {n : ℕ} (b : Qubits n) : (bitsEquivFin n b : ℕ) = bitsToNat b := by
  simp only [bitsEquivFin, Equiv.trans_apply, finFunctionFinEquiv_apply, Equiv.arrowCongr_apply,
    bitsToNat]
  refine Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin n)) _ _ (fun i => ?_)
  simp only [Function.comp_apply, Equiv.symm_symm, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hi := i.isLt
  have e1 : n - 1 - (n - ((i : ℕ) + 1)) = i := by omega
  cases h : b (Fin.rev i) <;> simp [finTwoEquiv, Fin.val_rev, e1, h]

example : bitsToNat (![true, false] : Qubits 2) = 2 := by decide

example : bitsToNat (![false, true, true] : Qubits 3) = 3 := by decide

example : dotBits (![true, true] : Qubits 2) ![true, true] = false := by decide

example : dotBits (![true, false] : Qubits 2) ![true, true] = true := by decide

example : hammingWeight (![true, false, true] : Fin 3 → Bool) = 2 := by decide

example {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) : IsState (ket i) := by
  simp [IsState, ket]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (ψ : EuclideanSpace ℂ ι) :
    inner ℂ (ket i) ψ = ψ i := by
  simp [ket, EuclideanSpace.inner_single_left]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (i z : ι) :
    prob (ket i) z = if z = i then 1 else 0 := by
  by_cases h : z = i <;> simp [prob, ket, h, EuclideanSpace.inner_single_left, Pi.single_apply]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  simp [act]

/-- A unitary preserves the norm of every vector, hence maps states to states. -/
theorem act_norm_of_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    ‖act U ψ‖ = ‖ψ‖ := by
  have h : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) U ∈ unitary (EuclideanSpace ℂ ι →L[ℂ]
      EuclideanSpace ℂ ι) := Unitary.map_mem (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) hU
  have e : act U ψ = Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) U ψ := rfl
  rw [e]
  exact ContinuousLinearMap.norm_map_of_mem_unitary h ψ

example (U : Fin 0 → Matrix (Fin 2) (Fin 2) ℂ) : orderedProd U = 1 := by
  simp [orderedProd]

example (U : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) : orderedProd U = U 1 * U 0 := by
  simp [orderedProd, List.ofFn_succ]

end QAlgorithms


