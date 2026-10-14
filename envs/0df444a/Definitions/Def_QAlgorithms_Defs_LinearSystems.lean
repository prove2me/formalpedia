-- Prove2me | Definitions.Def_QAlgorithms_Defs_LinearSystems
-- name    : QAlgorithms_Defs_LinearSystems
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:37:29.341977+00:00
-- url     : https://prove2.me/theorems/6aea6c8f-368a-4152-8a24-55a7f70139a6
-- title:
--   The quantum linear systems problem (shared definition layer)
-- statement:
--   The quantum linear systems problem (shared definition layer)
--
--   ### QAlgorithms.IsSparse
--
--   Let $N$ and $d$ be natural numbers and $A$ a complex $N \times N$ matrix. The predicate holds when both of the following are true:
--
--   1. Every row $j$ of $A$ has at most $d$ nonzero entries: $\#\{k : A_{jk} \ne 0\} \le d$.
--   2. Every column $k$ of $A$ has at most $d$ nonzero entries: $\#\{j : A_{jk} \ne 0\} \le d$.
--
--   For $N = 0$ the predicate holds trivially. For $d \ge N$ it holds for every $A$.
--
--   ### QAlgorithms.conditionNumber
--
--   Let $\iota$ be a finite index type with decidable equality and $A$ a complex $\iota \times \iota$ matrix. Write $\lambda_0 \le \lambda_1 \le \dots \le \lambda_{|\iota|-1}$ for the eigenvalues of the Hermitian matrix $A^\dagger A$ listed in ascending order with multiplicity. These eigenvalues are real and nonnegative.
--
--   The definition has two cases:
--
--   - **$\iota$ nonempty.** The value is
--   $$\kappa(A) = \frac{\sqrt{\lambda_{|\iota|-1}}}{\sqrt{\lambda_0}} = \frac{\sigma_{\max}(A)}{\sigma_{\min}(A)},$$
--   the ratio of the largest to the smallest singular value. Division by zero is defined as $0$. So if $A$ is singular, meaning $\lambda_0 = 0$, the value is $0$, not $\infty$.
--   - **$\iota$ empty.** The value is $0$.
--
--   ### QAlgorithms.normalizedVec
--
--   For a finite index type $\iota$ and a vector $b \in \mathbb{C}^\iota$ (Euclidean space), this defines
--
--   $$\operatorname{normalizedVec}(b) = \|b\|^{-1}\, b,$$
--
--   where $\|\cdot\|$ is the Euclidean norm. Since $0^{-1}$ is taken to be $0$, the zero vector is sent to the zero vector, which is not a unit vector. Every nonzero $b$ is sent to a unit vector.
--
--   ### QAlgorithms.padState
--
--   Let $n, N$ be natural numbers and $v \in \mathbb{C}^N$ (Euclidean space indexed by $\{0,\dots,N-1\}$). This defines a vector in $\mathbb{C}^{\{0,1\}^n}$, indexed by $n$-bit strings $z$.
--
--   Each bit string is read as a number in big-endian order:
--
--   $$\operatorname{num}(z) = \sum_{i=0}^{n-1} z_i\, 2^{\,n-1-i},$$
--
--   so bit $0$ is the most significant. The entries of the output vector are
--
--   $$\big(\operatorname{padState}_n(v)\big)_z = \begin{cases} v_{\operatorname{num}(z)} & \text{if } \operatorname{num}(z) < N,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   Two consequences follow from this formula:
--
--   - **$2^n \ge N$:** the result is $v$ padded with zeros.
--   - **$2^n < N$:** the entries $v_{2^n},\dots,v_{N-1}$ are dropped, so the output is a truncation of $v$.
--
--   No normalization is applied.
--
--   ### QAlgorithms.ket2
--
--   This definition builds a computational-basis vector of a $2n$-qubit register from two natural numbers $n, j, l$. A $k$-qubit basis label is a function $\{0,\dots,k-1\}\to\{\text{false},\text{true}\}$. The state space is $\mathbb{C}^{\{0,1\}^{2n}}$ with the Euclidean ($\ell^2$) norm.
--
--   For any $k$ and $n$, the bit string $\mathrm{bits}_n(k) \in \{0,1\}^n$ is the **big-endian** $n$-bit binary representation of $k \bmod 2^n$. Bit $0$ is the most significant: the string $b$ corresponds to the number
--   $$\sum_{i=0}^{n-1} b_i\, 2^{\,n-1-i}.$$
--   Then
--   $$\mathrm{ket2}(n,j,l) \;=\; e_{\,\mathrm{bits}_n(j)\,\Vert\,\mathrm{bits}_n(l)},$$
--   which is the standard basis vector (entry $1$ at that label, $0$ elsewhere). Here $\Vert$ is concatenation: positions $0,\dots,n-1$ carry $\mathrm{bits}_n(j)$ and positions $n,\dots,2n-1$ carry $\mathrm{bits}_n(l)$.
--
--   In bra-ket notation this is $|j \bmod 2^n\rangle|l \bmod 2^n\rangle$. Numbers $j, l \ge 2^n$ are silently reduced mod $2^n$, so for example $\mathrm{ket2}(n,j,l)=\mathrm{ket2}(n,j+2^n,l)$. When $n=0$ the space is one-dimensional and every $\mathrm{ket2}(0,j,l)$ is the same unit vector.
--
--   ### QAlgorithms.IsColumnOracle
--
--   **Setting.**
--   - $N\in\mathbb{N}$, and $A$ is an $N\times N$ complex matrix with rows and columns indexed by $\{0,\dots,N-1\}$.
--   - $d\in\mathbb{N}$.
--   - $c=\lceil \log_2 N\rceil$, the least $c$ with $N\le 2^c$. Note $c=0$ when $N\in\{0,1\}$.
--   - $O$ is a complex square matrix indexed by $2c$-qubit basis labels $\{0,1\}^{2c}$.
--
--   **Definition.** The proposition "$O$ is a column oracle for $A$ with sparsity $d$" holds iff both of the following hold.
--
--   1. $O$ is unitary: $O^*O=OO^*=I$.
--   2. There exists a function $\nu$ assigning to each column $j\in\{0,\dots,N-1\}$ and each slot $l\in\{0,\dots,d-1\}$ a row index $\nu_j(l)\in\{0,\dots,N-1\}$, such that:
--      - (a) for every $j$, the map $l\mapsto\nu_j(l)$ is injective;
--      - (b) for all $j,k$, if $A_{k j}\neq 0$ then $k=\nu_j(l)$ for some $l$;
--      - (c) for all $j<N$ and $l<d$:
--      $$O\,\mathrm{ket2}(c,j,l)=\mathrm{ket2}(c,j,\nu_j(l)),$$
--      that is, $O|j\rangle|l\rangle=|j\rangle|\nu_j(l)\rangle$ with both registers written big-endian on $c$ qubits.
--
--   **Consequences and edge cases.**
--   - Condition (b) says the nonzero entries of column $j$ lie among $\nu_j(0),\dots,\nu_j(d-1)$. These listed rows may also include rows where $A$ is zero.
--   - Injectivity forces $d\le N$ whenever $N\ge1$. Together with (b), every column of $A$ has at most $d$ nonzero entries; if $d>N\ge 1$ no such $\nu$ exists.
--   - If $d=0$, then (b) forces $A=0$.
--   - If $N=0$, all conditions on $\nu$ are vacuous, and the definition reduces to $O$ being a $1\times1$ unitary.
--   - Only the basis states with first register $<N$ and second register $<d$ are constrained in (c). On all other basis states, $O$ is constrained only by unitarity.
--   - Nothing is required about rows of $A$, only columns.
--
--   ### QAlgorithms.IsEntryOracle
--
--   **Setting.**
--   - $N,b\in\mathbb{N}$, and $A$ is an $N\times N$ complex matrix.
--   - $\mathrm{dec}:\{0,1\}^b\to\mathbb{C}$ is an arbitrary "decoding" function.
--   - $c=\lceil\log_2 N\rceil$.
--   - $O$ is a complex square matrix indexed by $\{0,1\}^{2c+b}$.
--
--   **Definition.** The proposition holds iff both of the following hold.
--
--   1. $O$ is unitary.
--   2. There exists a function $\mathrm{code}$ assigning a $b$-bit string $\mathrm{code}(j,k)\in\{0,1\}^b$ to every pair $j,k\in\{0,\dots,N-1\}$, such that:
--      - (a) $\mathrm{dec}(\mathrm{code}(j,k))=A_{jk}$ for all $j,k$;
--      - (b) for all $j,k<N$ and every $z\in\{0,1\}^b$:
--      $$O\, e_{\mathrm{bits}_c(j)\Vert\mathrm{bits}_c(k)\Vert z}=e_{\mathrm{bits}_c(j)\Vert\mathrm{bits}_c(k)\Vert (z\oplus\mathrm{code}(j,k))}.$$
--
--   In (b), $\mathrm{bits}_c$ is the big-endian $c$-bit encoding and $\oplus$ is bitwise XOR (addition in $\mathbb{F}_2^b$). In bra-ket form, $O|j\rangle|k\rangle|z\rangle=|j\rangle|k\rangle|z\oplus\mathrm{code}(j,k)\rangle$.
--
--   **Consequences and edge cases.**
--   - Condition (a) requires every entry of $A$ to be **exactly** a value of $\mathrm{dec}$. If some $A_{jk}$ is not in the image of $\mathrm{dec}$, the proposition is false. In particular, if $b=0$, all entries of $A$ must equal the single value $\mathrm{dec}(\varnothing)$.
--   - Basis states whose first two registers do not encode numbers $<N$ are constrained only by unitarity.
--   - When $N=0$, the definition reduces to $O$ being unitary.
--
--   ### QAlgorithms.IsSparseAccessOracle
--
--   **Setting.** The inputs are:
--   - $N,b,d\in\mathbb{N}$;
--   - an $N\times N$ complex matrix $A$;
--   - a function $\mathrm{dec}:\{0,1\}^b\to\mathbb{C}$;
--   - a matrix $O_{\mathrm{col}}$ on $2c$ qubits and a matrix $O_{\mathrm{ent}}$ on $2c+b$ qubits, where $c=\lceil\log_2N\rceil$.
--
--   **Definition.** The proposition is the conjunction of two conditions:
--   - $O_{\mathrm{col}}$ is a column oracle for $A$ with parameter $d$ in the sense of `IsColumnOracle`;
--   - $O_{\mathrm{ent}}$ is an entry oracle for $A$ with decoder $\mathrm{dec}$ in the sense of `IsEntryOracle`.
--
--   **Unfolded, it states:**
--   - both matrices are unitary;
--   - there are injective slot maps $\nu_j:\{0,\dots,d-1\}\to\{0,\dots,N-1\}$ covering the nonzero entries of each column $j$, with $O_{\mathrm{col}}|j\rangle|l\rangle=|j\rangle|\nu_j(l)\rangle$ for $j<N$, $l<d$;
--   - there is a code $\mathrm{code}(j,k)\in\{0,1\}^b$ with $\mathrm{dec}(\mathrm{code}(j,k))=A_{jk}$ and $O_{\mathrm{ent}}|j\rangle|k\rangle|z\rangle=|j\rangle|k\rangle|z\oplus\mathrm{code}(j,k)\rangle$.
--
--   All edge cases of the two components carry over:
--   - every column of $A$ has at most $d$ nonzeros, and $d\le N$ when $N\ge1$;
--   - every entry of $A$ lies in the image of $\mathrm{dec}$.
--
--   No condition relates the two oracles' witnesses $\nu$ and $\mathrm{code}$ to each other.
--
--   ### QAlgorithms.IsStatePrep
--
--   **Setting.** $N\in\mathbb{N}$, $\mathbf{b}\in\mathbb{C}^N$ (Euclidean space), $c=\lceil\log_2N\rceil$, and $O$ is a complex matrix on $c$ qubits (indexed by $\{0,1\}^c$).
--
--   **Definition.** The proposition holds iff $O$ is unitary and
--   $$O\,e_{0\cdots0}=\mathrm{pad}_c\!\left(\hat{\mathbf b}\right).$$
--   The pieces are as follows.
--   - $e_{0\cdots0}$ is the all-false basis vector of $c$ qubits.
--   - $\hat{\mathbf b}=\|\mathbf b\|^{-1}\mathbf b$, with the convention $0^{-1}=0$. So $\hat{\mathbf b}=0$ when $\mathbf b=0$.
--   - $\mathrm{pad}_c(v)$ is the vector on $\{0,1\}^c$ whose $z$-entry is $v_{\mathrm{num}(z)}$ if $\mathrm{num}(z)<N$, and $0$ otherwise. Here $\mathrm{num}(z)=\sum_i z_i2^{c-1-i}$ reads $z$ big-endian.
--
--   In bra-ket form, $O|0\rangle=\sum_{i<N}(\mathbf b_i/\|\mathbf b\|)|i\rangle$.
--
--   **Edge cases.**
--   - Since a unitary maps the unit vector $e_{0\cdots0}$ to a unit vector, the condition is unsatisfiable when $\mathbf b=0$.
--   - In particular, it is unsatisfiable when $N=0$: then $c=0$, and the padded vector is $0$.
--
--   ### QAlgorithms.flagWire
--
--   For $n,m\in\mathbb{N}$, this is the qubit position $0$ in a register of $1+n+m$ qubits, whose positions are $\{0,\dots,n+m\}$. It is the first position, intended to sit before an $n$-qubit block and an $m$-qubit block.
--
--   ### QAlgorithms.outPart
--
--   For $n,m\in\mathbb{N}$ and a basis label $z\in\{0,1\}^{1+n+m}$, this is the $n$-bit string $\mathrm{out}(z)\in\{0,1\}^n$ given by
--   $$\mathrm{out}(z)_i=z_{1+i},\qquad i=0,\dots,n-1.$$
--   It extracts positions $1$ through $n$ of $z$.
--
--   ### QAlgorithms.garbagePart
--
--   For $n,m\in\mathbb{N}$ and $z\in\{0,1\}^{1+n+m}$, this is the $m$-bit string $\mathrm{garb}(z)\in\{0,1\}^m$ given by
--   $$\mathrm{garb}(z)_k=z_{1+n+k},\qquad k=0,\dots,m-1.$$
--   It extracts the last $m$ positions of $z$.
--
--   ### QAlgorithms.QLSPSuccess
--
--   **Setting.**
--   - $n,m\in\mathbb{N}$.
--   - $\varphi$ is a vector in $\mathbb{C}^{\{0,1\}^{1+n+m}}$ (Euclidean norm), **not required to be normalized**.
--   - $x\in\mathbb{C}^{\{0,1\}^n}$, also not required to be normalized.
--   - $\varepsilon\in\mathbb{R}$.
--
--   Write $z_0$ for the flag bit (position $0$), and $\mathrm{out}(z)$, $\mathrm{garb}(z)$ for positions $1..n$ and $1+n..n+m$ of a label $z$. Let
--   $$p=\sum_{z:\,z_0=\text{true}}|\varphi_z|^2,$$
--   which is the sum of squared moduli of the amplitudes of $\varphi$ on flag $=1$.
--
--   **Definition.** The proposition holds iff both of the following hold.
--
--   1. $\tfrac12\le p$.
--   2. There exists $g\in\mathbb{C}^{\{0,1\}^m}$ with $\|g\|=1$ such that
--   $$\Big\|\,u-w\,\Big\|\le\varepsilon,\qquad u_z=\begin{cases}p^{-1/2}\,\varphi_z & z_0=\text{true}\\ 0&\text{otherwise}\end{cases},\qquad w_z=\begin{cases}x_{\mathrm{out}(z)}\,g_{\mathrm{garb}(z)}&z_0=\text{true}\\0&\text{otherwise}\end{cases}.$$
--
--   Here $\|\cdot\|$ is the Euclidean norm on $\mathbb{C}^{\{0,1\}^{1+n+m}}$. Thus $w$ is $|1\rangle\otimes x\otimes g$ with the flag in front.
--
--   **Notes.**
--   - The comparison is exact, with no global-phase freedom other than what can be absorbed into the choice of $g$.
--   - If $\varepsilon<0$ the proposition is false.
--   - Since $p\ge\frac12>0$, the factor $p^{-1/2}$ is a genuine real number. However, $p$ may exceed $1$, because $\varphi$ is not assumed to be a unit vector.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/LinearSystems.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Information
/-!
# The quantum linear systems problem (shared definition layer)

Childs, Kothari, Somma, *Quantum linear systems algorithm with exponentially improved dependence
on precision*, SIAM J. Comput. 2017 (arXiv:1511.02306v2), cited "CKS p.N" (PDF pages).

Indexing: the source's `[N] = {1, …, N}` is `Fin N` (0-based); index `j` is held in
`n = ⌈log₂ N⌉ = Nat.clog 2 N` qubits as the `n`-bit most-significant-first expansion
`natToBits n j`.
-/

namespace QAlgorithms

/-- CKS p.3 (§1.1): `A` is `d`-sparse: at most `d` nonzero entries in any row or column. -/
def IsSparse {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) : Prop :=
  (∀ j, (Finset.univ.filter fun k => A j k ≠ 0).card ≤ d) ∧
    ∀ k, (Finset.univ.filter fun j => A j k ≠ 0).card ≤ d

/-- CKS p.3 (§1.1): the condition number `σ_max(A)/σ_min(A)`, the ratio of the largest to the
smallest singular value (singular values = square roots of the eigenvalues of `A†A`, which are
nonnegative). The source leaves it undefined for non-invertible `A`; there the formula divides by
`0` and returns `0`, so statements assume `A` invertible (and a nonempty index type). For
Hermitian `A` it is `max |λ| / min |λ|`. -/
noncomputable def conditionNumber {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  if h : 0 < Fintype.card ι then
    Real.sqrt (ascEigenvalues (A.conjTranspose * A) ⟨Fintype.card ι - 1, by omega⟩) /
      Real.sqrt (ascEigenvalues (A.conjTranspose * A) ⟨0, h⟩)
  else 0

/-- CKS p.2–3 ((3)): the normalized state `|b⟩ = Σ_i b_i |i⟩ / ‖Σ_i b_i |i⟩‖` (statements require
`b ≠ 0`; at `b = 0` the value is `0`). -/
noncomputable def normalizedVec {ι : Type*} [Fintype ι] (b : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  ((‖b‖⁻¹ : ℝ) : ℂ) • b

/-- CKS p.2 (§1.1): a vector indexed by `[N]` placed on an `n`-qubit register: amplitude `v_i` at
the `n`-bit string of `i` and `0` at the strings encoding numbers `≥ N` (meaningful for
`N ≤ 2ⁿ`). -/
noncomputable def padState {N : ℕ} (n : ℕ) (v : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun z => if h : bitsToNat z < N then v ⟨bitsToNat z, h⟩ else 0

/-- The basis state `|j, l⟩` of two `n`-qubit registers (`j`, `l` written in `n` bits each). -/
noncomputable def ket2 (n j l : ℕ) : EuclideanSpace ℂ (Qubits (n + n)) :=
  ket (Fin.append (natToBits n j) (natToBits n l))

/-- CKS p.2 ((1)): `O` is a column oracle for the `d`-sparse `A`: a unitary on two `n`-qubit
registers (`n = ⌈log₂ N⌉`) performing `|j, ℓ⟩ ↦ |j, ν(j, ℓ)⟩` for `j ∈ [N]`, `ℓ ∈ [d]`, where
`ν(j, ·)` enumerates, without repetition, positions of column `j` that include all of its nonzero
entries (the "row index of the `ℓ`-th nonzero entry"; when the column has fewer than `d` nonzero
entries the remaining `ν(j, ℓ)` are other positions, as in [BCK15]). Computed in place; basis
states outside `[N] × [d]` are unconstrained. -/
def IsColumnOracle {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (d : ℕ)
    (O : Matrix (Qubits (Nat.clog 2 N + Nat.clog 2 N)) (Qubits (Nat.clog 2 N + Nat.clog 2 N)) ℂ) :
    Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧
    ∃ ν : Fin N → Fin d → Fin N, (∀ j, Function.Injective (ν j)) ∧
      (∀ j k, A k j ≠ 0 → ∃ l, ν j l = k) ∧
      ∀ (j : Fin N) (l : Fin d), act O (ket2 (Nat.clog 2 N) j l) = ket2 (Nat.clog 2 N) j (ν j l)

/-- CKS p.3 ((2)): `O` is an entry oracle for `A`: a unitary performing
`|j, k, z⟩ ↦ |j, k, z ⊕ A_{jk}⟩` for `j, k ∈ [N]`, where the third register holds a `b`-bit string
representing the entry exactly ("we assume the entries of `A` can be represented exactly"): the
entry `A_{jk}` is written as the code `code j k`, which the fixed decoding `dec` reads back as
`A_{jk}`. -/
def IsEntryOracle {N b : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (dec : Qubits b → ℂ)
    (O : Matrix (Qubits (Nat.clog 2 N + Nat.clog 2 N + b))
      (Qubits (Nat.clog 2 N + Nat.clog 2 N + b)) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧
    ∃ code : Fin N → Fin N → Qubits b, (∀ j k, dec (code j k) = A j k) ∧
      ∀ (j k : Fin N) (z : Qubits b),
        act O (ket (Fin.append (Fin.append (natToBits (Nat.clog 2 N) j) (natToBits (Nat.clog 2 N) k))
          z)) =
        ket (Fin.append (Fin.append (natToBits (Nat.clog 2 N) j) (natToBits (Nat.clog 2 N) k))
          (z + code j k))

/-- CKS p.2–3 (Problem 1: "a procedure `P_A` that computes entries of `A` as described in
equations (1) and (2)"): the pair `(Ocol, Oent)` is a sparse-access oracle `P_A` for `A`: the map
(1) and the map (2). A use of `P_A` is a use of either map. -/
def IsSparseAccessOracle {N b : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) (dec : Qubits b → ℂ)
    (Ocol : Matrix (Qubits (Nat.clog 2 N + Nat.clog 2 N)) (Qubits (Nat.clog 2 N + Nat.clog 2 N)) ℂ)
    (Oent : Matrix (Qubits (Nat.clog 2 N + Nat.clog 2 N + b))
      (Qubits (Nat.clog 2 N + Nat.clog 2 N + b)) ℂ) : Prop :=
  IsColumnOracle A d Ocol ∧ IsEntryOracle A dec Oent

/-- CKS p.2–3 (Problem 1: "a procedure `P_B` that prepares the state `|b⟩`"): `O` is a unitary on
`n = ⌈log₂ N⌉` qubits with `O|0ⁿ⟩ = |b⟩`. -/
def IsStatePrep {N : ℕ} (bvec : EuclideanSpace ℂ (Fin N))
    (O : Matrix (Qubits (Nat.clog 2 N)) (Qubits (Nat.clog 2 N)) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup _ ℂ ∧ act O (zeroKet (Nat.clog 2 N)) = padState (Nat.clog 2 N) (normalizedVec bvec)

/-- The flag wire (wire `0`) of a register laid out as flag, `n` output wires, `m` garbage wires. -/
def flagWire (n m : ℕ) : Fin (1 + n + m) :=
  Fin.castAdd m (Fin.castAdd n (0 : Fin 1))

/-- The output-register part of a basis string of the layout flag / output / garbage. -/
def outPart {n m : ℕ} (z : Qubits (1 + n + m)) : Qubits n :=
  fun i => z (Fin.castAdd m (Fin.natAdd 1 i))

/-- The garbage part of a basis string of the layout flag / output / garbage. -/
def garbagePart {n m : ℕ} (z : Qubits (1 + n + m)) : Qubits m :=
  fun k => z (Fin.natAdd (1 + n) k)

/-- CKS p.3 (Problem 1: "output a state `|x̃⟩` such that `‖|x̃⟩ − |x⟩‖ ≤ ε`, succeeding with
probability `Ω(1)` (say, at least `1/2`), with a flag indicating success"): the final state `φ`
(register laid out as flag wire, `n` output wires, `m` garbage wires) has the flag equal to `1`
with probability `p ≥ 1/2`, and the normalized flag-`1` branch `p^{−1/2} (|1⟩⟨1|_flag ⊗ I) φ` is
within Euclidean distance `ε` of `|1⟩_flag ⊗ |x⟩ ⊗ |g⟩` for some unit garbage state `g` (the
garbage is arbitrary, so a global phase of the output is absorbed into `g`). -/
def QLSPSuccess {n m : ℕ} (φ : EuclideanSpace ℂ (Qubits (1 + n + m))) (x : EuclideanSpace ℂ (Qubits n))
    (ε : ℝ) : Prop :=
  1 / 2 ≤ probEvent φ (fun z => z (flagWire n m) = true) ∧
    ∃ g : EuclideanSpace ℂ (Qubits m), ‖g‖ = 1 ∧
      ‖(WithLp.toLp 2 fun z => if z (flagWire n m) = true then
            ((Real.sqrt (probEvent φ fun z => z (flagWire n m) = true))⁻¹ : ℂ) * φ z else 0 :
          EuclideanSpace ℂ (Qubits (1 + n + m))) -
        WithLp.toLp 2 fun z => if z (flagWire n m) = true then x (outPart z) * g (garbagePart z)
          else 0‖ ≤ ε

/-! ### Sanity tests -/

/-- The identity is `1`-sparse. -/
example : IsSparse (1 : Matrix (Fin 3) (Fin 3) ℂ) 1 := by
  constructor <;> intro j <;> refine Finset.card_le_one.2 fun a ha b hb => ?_ <;>
    simp [Matrix.one_apply] at ha hb <;> subst ha <;> subst hb <;> rfl

/-- `|b⟩` is a unit vector for `b ≠ 0`. -/
example {ι : Type*} [Fintype ι] (b : EuclideanSpace ℂ ι) (hb : b ≠ 0) : ‖normalizedVec b‖ = 1 := by
  rw [normalizedVec, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (norm_nonneg b))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hb)

/-- Padding a vector on `N = 2ⁿ` indices loses nothing: the basis vector `e_0` becomes `|0ⁿ⟩`. -/
example : padState 1 (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (fun _ => false) = 1 := by
  simp [padState, bitsToNat]

end QAlgorithms


