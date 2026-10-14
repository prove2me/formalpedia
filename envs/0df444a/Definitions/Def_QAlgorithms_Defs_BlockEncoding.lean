-- Prove2me | Definitions.Def_QAlgorithms_Defs_BlockEncoding
-- name    : QAlgorithms_Defs_BlockEncoding
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:45:53.02618+00:00
-- url     : https://prove2.me/theorems/1966b03d-8eec-4f81-ba69-4ffcc1a8b0ce
-- title:
--   Clock Hamiltonian, iterative refinement, block-encodings, state-preparation pairs
-- statement:
--   Clock Hamiltonian, iterative refinement, block-encodings, state-preparation pairs
--
--   ### QAlgorithms.clockHamiltonian
--
--   This is a definition. For $N \in \mathbb{N}$, it is the $N\times N$ complex matrix indexed by $i,j \in \{0,\dots,N-1\}$ with entries
--
--   $$
--   H_{ij} \;=\; \begin{cases} \tfrac12\sqrt{(m+1)(N-m-1)}, \quad m = \min(i,j), & \text{if } |i-j| = 1,\\[2pt] 0 & \text{otherwise.}\end{cases}
--   $$
--
--   When $|i-j|=1$ we have $m \le N-2$, so $N-m-1 \ge 1$ and the natural-number subtraction is exact. Hence the nonzero entries are positive reals, viewed as complex numbers.
--
--   The matrix is real, symmetric and tridiagonal, with zero diagonal. Its off-diagonal entries are
--
--   $$
--   H_{m,m+1} = H_{m+1,m} = \tfrac12\sqrt{(m+1)(N-m-1)} \qquad \text{for } m = 0,\dots,N-2.
--   $$
--
--   The degenerate cases are:
--
--   - For $N=0$, the matrix is empty.
--   - For $N=1$, it is the $1\times1$ zero matrix.
--
--   ### QAlgorithms.mirrorMatrix
--
--   For a natural number $N$, this defines the $N \times N$ complex matrix $M_N$ whose rows and columns are indexed by $\{0, 1, \dots, N-1\}$, with entries
--
--   $$
--   (M_N)_{i,j} = \begin{cases} 1 & \text{if } i = N-1-j, \\ 0 & \text{otherwise.} \end{cases}
--   $$
--
--   So $M_N$ is the anti-diagonal permutation matrix. It has ones on the anti-diagonal and zeros elsewhere, and as an operator it sends the basis vector $e_j$ to $e_{N-1-j}$.
--
--   For $N = 0$ it is the empty matrix. For $N = 1$ it is the $1\times 1$ matrix $(1)$.
--
--   ### QAlgorithms.iterRefineX
--
--   **Inputs.**
--
--   - A natural number $N$.
--   - A complex $N\times N$ matrix $A$, with rows and columns indexed by $\{0,\dots,N-1\}$.
--   - A vector $b \in \mathbb{C}^N$, equipped with the Euclidean norm $\|\cdot\|$.
--   - A sequence $(\hat x_k)_{k \in \mathbb{N}}$ of vectors in $\mathbb{C}^N$.
--
--   **Recursion.** The definition produces a sequence $(x_k)_{k\in\mathbb{N}}$ in $\mathbb{C}^N$:
--
--   $$
--   x_0 = 0, \qquad x_{k+1} = x_k + \|b - A x_k\| \cdot \hat x_{k+1} \quad (k \ge 0).
--   $$
--
--   Here $A x_k$ is the ordinary matrix–vector product. The scalar $\|b - A x_k\|$ is the Euclidean norm of the residual. It is a nonnegative real number used as a complex scalar.
--
--   **Remarks.**
--
--   - The term $\hat x_0$ never enters the recursion.
--   - No condition is placed on $A$, $b$ or the $\hat x_k$. In particular, $A$ need not be invertible, and the $\hat x_k$ need not be normalized or related to $A$ in any way.
--   - If $b - A x_k = 0$ at some step, then $x_{k+1} = x_k$.
--
--   ### QAlgorithms.IsBlockEncoding
--
--   **Inputs.**
--
--   - Finite index sets $\kappa$ (the ancilla index set) and $\iota$ (the system index set), each with decidable equality.
--   - A distinguished ancilla index $z_0 \in \kappa$.
--   - A complex square matrix $U$ indexed by $\kappa \times \iota$.
--   - Real numbers $\alpha$ and $\xi$.
--   - A complex square matrix $A$ indexed by $\iota$.
--
--   **Auxiliary block.** Let $U_{z_0}$ denote the $\iota\times\iota$ block of $U$ obtained by fixing the ancilla index to $z_0$ in both rows and columns:
--
--   $$
--   (U_{z_0})_{i,j} = U_{(z_0,i),(z_0,j)}.
--   $$
--
--   **The predicate.** $\mathrm{IsBlockEncoding}(z_0, U, \alpha, \xi, A)$ holds iff both of the following are true:
--
--   1. $U$ is unitary, i.e. $U^* U = U U^* = I$.
--   2. The following bound holds:
--      $$
--      \big\| \alpha\, U_{z_0} - A \big\|_{\mathrm{op}} \le \xi.
--      $$
--      Here $\|\cdot\|_{\mathrm{op}}$ is the spectral norm, i.e. the operator norm induced by the Euclidean norm (the largest singular value).
--
--   **Edge cases.**
--
--   - No sign condition is imposed on $\alpha$ or $\xi$. If $\xi < 0$, the predicate is unsatisfiable. A negative $\alpha$ is allowed.
--   - If $\iota$ is empty, the norm condition holds for every $\xi \ge 0$.
--
--   ### QAlgorithms.IsStatePrepPair
--
--   **Inputs.**
--
--   - Natural numbers $m$ and $p$.
--   - Real numbers $\beta$ and $\xi$.
--   - A vector $y = (y_0,\dots,y_{m-1}) \in \mathbb{C}^m$.
--   - Two complex $2^p\times 2^p$ matrices $P_L$ and $P_R$, indexed by $p$-bit strings.
--
--   **Notation.**
--
--   - Let $|0^p\rangle$ be the basis vector of the all-zero bit string.
--   - Put $\ell = P_L|0^p\rangle$ and $r = P_R|0^p\rangle$. For a bit string $z$, write $\ell_z$ and $r_z$ for their coordinates.
--   - For a bit string $z = z_0 z_1\cdots z_{p-1}$, let $\mathrm{val}(z) = \sum_i z_i 2^{p-1-i}$ be its value read most-significant-bit first.
--   - For an integer $j$, let $\mathrm{bin}_p(j)$ be the $p$-bit most-significant-first expansion of $j \bmod 2^p$.
--
--   **The predicate.** $\mathrm{IsStatePrepPair}(\beta,\xi,y,P_L,P_R)$ holds iff all of the following are true:
--
--   1. $P_L$ is unitary.
--   2. $P_R$ is unitary.
--   3. $m \le 2^p$, so that $\mathrm{bin}_p(j)$ is the exact binary expansion of $j$ for every $j < m$.
--   4. The entries of $y$ are bounded by $\beta$:
--      $$\sum_{j=0}^{m-1} |y_j| \le \beta.$$
--   5. The products of coordinates approximate $y$ within $\xi$:
--      $$\sum_{j=0}^{m-1} \Big| \beta\, \overline{\ell_{\mathrm{bin}_p(j)}}\; r_{\mathrm{bin}_p(j)} - y_j \Big| \le \xi.$$
--   6. For every $p$-bit string $z$ with $\mathrm{val}(z) \ge m$:
--      $$\overline{\ell_z}\, r_z = 0.$$
--
--   **Consequences.**
--
--   - Conditions 4 and 5 force $\beta \ge 0$ and $\xi \ge 0$.
--   - If $m = 0$, conditions 4 and 5 reduce to $\beta \ge 0$ and $\xi \ge 0$. Condition 6 then applies to all bit strings.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/BlockEncoding.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_GradientMethods
/-!
# Clock Hamiltonian, iterative refinement, block-encodings, state-preparation pairs
(shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapters 6–7. The source's 1-based indices `1, …, N` are `Fin N` (0-based). A
block-encoding puts the auxiliary register **first** (Def. 7.11: `(⟨0|_a ⊗ I) U (|0⟩_a ⊗ I)`).
-/

namespace QAlgorithms

open scoped ComplexConjugate

/-- Nannicini p.135, §6.1.1: the clock Hamiltonian `H_B` in the basis `|u^{(1)}⟩, …, |u^{(N)}⟩`,
the symmetric tridiagonal `N × N` matrix with zero diagonal and
`(H_B)_{j,j+1} = (H_B)_{j+1,j} = ½ √(j(N − j))` for `j = 1, …, N − 1` (1-based); here 0-based,
entry `(i, i+1)` is `½ √((i + 1)(N − i − 1))` (the subtraction is in `ℕ` and never truncates, as
`i + 1 < N`). -/
noncomputable def clockHamiltonian (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then
      ((2⁻¹ * Real.sqrt (((min (i : ℕ) j + 1) * (N - min (i : ℕ) j - 1) : ℕ) : ℝ) : ℝ) : ℂ)
    else 0

/-- Nannicini p.136, §6.1.1: the mirror matrix `M_s = Σ_j |u^{(j)}⟩⟨u^{(N+1−j)}|`, which sends the
`j`-th basis vector to the `(N + 1 − j)`-th; 0-based, `i ↦ N − 1 − i` (`Fin.rev`). An eigenvector
`ψ` of `H_B` is symmetric iff `M_s ψ = ψ`, antisymmetric iff `M_s ψ = −ψ`. -/
def mirrorMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if i = Fin.rev j then 1 else 0

/-- Nannicini p.158, Alg. 5: the iterates of iterative refinement for `Ax = b`:
`x^{(0)} = 0` and `x^{(k)} = x^{(k−1)} + ‖r^{(k−1)}‖ x̂^{(k)}` with the residual
`r^{(k−1)} = b − A x^{(k−1)}`, where `xhat k` is the solver output `x̂^{(k)}` used at iteration
`k ≥ 1` (`xhat 0` is never read). -/
noncomputable def iterRefineX {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (b : EuclideanSpace ℂ (Fin N))
    (xhat : ℕ → EuclideanSpace ℂ (Fin N)) : ℕ → EuclideanSpace ℂ (Fin N)
  | 0 => 0
  | k + 1 => iterRefineX A b xhat k + (‖b - act A (iterRefineX A b xhat k)‖ : ℂ) • xhat (k + 1)

/-- Nannicini p.159, Defs. 7.10–7.11: `U` is an `(α, a, ξ)`-block-encoding of `A`: `U` is unitary
and `‖α (⟨0⃗|_a ⊗ I) U (|0⃗⟩_a ⊗ I) − A‖ ≤ ξ` in the operator norm (frozen `specNorm`), the
auxiliary register (index type `κ`, all-zero element `z0`) first. The source's form is
`κ = Qubits a`, `z0 = 0`; a composite auxiliary register uses its all-zero element. -/
def IsBlockEncoding {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] (z0 : κ)
    (U : Matrix (κ × ι) (κ × ι) ℂ) (α ξ : ℝ) (A : Matrix ι ι ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (κ × ι) ℂ ∧
    specNorm ((α : ℂ) • (Matrix.of fun i j => U (z0, i) (z0, j)) - A) ≤ ξ

/-- Nannicini p.161, Def. 7.16: `(P_L, P_R)` is a `(β, p, ξ)`-state-preparation pair for
`y ∈ ℂ^m` (0-based): `P_L, P_R` are `p`-qubit unitaries, `‖y‖₁ ≤ β`, and with
`P_L|0⟩ = Σ_j c_j|j⟩`, `P_R|0⟩ = Σ_j d_j|j⟩` (index `j` ↔ the integer `bitsToNat j`),
`Σ_{j=0}^{m−1} |β c_j^† d_j − y_j| ≤ ξ` and `c_j^† d_j = 0` for `j = m, …, 2^p − 1`. The
definition also records `m ≤ 2^p`, implicit in the source (the coefficients `c_j, d_j` exist only
for `j < 2^p`). -/
def IsStatePrepPair {m p : ℕ} (β ξ : ℝ) (y : Fin m → ℂ) (PL PR : Matrix (Qubits p) (Qubits p) ℂ) :
    Prop :=
  PL ∈ Matrix.unitaryGroup (Qubits p) ℂ ∧ PR ∈ Matrix.unitaryGroup (Qubits p) ℂ ∧ m ≤ 2 ^ p ∧
    ∑ j, ‖y j‖ ≤ β ∧
    ∑ j : Fin m, ‖(β : ℂ) * conj (act PL (zeroKet p) (natToBits p j)) *
        act PR (zeroKet p) (natToBits p j) - y j‖ ≤ ξ ∧
    ∀ j : Qubits p, m ≤ bitsToNat j → conj (act PL (zeroKet p) j) * act PR (zeroKet p) j = 0

/-! ### Sanity tests -/

example : clockHamiltonian 2 0 1 = 2⁻¹ ∧ clockHamiltonian 2 1 0 = 2⁻¹ ∧
    clockHamiltonian 2 0 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [clockHamiltonian]

example : mirrorMatrix 2 0 1 = 1 ∧ mirrorMatrix 2 0 0 = 0 := by
  constructor <;> simp [mirrorMatrix] <;> decide

example {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (b : EuclideanSpace ℂ (Fin N))
    (xhat : ℕ → EuclideanSpace ℂ (Fin N)) : iterRefineX A b xhat 1 = (‖b‖ : ℂ) • xhat 1 := by
  simp [iterRefineX, act]

example {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] (z0 : κ) :
    IsBlockEncoding z0 (1 : Matrix (κ × ι) (κ × ι) ℂ) 1 0 1 := by
  refine ⟨one_mem _, ?_⟩
  have h : ((1 : ℝ) : ℂ) • (Matrix.of fun i j : ι => (1 : Matrix (κ × ι) (κ × ι) ℂ) (z0, i) (z0, j)) -
      1 = 0 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [h, specNorm]
  letI : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.instL2OpNormedAddCommGroup
  exact le_of_eq norm_zero

end QAlgorithms


