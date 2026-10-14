-- Prove2me | Definitions.Def_QAlgorithms_Defs_Information
-- name    : QAlgorithms_Defs_Information
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:36:15.947345+00:00
-- url     : https://prove2.me/theorems/e733c0f6-ceca-4260-b927-7dac5d35983f
-- title:
--   Mixed states, measurements, encodings (shared definition layer)
-- statement:
--   Mixed states, measurements, encodings (shared definition layer)
--
--   ### QAlgorithms.IsDensityMatrix
--
--   Let $\iota$ be any finite index type and $\rho$ a complex square matrix with rows and columns indexed by $\iota$. The predicate states that $\rho$ is a **density matrix**, meaning both of the following hold:
--
--   1. $\rho$ is positive semidefinite. This means $\rho$ is Hermitian ($\rho^\dagger = \rho$) and $v^\dagger \rho v$ is a nonnegative real number for every $v \in \mathbb{C}^\iota$.
--   2. $\operatorname{tr}\rho = 1$, as an equality of complex numbers.
--
--   If $\iota$ is empty, the trace is $0$, so no matrix satisfies the predicate.
--
--   ### QAlgorithms.IsEffect
--
--   Let $\iota$ be a finite index type with decidable equality and $M$ a complex $\iota \times \iota$ matrix. The predicate states that $M$ is an **effect**: both $M$ and $I - M$ are positive semidefinite. Here $I$ is the $\iota \times \iota$ identity matrix, and positive semidefinite means Hermitian with $v^\dagger X v \ge 0$ for every $v$. Equivalently, in the Loewner order,
--
--   $$0 \preceq M \preceq I.$$
--
--   ### QAlgorithms.effectProb
--
--   For a finite index type $\iota$ and two arbitrary complex $\iota \times \iota$ matrices $M$ and $\rho$, this defines the real number
--
--   $$\operatorname{effectProb}(M,\rho) = \operatorname{Re}\,\operatorname{tr}(M\rho).$$
--
--   No hypotheses are imposed. Neither matrix needs to be an effect or a density matrix, so the value need not lie in $[0,1]$. The imaginary part of the trace is discarded.
--
--   ### QAlgorithms.pureDensity
--
--   For an arbitrary index type $\iota$ and a vector $\psi \in \mathbb{C}^\iota$ (an element of the Euclidean space over $\iota$), this defines the $\iota \times \iota$ complex matrix with entries
--
--   $$\big(\operatorname{pureDensity}(\psi)\big)_{a,b} = \psi_a\,\overline{\psi_b}.$$
--
--   This is the outer product $|\psi\rangle\langle\psi|$. The vector $\psi$ is not required to be normalized, so the trace of this matrix is $\|\psi\|^2$, which need not equal $1$.
--
--   ### QAlgorithms.traceLeft
--
--   Let $\alpha$ be a finite type and $\beta$ an arbitrary type. For a complex matrix $M$ indexed by pairs $(\alpha \times \beta) \times (\alpha \times \beta)$, this defines the $\beta \times \beta$ matrix with entries
--
--   $$\big(\operatorname{traceLeft}(M)\big)_{b,b'} = \sum_{a \in \alpha} M_{(a,b),(a,b')}.$$
--
--   This is the partial trace over the first tensor factor $\alpha$. It is defined for every matrix, with no positivity or trace assumptions.
--
--   ### QAlgorithms.binEntropy2
--
--   For any real number $p$, this defines
--
--   $$\operatorname{binEntropy2}(p) = \frac{-p\ln p - (1-p)\ln(1-p)}{\ln 2},$$
--
--   which is the binary entropy measured in bits. The logarithm follows the convention that $\ln 0 = 0$ and $\ln x = \ln|x|$ for $x < 0$. Consequently:
--
--   - The endpoints give $\operatorname{binEntropy2}(0) = \operatorname{binEntropy2}(1) = 0$.
--   - For $p$ outside $[0,1]$, the function still returns a value, computed with $\ln|\cdot|$, rather than being undefined.
--
--   ### QAlgorithms.IsQRAC
--
--   Let $n, m$ be natural numbers and $p$ a real number. Let $\rho$ be a function assigning to each bit string $x \in \{0,1\}^n$ a complex $2^m \times 2^m$ matrix $\rho_x$, with rows and columns indexed by $m$-bit strings. The predicate holds when both of the following are true:
--
--   1. **Valid states.** For every $x \in \{0,1\}^n$, $\rho_x$ is a density matrix: positive semidefinite (Hermitian with $v^\dagger \rho_x v \ge 0$ for all $v$) and of trace $1$.
--   2. **Good decoding of every bit.** For every index $i \in \{0,\dots,n-1\}$, there exists a matrix $M$ (allowed to depend on $i$) with $0 \preceq M \preceq I$, that is, both $M$ and $I-M$ positive semidefinite, such that
--   $$\frac{1}{2^n}\sum_{x \in \{0,1\}^n} s_i(x) \;\ge\; p,
--   \qquad
--   s_i(x) = \begin{cases} \operatorname{Re}\operatorname{tr}(M\rho_x) & \text{if } x_i = 1,\\[2pt] 1 - \operatorname{Re}\operatorname{tr}(M\rho_x) & \text{if } x_i = 0.\end{cases}$$
--
--   The quantity on the left is a uniform average over $x$; it is not a worst case over $x$. The predicate places no restriction on $p$.
--
--   If $n = 0$, condition 2 is vacuous, so any assignment of a density matrix to the single empty string satisfies the predicate for every $p$.
--
--   ### QAlgorithms.IsLDC
--
--   Let $n, N, q$ be natural numbers and $\delta, \varepsilon$ real numbers. Let $C$ be a map from $n$-bit strings to $N$-bit strings. The predicate holds when, for every index $i \in \{0,\dots,n-1\}$, there exists a probability distribution $R$ over (deterministic) decision trees with two properties.
--
--   Each decision tree is of the following kind:
--
--   - Each internal node queries a position in $\{0,\dots,N-1\}$ of a string $y \in \{0,1\}^N$ and branches on the bit read.
--   - Each leaf outputs a bit.
--   - The number of queries a tree makes on input $y$ is the number of internal nodes on the path that $y$ follows. A position queried more than once is counted each time.
--
--   The two properties required of $R$ are:
--
--   1. **Query bound.** Every tree $t$ in the support of $R$ makes at most $q$ queries on every input $y \in \{0,1\}^N$.
--   2. **Decoding guarantee.** For all $x \in \{0,1\}^n$ and $y \in \{0,1\}^N$ with Hamming distance $d_H(C(x), y) \le \delta N$, the decoder succeeds with probability at least $\tfrac12 + \varepsilon$:
--   $$\Pr_{t \sim R}\big[\, t(y) = x_i \,\big] \;\ge\; \tfrac12 + \varepsilon.$$
--   Here $t(y)$ is the leaf value reached on input $y$, and the probability is converted to a real number.
--
--   Several cases are degenerate:
--
--   - **$n = 0$:** the condition is vacuous, so every $C$ qualifies.
--   - **$\delta < 0$ and $N > 0$:** no $y$ satisfies the distance hypothesis, so condition 2 is vacuous.
--   - **$N = 0$:** the hypothesis reads $0 \le 0$ and always applies.
--   - **$\varepsilon \le -\tfrac12$:** condition 2 holds trivially.
--   - **$\varepsilon > \tfrac12$:** condition 2 cannot hold unless it is vacuous.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Information.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Walk
/-!
# Mixed states, measurements, encodings (shared definition layer)
-/

namespace QAlgorithms

open scoped ComplexConjugate ComplexOrder

/-- de Wolf p.139 (§15.1: "the set of density matrices is exactly the set of positive semidefinite
matrices of trace 1"): `ρ` is a density matrix. -/
def IsDensityMatrix {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- de Wolf p.140 (§15.1), p.141 (§15.2: "a measurement `{M_i, I − M_i}`"): `M` is the first
operator of a two-outcome POVM `{M, I − M}`: `0 ⪯ M ⪯ I`. -/
def IsEffect {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : Prop :=
  M.PosSemidef ∧ (1 - M).PosSemidef

/-- de Wolf p.140 (§15.1): the probability `Tr(Mρ)` of the outcome with POVM operator `M` when
measuring `ρ` (a real number for an effect `M` and a density matrix `ρ`; its real part). -/
noncomputable def effectProb {ι : Type*} [Fintype ι] (M ρ : Matrix ι ι ℂ) : ℝ :=
  (M * ρ).trace.re

/-- de Wolf p.139 (§15.1): the density matrix `|ψ⟩⟨ψ|` of a pure state. -/
noncomputable def pureDensity {ι : Type*} (ψ : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.of fun a b => ψ a * conj (ψ b)

/-- de Wolf p.170 (§18.1: "tracing out Alice's part of the space: `ρ_B = Tr_A(ρ_AB)`"), p.172:
the partial trace over the first tensor factor, `(Tr_A M)_{b b'} = Σ_a M_{(a,b),(a,b')}`. -/
def traceLeft {α β : Type*} [Fintype α] (M : Matrix (α × β) (α × β) ℂ) : Matrix β β ℂ :=
  Matrix.of fun b b' => ∑ a, M (a, b) (a, b')

/-- de Wolf p.142 (Theorem 4): the binary entropy in bits,
`H(p) = −p log₂ p − (1 − p) log₂(1 − p)` (Mathlib's `Real.binEntropy` is in nats; `0 log 0 = 0`). -/
noncomputable def binEntropy2 (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

/-- de Wolf p.141–142 (§15.2, Theorem 4): `x ↦ ρ_x` encodes `n`-bit strings into `m`-qubit states
such that, for each `i`, some two-outcome measurement `{M_i, I − M_i}` (`M_i` = output `1`)
recovers `x_i` with success probability at least `p` averaged over a uniformly random `x` (an
average, as Theorem 4 says, not a worst-case guarantee). -/
def IsQRAC {n m : ℕ} (ρ : (Fin n → Bool) → Matrix (Qubits m) (Qubits m) ℂ) (p : ℝ) : Prop :=
  (∀ x, IsDensityMatrix (ρ x)) ∧
    ∀ i : Fin n, ∃ M : Matrix (Qubits m) (Qubits m) ℂ, IsEffect M ∧
      ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool,
        (if x i then effectProb M (ρ x) else 1 - effectProb M (ρ x)) ≥ p

/-- de Wolf p.142 (Definition 3), p.143: `C : {0,1}ⁿ → {0,1}^N` is a `(q, δ, ε)`-locally decodable
code: a classical randomized decoder, which knows `i` (so one randomized decision tree per `i`)
and may query the `N`-bit string `y` adaptively at most `q` times, outputs `x_i` with probability
at least `1/2 + ε` for every `x`, every `i` and every `y` within Hamming distance `δN` of `C(x)`. -/
def IsLDC {n N : ℕ} (q : ℕ) (δ ε : ℝ) (C : (Fin n → Bool) → (Fin N → Bool)) : Prop :=
  ∀ i : Fin n, ∃ R : RandDecisionTree (Fin N) Bool Bool, RandMakesAtMost R q ∧
    ∀ (x : Fin n → Bool) (y : Fin N → Bool), (hammingDist (C x) y : ℝ) ≤ δ * N →
      successProb R y (x i) ≥ 1 / 2 + ε

/-! ### Sanity tests -/

/-- `Tr_A(C ⊗ D) = Tr(C) D`. -/
example {α β : Type*} [Fintype α] (C : Matrix α α ℂ) (D : Matrix β β ℂ) :
    traceLeft (Matrix.kronecker C D) = C.trace • D := by
  ext b b'
  simp [traceLeft, Matrix.kronecker, Matrix.trace, Finset.sum_mul]

/-- The binary entropy of a fair coin is one bit. -/
example : binEntropy2 (1 / 2) = 1 := by
  rw [binEntropy2, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

/-- The identity is an effect (the measurement that always outputs `1`). -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] : IsEffect (1 : Matrix ι ι ℂ) := by
  refine ⟨Matrix.PosSemidef.one, ?_⟩
  rw [sub_self]
  exact Matrix.PosSemidef.zero

/-- A basis state gives a pure density matrix with a single `1` on the diagonal. -/
example {ι : Type*} [DecidableEq ι] (i : ι) : pureDensity (ket (ι := ι) i) i i = 1 := by
  simp [pureDensity, ket]

end QAlgorithms


