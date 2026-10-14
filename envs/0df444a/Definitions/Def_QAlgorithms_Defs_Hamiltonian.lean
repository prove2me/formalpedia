-- Prove2me | Definitions.Def_QAlgorithms_Defs_Hamiltonian
-- name    : QAlgorithms_Defs_Hamiltonian
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:34:12.658643+00:00
-- url     : https://prove2.me/theorems/d51c9426-92d0-4d26-bb78-f5588d05f823
-- title:
--   Hamiltonians, spectral gaps, adiabatic evolution, quantum signal processing
-- statement:
--   Hamiltonians, spectral gaps, adiabatic evolution, quantum signal processing
--
--   ### QAlgorithms.ascEigenvalues
--
--   This definition takes a square matrix $A$ with entries in $\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ (any "RCLike" field). The rows and columns of $A$ are indexed by a finite type $\iota$ with decidable equality. Write $N = |\iota|$. The result is a real-valued sequence indexed by $\{0, 1, \dots, N-1\}$.
--
--   - **If $A$ is Hermitian** ($A^* = A$): let $\mu_0 \ge \mu_1 \ge \dots \ge \mu_{N-1}$ be the eigenvalues of $A$ in decreasing order, repeated according to multiplicity. These are what the library's standard eigenvalue list returns. The definition reverses that order, giving
--   $$\lambda_k(A) = \mu_{N-1-k}, \qquad k = 0, \dots, N-1.$$
--   So $\lambda_0(A) \le \lambda_1(A) \le \dots \le \lambda_{N-1}(A)$ are the eigenvalues in ascending order, with multiplicity.
--   - **If $A$ is not Hermitian**, the result is the constant zero sequence: $\lambda_k(A) = 0$ for all $k$.
--
--   If $\iota$ is empty ($N = 0$), the sequence has no entries.
--
--   ### QAlgorithms.minEigenvalue
--
--   This definition takes a square matrix $A$ over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, indexed by a finite type $\iota$ with decidable equality. It returns a real number $\lambda_{\min}(A)$:
--   $$\lambda_{\min}(A) = \begin{cases} \lambda_0(A) & \text{if } |\iota| > 0,\\ 0 & \text{if } \iota \text{ is empty.}\end{cases}$$
--   Here $\lambda_0(A)$ is the first entry of the ascending eigenvalue sequence from `ascEigenvalues`.
--
--   Unfolding that definition gives two cases:
--
--   - For a Hermitian $A$ of positive size, $\lambda_{\min}(A)$ is the smallest eigenvalue of $A$.
--   - For a non-Hermitian $A$, $\lambda_{\min}(A) = 0$ by convention, whatever its actual spectrum.
--
--   ### QAlgorithms.spectralGap
--
--   This definition takes a square matrix $A$ over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, indexed by a finite type $\iota$ with decidable equality. It returns the real number
--   $$\operatorname{gap}(A) = \begin{cases} \lambda_1(A) - \lambda_0(A) & \text{if } |\iota| \ge 2,\\ 0 & \text{if } |\iota| \le 1.\end{cases}$$
--   Here $\lambda_0(A) \le \lambda_1(A)$ are the first two entries of the ascending eigenvalue sequence from `ascEigenvalues`.
--
--   For a Hermitian $A$, this is the second-smallest eigenvalue minus the smallest one, counted with multiplicity. In particular, $\operatorname{gap}(A) = 0$ whenever the smallest eigenvalue has multiplicity at least 2.
--
--   For a non-Hermitian $A$, both eigenvalue entries are $0$ by convention, so $\operatorname{gap}(A) = 0$.
--
--   ### QAlgorithms.HasSimpleGroundState
--
--   This is a property of a square matrix $A$ over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, indexed by a finite type $\iota$ with decidable equality. It holds exactly when all three of the following hold:
--
--   1. $A$ is Hermitian;
--   2. $|\iota| \ge 2$;
--   3. $\operatorname{gap}(A) > 0$, i.e. $\lambda_1(A) - \lambda_0(A) > 0$.
--
--   Here $\lambda_0(A) \le \lambda_1(A)$ are the two smallest eigenvalues of $A$, counted with multiplicity. Given (1) and (2), condition (3) says the smallest eigenvalue of $A$ is strictly smaller than the next one in the multiplicity-counted list. Equivalently, the smallest eigenvalue has multiplicity exactly one.
--
--   ### QAlgorithms.IsGroundState
--
--   This is a property of a complex square matrix $A$ indexed by a finite type $\iota$ with decidable equality, and a vector $\varphi \in \mathbb{C}^{\iota}$ with the Euclidean norm. It holds exactly when:
--
--   1. $\varphi$ is a unit vector: $\|\varphi\| = 1$;
--   2. $A\varphi = \lambda_{\min}(A)\,\varphi$, where $\lambda_{\min}(A)$ is the real number from `minEigenvalue`, viewed as a complex scalar.
--
--   No hypothesis requires $A$ to be Hermitian. If $A$ is not Hermitian, then $\lambda_{\min}(A) = 0$ by convention, so the condition becomes "$\varphi$ is a unit vector with $A\varphi = 0$."
--
--   If $\iota$ is empty, no unit vector exists, so the property is never satisfied.
--
--   ### QAlgorithms.SolvesScaledSchrodinger
--
--   The inputs are:
--
--   - a finite index type $\iota$;
--   - a family $s \mapsto H(s)$ of complex $\iota \times \iota$ matrices, defined for all real $s$;
--   - a real number $T$;
--   - a curve $s \mapsto \psi(s) \in \mathbb{C}^{\iota}$, defined for all real $s$.
--
--   The property holds when, for every $s \in [0,1]$, the curve $\psi$ has derivative within the closed interval $[0,1]$ at $s$ equal to
--   $$\psi'(s) = -i\,T\,H(s)\,\psi(s).$$
--   Because the derivative is taken within $[0,1]$, it is a one-sided derivative at the endpoints $s = 0$ and $s = 1$, and the values of $\psi$ outside $[0,1]$ play no role.
--
--   Several things are not required:
--
--   - There is no initial condition on $\psi(0)$.
--   - There is no requirement that $H(s)$ be Hermitian, or continuous in $s$.
--   - There is no sign restriction on $T$. For $T = 0$ the condition says $\psi$ has zero derivative on $[0,1]$.
--
--   ### QAlgorithms.problemHamiltonian
--
--   This definition takes a natural number $n$ and a real-valued function $h$ on $n$-bit strings $z \in \{0,1\}^n$. The bit strings are modelled as functions from $\{0, \dots, n-1\}$ to the Booleans.
--
--   The result is the complex $2^n \times 2^n$ matrix, rows and columns indexed by $n$-bit strings, that is diagonal with entries given by $h$:
--   $$H_P = \operatorname{diag}\big(h(z)\big)_{z \in \{0,1\}^n}, \qquad (H_P)_{z,z'} = \begin{cases} h(z) & z = z',\\ 0 & z \ne z'.\end{cases}$$
--
--   For $n = 0$ this is the $1 \times 1$ matrix whose single entry is $h$ evaluated at the empty string.
--
--   ### QAlgorithms.linInterp
--
--   This definition takes two complex square matrices $H_B$ and $H_P$ indexed by the same type $\iota$, and a real number $s$. It returns
--   $$H(s) = (1 - s)\,H_B + s\,H_P.$$
--   The parameter $s$ is not restricted to $[0,1]$; the formula is defined for every real $s$.
--
--   ### QAlgorithms.minGap
--
--   This definition takes a finite index type $\iota$ with decidable equality and a family $s \mapsto H(s)$ of complex $\iota \times \iota$ matrices. It returns the real number
--   $$\inf\{\operatorname{gap}(H(s)) : s \in [0,1]\}.$$
--   Here $\operatorname{gap}$ is the `spectralGap` function, so the following conventions carry over:
--
--   - $\operatorname{gap}(H(s)) = \lambda_1(H(s)) - \lambda_0(H(s))$ when $H(s)$ is Hermitian and $|\iota| \ge 2$.
--   - $\operatorname{gap}(H(s)) = 0$ when $H(s)$ is not Hermitian or $|\iota| \le 1$.
--
--   The set being minimised is nonempty, and all its elements are $\ge 0$. So the infimum is a genuine greatest lower bound. It need not be attained by any particular $s$.
--
--   A single $s \in [0,1]$ at which $H(s)$ fails to be Hermitian, or has a degenerate smallest eigenvalue, already forces the value to be $0$.
--
--   ### QAlgorithms.clockPathMatrix
--
--   This definition takes a natural number $k$ and a real number $s$. It returns the real $(k+1) \times (k+1)$ matrix $M$ with rows and columns indexed by $0, 1, \dots, k$, whose entries are:
--   $$M_{i,j} = \begin{cases} s - 1 & \text{if } i = j = 0,\\ -s & \text{if } |i - j| = 1,\\ 0 & \text{otherwise.}\end{cases}$$
--   So $M$ is symmetric and tridiagonal:
--
--   - its only nonzero diagonal entry is the top-left one, $s - 1$;
--   - every entry on the sub- and super-diagonal equals $-s$.
--
--   For $k = 0$ it is the $1 \times 1$ matrix $(s - 1)$. The parameter $s$ ranges over all reals.
--
--   ### QAlgorithms.qspW
--
--   This definition takes a real number $x$ and returns the complex $2 \times 2$ matrix
--   $$W(x) = \begin{pmatrix} x & i\sqrt{1 - x^2} \\ i\sqrt{1 - x^2} & x \end{pmatrix}.$$
--   Here $\sqrt{\cdot}$ is the real square root with the convention that $\sqrt{t} = 0$ for $t < 0$.
--
--   So for $|x| \le 1$ this is the usual matrix above. For $|x| > 1$, the off-diagonal entries are $0$ and $W(x) = x I_2$.
--
--   ### QAlgorithms.qspZ
--
--   This definition takes a real number $\phi$ and returns the complex $2 \times 2$ diagonal matrix
--   $$Z(\phi) = \begin{pmatrix} e^{i\phi} & 0 \\ 0 & e^{-i\phi} \end{pmatrix}.$$
--
--   ### QAlgorithms.qspSequence
--
--   This is a definition, not a theorem. It takes a natural number $k$, a list of $k+1$ real angles $\Phi = (\Phi_0, \Phi_1, \dots, \Phi_k)$, and a real number $x$. It returns a $2\times 2$ complex matrix, with rows and columns indexed by $\{0,1\}$.
--
--   It uses two auxiliary matrices. The first is the "signal" matrix
--   $$
--   W(x) = \begin{pmatrix} x & i\sqrt{1-x^2} \\ i\sqrt{1-x^2} & x \end{pmatrix}.
--   $$
--   Here $\sqrt{\cdot}$ is the real square root, which is defined to be $0$ on negative inputs. So for $|x| > 1$ the off-diagonal entries are $0$ and $W(x) = x\,I$. The second is the phase matrix
--   $$
--   Z(\varphi) = \begin{pmatrix} e^{i\varphi} & 0 \\ 0 & e^{-i\varphi} \end{pmatrix}.
--   $$
--
--   The output is the ordered product, multiplied left to right in index order:
--   $$
--   \mathrm{QSP}_\Phi(x) = Z(\Phi_0)\cdot W(x)Z(\Phi_1)\cdot W(x)Z(\Phi_2)\cdots W(x)Z(\Phi_k).
--   $$
--   This contains exactly $k$ copies of $W(x)$. When $k=0$ the result is just $Z(\Phi_0)$.
--
--   ### QAlgorithms.HasParity
--
--   This is a definition of a property of a complex polynomial $P \in \mathbb{C}[X]$ and a natural number $k$. It holds exactly when substituting $-X$ for $X$ in $P$ gives $(-1)^k$ times $P$, as an identity of polynomials:
--   $$
--   P(-X) = (-1)^k\, P(X).
--   $$
--
--   - For even $k$ this says $P$ is an even polynomial, with only even-degree coefficients nonzero.
--   - For odd $k$ it says $P$ is odd, with only odd-degree coefficients nonzero.
--   - Only the parity of $k$ matters. No relation between $k$ and the degree of $P$ is imposed.
--   - The zero polynomial satisfies the property for every $k$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Hamiltonian.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_CompressedOracle
/-!
# Hamiltonians, spectral gaps, adiabatic evolution, quantum signal processing
(shared definition layer)

Hermiticity is Mathlib's `Matrix.IsHermitian`; it is a hypothesis of the statements (or part of
`HasSimpleGroundState`). Eigenvalues are counted with multiplicity and sorted increasingly.
-/

namespace QAlgorithms

/-- Childs p.162 (§30.3), p.182 (Lemma 33.1), de Wolf p.129 (§14.2): the eigenvalues of a Hermitian
matrix, counted with multiplicity, in increasing order (Mathlib's `IsHermitian.eigenvalues₀` is
decreasing; it is composed with `Fin.rev`). For a non-Hermitian matrix the value is `0`
(statements assume `IsHermitian`). -/
noncomputable def ascEigenvalues {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : Fin (Fintype.card ι) → ℝ :=
  open Classical in
  if h : A.IsHermitian then fun k => h.eigenvalues₀ (Fin.rev k) else 0

/-- Childs p.160 (§30.1, "the instantaneous ground state energy" `E(s)`), p.182, de Wolf p.129:
the smallest eigenvalue `λ_min(A)` of a Hermitian matrix (`0` on the empty index type, which
statements exclude). -/
noncomputable def minEigenvalue {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : ℝ :=
  if h : 0 < Fintype.card ι then ascEigenvalues A ⟨0, h⟩ else 0

/-- Childs p.162 (§30.2: "the gap between the smallest eigenvalue `E(s)` of `H(s)` and the nearest
distinct eigenvalue"), p.166 (§31.2: "the gap between the ground and first excited states"),
p.182 (Lemma 33.1): the second smallest minus the smallest eigenvalue, counted with multiplicity
(so a degenerate ground level has gap `0`); `0` if there are fewer than two eigenvalues. Under
`HasSimpleGroundState` it is the source's gap. -/
noncomputable def spectralGap {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : ℝ :=
  if h : 2 ≤ Fintype.card ι then ascEigenvalues A ⟨1, h⟩ - ascEigenvalues A ⟨0, by omega⟩ else 0

/-- Childs p.160 (§30.1: "the ground state of `H(s)` is nondegenerate"): `A` is Hermitian, acts on a
space of dimension at least two, and its smallest eigenvalue is simple. -/
def HasSimpleGroundState {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : Prop :=
  A.IsHermitian ∧ 2 ≤ Fintype.card ι ∧ 0 < spectralGap A

/-- Childs p.160 ((30.6)): `φ` is a ground state of `A`: a unit vector with `A φ = λ_min(A) φ`. -/
def IsGroundState {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (φ : EuclideanSpace ℂ ι) : Prop :=
  IsState φ ∧ act A φ = (minEigenvalue A : ℂ) • φ

/-- Childs p.159–160 ((30.5)): `ψ` solves the Schrödinger equation in rescaled time,
`i dψ/ds = T H(s) ψ(s)` for `s ∈ [0, 1]` (one-sided derivatives at the endpoints), i.e.
`dψ/ds = −i T H(s) ψ(s)` (sign convention `e^{−iHt}`, (30.2); trap Q12). The derivatives
`Ḣ(s), Ḧ(s)` of the statements are `derivWithin` on `[0, 1]`. -/
def SolvesScaledSchrodinger {ι : Type*} [Fintype ι] (H : ℝ → Matrix ι ι ℂ) (T : ℝ)
    (ψ : ℝ → EuclideanSpace ℂ ι) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt ψ (-Complex.I • (T : ℂ) • act (H s) (ψ s)) (Set.Icc 0 1) s

/-- Childs p.165 ((31.2)): the problem Hamiltonian `H_P = Σ_z h(z) |z⟩⟨z|`. -/
def problemHamiltonian {n : ℕ} (h : Qubits n → ℝ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal fun z => (h z : ℂ)

/-- Childs p.165–166 ((31.3) with `f(s) = s`), p.181 ((33.13)): the linear interpolation
`H(s) = (1 − s) H_B + s H_P`. -/
def linInterp {ι : Type*} (HB HP : Matrix ι ι ℂ) (s : ℝ) : Matrix ι ι ℂ :=
  ((1 - s : ℝ) : ℂ) • HB + (s : ℂ) • HP

/-- Childs p.166 ((31.8)): `∆_min = min_{s ∈ [0,1]} ∆(s)`, as the infimum of the gaps over `[0, 1]`
(a nonempty set of nonnegative reals, so the infimum is not a junk value; it is attained when
`H` is continuous). -/
noncomputable def minGap {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ℝ → Matrix ι ι ℂ) : ℝ :=
  sInf ((fun s => spectralGap (H s)) '' Set.Icc 0 1)

/-- Childs p.181 ((33.14)–(33.16)): the restriction of `(1 − s) H_B + s H_C` to the computational
subspace `span{|ψ_0⟩, …, |ψ_k⟩}`: entry `(0, 0)` is `s − 1`, the entries `(j, j + 1)` and
`(j + 1, j)` are `−s`, all others are `0`. -/
def clockPathMatrix (k : ℕ) (s : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then s - 1
    else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -s else 0

/-- Childs p.152 ((29.6)): the signal rotation `W(x) = [[x, i√(1 − x²)], [i√(1 − x²), x]]`
(for the source's `x ∈ [−1, 1]`). -/
noncomputable def qspW (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x : ℂ), Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ); Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)]

/-- Childs p.152 ((29.7)): the `z` rotation `e^{iϕσ_z} = diag(e^{iϕ}, e^{−iϕ})`. -/
noncomputable def qspZ (ϕ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (ϕ * Complex.I), 0; 0, Complex.exp (-(ϕ * Complex.I))]

/-- Childs p.152 ((29.7)): `W_Φ(x) = e^{iϕ_0σ_z} W(x) e^{iϕ_1σ_z} W(x) ⋯ W(x) e^{iϕ_kσ_z}` for
`Φ = (ϕ_0, …, ϕ_k)` (`k` factors `W(x)`). -/
noncomputable def qspSequence {k : ℕ} (Φ : Fin (k + 1) → ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (List.ofFn fun i : Fin (k + 1) => if i = 0 then qspZ (Φ i) else qspW x * qspZ (Φ i)).prod

/-- Childs p.153 (Lemma 29.1: "an even function has parity 0 and an odd function has parity 1"):
`P` has parity `k mod 2`, i.e. `P(−x) = (−1)^k P(x)`. -/
def HasParity (P : Polynomial ℂ) (k : ℕ) : Prop :=
  P.comp (-Polynomial.X) = (-1 : ℂ) ^ k • P

/-! ### Sanity tests -/

example : clockPathMatrix 2 0 = Matrix.diagonal ![-1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [clockPathMatrix]

/-- With `k = 0` (no `W(x)` factors), `W_Φ(x) = e^{iϕ_0σ_z}` (Childs p.152, base case). -/
example (Φ : Fin 1 → ℝ) (x : ℝ) : qspSequence Φ x = qspZ (Φ 0) := by
  simp [qspSequence]

example (Φ : Fin 2 → ℝ) (x : ℝ) : qspSequence Φ x = qspZ (Φ 0) * (qspW x * qspZ (Φ 1)) := by
  simp [qspSequence, List.ofFn_succ]

/-- An even polynomial (here `X²`) has parity `0`. -/
example : HasParity (Polynomial.X ^ 2) 0 := by
  simp [HasParity]

/-- The eigenvalues of `diag(2, 1)` in increasing order are `1, 2`, so its gap is `1`. -/
example : ascEigenvalues (Matrix.diagonal ![(2 : ℂ), 1]) ⟨0, by simp⟩ ≤
    ascEigenvalues (Matrix.diagonal ![(2 : ℂ), 1]) ⟨1, by simp⟩ := by
  have h : (Matrix.diagonal ![(2 : ℂ), 1]).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i; fin_cases i <;> simp
  simp only [ascEigenvalues, dif_pos h]
  exact h.eigenvalues₀_antitone (Fin.rev_le_rev.2 (by simp [Fin.le_def]))

example {n : ℕ} (h : Qubits n → ℝ) : (problemHamiltonian h).IsHermitian := by
  rw [problemHamiltonian, Matrix.isHermitian_diagonal_iff]
  intro z; simp [IsSelfAdjoint]

end QAlgorithms


