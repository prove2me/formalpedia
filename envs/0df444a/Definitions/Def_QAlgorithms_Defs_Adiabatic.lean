-- Prove2me | Definitions.Def_QAlgorithms_Defs_Adiabatic
-- name    : QAlgorithms_Defs_Adiabatic
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:50:19.07499+00:00
-- url     : https://prove2.me/theorems/fc87ab8a-96f1-4b08-983f-b0c1765fb185
-- title:
--   Spectral gaps around a tracked eigenvalue, the adiabatic evolution, QAOA
-- statement:
--   Spectral gaps around a tracked eigenvalue, the adiabatic evolution, QAOA
--
--   ### QAlgorithms.HasGapAround
--
--   The inputs are a finite index type $\iota$ with $N = |\iota|$ elements, a complex $\iota\times\iota$ matrix $A$, and reals $\lambda$ and $\gamma$. The predicate holds iff all three of the following hold:
--
--   1. $A$ is Hermitian.
--   2. Write $\lambda_0 \le \lambda_1 \le \dots \le \lambda_{N-1}$ for the eigenvalues of $A$, listed with multiplicity in increasing order. There is exactly one index $k$ with $\lambda_k = \lambda$. In other words, $\lambda$ is an eigenvalue of multiplicity exactly one.
--   3. For every index $k$ with $\lambda_k \neq \lambda$,
--   $$\gamma \le |\lambda_k - \lambda|.$$
--
--   Edge cases:
--
--   - No sign condition is placed on $\gamma$. If $\gamma \le 0$, condition 3 is automatic.
--   - If $N = 1$, condition 3 is vacuous.
--   - If $N = 0$, condition 2 fails, so the predicate is false.
--
--   ### QAlgorithms.SolvesAdiabaticPlus
--
--   The inputs are:
--
--   - a finite index type $\iota$;
--   - a family $s \mapsto H(s)$ of complex $\iota\times\iota$ matrices, for $s \in \mathbb{R}$, with no Hermiticity assumption;
--   - a real $T$;
--   - a curve $s \mapsto \psi(s)$ in $\mathbb{C}^\iota$.
--
--   The predicate holds iff, for every $s \in [0,1]$, the curve $\psi$ restricted to $[0,1]$ has derivative at $s$ equal to
--
--   $$\psi'(s) = i\, T\, H(s)\,\psi(s).$$
--
--   The derivative is taken within $[0,1]$, so it is one-sided at $s = 0$ and $s = 1$.
--
--   The sign is $+i$. No initial condition, normalization, or behaviour of $\psi$ outside $[0,1]$ is required.
--
--   ### QAlgorithms.qaoaMixer
--
--   For $n \in \mathbb{N}$, this is the $2^n\times 2^n$ complex matrix on $n$-qubit basis strings $z \in \{0,1\}^n$:
--
--   $$B = \sum_{j=0}^{n-1} X_j.$$
--
--   Here $X_j$ is the Pauli matrix $X = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ acting on qubit $j$ and as the identity elsewhere. Concretely, the entry $(X_j)_{y,z}$ equals:
--
--   - $X_{y_j, z_j}$ if $y$ and $z$ agree on every wire other than $j$;
--   - $0$ otherwise.
--
--   So $X_j$ maps $|z\rangle$ to $|z \oplus e_j\rangle$, flipping bit $j$.
--
--   For $n = 0$, $B$ is the zero $1\times 1$ matrix.
--
--   ### QAlgorithms.qaoaUnitary
--
--   The inputs are $n \in \mathbb{N}$, a real function $f$ on $n$-bit strings, a depth $p \in \mathbb{N}$, and real angle vectors $\beta, \theta \in \mathbb{R}^p$. The output is the $2^n\times 2^n$ complex matrix
--
--   $$U = V_{p-1} V_{p-2} \cdots V_1 V_0, \qquad V_k = e^{-i\beta_k B}\, e^{-i\theta_k H_f}.$$
--
--   Here:
--
--   - $e^{(\cdot)}$ is the matrix exponential.
--   - $B = \sum_j X_j$ is the mixer defined above.
--   - $H_f$ is the diagonal matrix with entries $(H_f)_{zz} = f(z)$.
--
--   The factor $V_0$ stands rightmost, so it acts first on a vector. Within each $V_k$, the phase factor $e^{-i\theta_k H_f}$ acts before the mixer factor $e^{-i\beta_k B}$.
--
--   For $p = 0$, $U$ is the identity matrix.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Adiabatic.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_SDP
/-!
# Spectral gaps around a tracked eigenvalue, the adiabatic evolution, QAOA
(shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapter 9. Nannicini's adiabatic evolution is `dψ/ds = +iT H(s) ψ` (Eq. (9.8)); the
frozen `SolvesScaledSchrodinger` (Childs) has the sign `−i` and is not reused (trap Q12).
-/

namespace QAlgorithms

/-- Nannicini p.211, Defs. 9.8–9.9: the Hermitian matrix `A` has a spectral gap at least `γ`
around `lam`: `A` is Hermitian, `lam` is an eigenvalue of multiplicity one (the frozen
`ascEigenvalues` lists eigenvalues with multiplicity), and every other eigenvalue is at distance
at least `γ` from `lam`. Used pointwise in `s` with `γ` the source's `γ = min_s γ(s)` (a lower
bound on each instantaneous gap); with `γ > 0` it excludes the source's gap-`0` case of
multiplicity `> 1`. -/
def HasGapAround {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (lam γ : ℝ) : Prop :=
  A.IsHermitian ∧ (∃! k, ascEigenvalues A k = lam) ∧
    ∀ k, ascEigenvalues A k ≠ lam → γ ≤ |ascEigenvalues A k - lam|

/-- Nannicini p.212, Eq. (9.8): `ψ` solves the rescaled adiabatic evolution
`d|ψ(s)⟩/ds = iT H(s) |ψ(s)⟩` on `s ∈ [0, 1]` (sign `+i`, as in the source; derivative within
`[0, 1]`). The initial condition is a separate hypothesis. -/
def SolvesAdiabaticPlus {ι : Type*} [Fintype ι] (H : ℝ → Matrix ι ι ℂ) (T : ℝ)
    (ψ : ℝ → EuclideanSpace ℂ ι) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1,
    HasDerivWithinAt ψ (Complex.I • (T : ℂ) • act (H s) (ψ s)) (Set.Icc 0 1) s

/-- Nannicini p.229, Eq. (9.40): the initial QAOA Hamiltonian `H_I = Σ_{j=1}^n σ_j^X`, with
`σ_j^X = I ⊗ ⋯ ⊗ X ⊗ ⋯ ⊗ I` (Pauli `X` on wire `j`, the frozen `CliffordOp.mat` of a Pauli
gate). -/
noncomputable def qaoaMixer (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ j : Fin n, Stabilizer.CliffordOp.mat (Stabilizer.CliffordOp.pauli j Stabilizer.Pauli.X)

/-- Nannicini p.230, Eq. (9.42) (with Eq. (9.39), `H_F = Σ_x f(x)|x⟩⟨x|`, the frozen
`problemHamiltonian f`): `U_QAOA(p, β, θ) = e^{−iβ_p H_I} e^{−iθ_p H_F} ⋯ e^{−iβ_1 H_I}
e^{−iθ_1 H_F}`. Layer `k` (the source's `k + 1`) is applied after layers `0, …, k − 1`, and inside
each layer `e^{−iθ H_F}` acts before `e^{−iβ H_I}`. -/
noncomputable def qaoaUnitary {n : ℕ} (f : Qubits n → ℝ) (p : ℕ) (β θ : Fin p → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  orderedProd fun k : Fin p =>
    NormedSpace.exp (-(Complex.I * (β k : ℂ)) • qaoaMixer n) *
      NormedSpace.exp (-(Complex.I * (θ k : ℂ)) • problemHamiltonian f)

/-! ### Sanity tests -/

example {n : ℕ} (f : Qubits n → ℝ) (β θ : Fin 0 → ℝ) : qaoaUnitary f 0 β θ = 1 := by
  simp [qaoaUnitary, orderedProd]

example {ι : Type*} [Fintype ι] (T : ℝ) (ψ : EuclideanSpace ℂ ι) :
    SolvesAdiabaticPlus (fun _ => 0) T (fun _ => ψ) := by
  intro s _
  simpa [act] using hasDerivWithinAt_const s (Set.Icc (0 : ℝ) 1) ψ

example : qaoaMixer 0 = 0 := by
  simp [qaoaMixer]

end QAlgorithms


