-- Prove2me | Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
-- name    : QuantumOnePCA369_PauliPCA_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:39.87166+00:00
-- url     : https://prove2.me/theorems/b32ce510-5635-4f7f-9d25-76c70de1b0c9
-- title:
--   Qubit strings, Pauli matrices $\sigma_{x,z}$, Pauli basis measurements and spectral predicates
-- statement:
--   This file fixes the objects of §2 of the paper.
--
--   **Qubits and bit strings.** The computational basis of $n$ qubits is indexed by $x\in\mathbb F_2^n$; qubit $0$ is the first qubit. For a prefix length $\ell$ and suffix length $m$ with $\ell+m=n$, a string is written $sy$ with $s\in\mathbb F_2^\ell$ on the first $\ell$ qubits and $y\in\mathbb F_2^m$ on the last $m$. The unnormalized block of a matrix $\rho$ at prefix $s$ is $(\langle s|\otimes I)\rho(|s\rangle\otimes I)$, and the prefix mass is $\operatorname{tr}((|s\rangle\langle s|\otimes I)\rho)$, the probability of observing $s$ when the first $\ell$ qubits are measured in the computational basis. For $\ell=0$ the only prefix is the empty string.
--
--   **Pauli matrices.** With $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$, $Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$ as printed on p. 6,
--   $$\sigma_{x,z}:=i^{x\cdot z}\bigotimes_{j=1}^n X^{x_j}Z^{z_j},\qquad x,z\in\mathbb F_2^n,$$
--   where $x\cdot z$ is the integer dot product of the 0/1 vectors, read mod 4. The quadratic phase $q_A(x)=\sum_{i,j}x_iA_{ij}x_j \bmod 4$ of a matrix $A$ over $\mathbb F_2$ lifts every entry of $A$ and $x$ to $\{0,1\}\subset\mathbb Z$ before multiplying. $\mathrm{Sym}_m(\mathbb F_2)$ is the set of symmetric $m\times m$ matrices over $\mathbb F_2$.
--
--   **Pauli basis measurements.** A setting assigns $X$, $Y$ or $Z$ to every qubit. Measuring one copy of $\rho$ in setting $\theta$ yields $y\in\mathbb F_2^n$ with Born probability
--   $$\Pr_\rho[y\mid\theta]=\operatorname{tr}\Big(\rho\bigotimes_{j=1}^n\frac{I+(-1)^{y_j}\sigma_{\theta_j}}{2}\Big).$$
--   An $n$-qubit state is a positive semidefinite $2^n\times2^n$ complex matrix of trace one.
--
--   **Linear algebra.** $\langle a|b\rangle=\sum_i\overline{a_i}b_i$; $\|v\|_2^2=\sum_i|v_i|^2$; $\|A\|_\infty$ is the Schatten-$\infty$ (spectral) norm; $\Pi$ is an orthogonal projection if $\Pi^2=\Pi=\Pi^\dagger$; $U$ is an isometry (partial unitary) if $U^\dagger U=I$. A top eigenvector of $A$ is a unit vector $v$ with $Av=\mu v$ for a real $\mu$ that is at least every eigenvalue of $A$. A projection $\Pi$ onto a top-$k$ eigenspace of a Hermitian $A$ is an orthogonal projection of rank $k$ commuting with $A$ such that $\langle u|A|u\rangle\ge\langle w|A|w\rangle$ for all unit $u\in\operatorname{range}\Pi$ and unit $w\in\ker\Pi$ (ties broken arbitrarily). The sorted eigenvalues of a Hermitian matrix are $\lambda_1\ge\lambda_2\ge\dots$, counted with multiplicity.
--
--   **The spectral primitive.** A *spectral chooser* is an exact eigensolver: for every $d$ and every $d\times d$ matrix it returns eigenvalues and a matrix of eigenvector columns, and on Hermitian inputs the columns form an orthonormal eigenbasis sorted by non-increasing eigenvalue. Degenerate eigenspaces may be split arbitrarily (p. 15), so every guarantee of the mission is stated for every chooser.
--
--   **Formalization Note** Bit strings are functions $\mathrm{Fin}\,n\to\mathbb Z/2$. Prefix, suffix, one-bit extension and first-bit operations are total functions (with a default bit outside the intended range); they are used only with $\ell+m=n$ and one-bit extensions of the right length. Fidelities and inner products are written out as sums.
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, pp. 5–6, §2 (Preliminaries: Schatten norms, F_2, Pauli matrices, single-qubit Pauli eigenstate projections, eq. (1)); p. 15 (arbitrary eigenvectors of degenerate matrices)

import Mathlib

namespace QuantumOnePCA369.PauliPCA

open scoped Matrix.Norms.L2Operator ComplexOrder

/-! Hansen–Li, *Quantum 1-PCA with Pauli Measurements in Nearly Linear Time*, STOC 2027 #369,
§2 (p. 5–6): bit strings, Pauli matrices, single-qubit Pauli basis measurements, and the linear
algebra used throughout. -/

/-- Bit strings `x ∈ 𝔽₂ⁿ`; the computational basis of `n` qubits is indexed by `Bits n`
(qubit `0` is the first qubit). -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- Integer dot product of two 0/1 vectors, read mod 4 (p. 6: "the dot product `x · z` is
taken in `ℂⁿ` (or mod 4)"): each bit is lifted to `{0,1} ⊂ ℤ` before multiplying. -/
def dot4 {n : ℕ} (x z : Bits n) : ZMod 4 := ∑ j, ((x j).val * (z j).val : ZMod 4)

/-- Dot product over `𝔽₂`. -/
def dot2 {n : ℕ} (x y : Bits n) : ZMod 2 := ∑ j, x j * y j

/-- The quadratic form `x · A x` with the **whole matrix lifted** to `ℤ` before multiplying,
read mod 4: `q_A(x) = ∑_{i,j} x_i A_{ij} x_j mod 4`. -/
def quad4 {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Bits n) : ZMod 4 :=
  ∑ i, ∑ j, ((x i).val * (A i j).val * (x j).val : ZMod 4)

/-- `i^e` for `e ∈ ℤ/4`. -/
noncomputable def iPow (e : ZMod 4) : ℂ := Complex.I ^ e.val

/-- `(-1)^b` for a bit `b`. -/
def sgn (b : ZMod 2) : ℂ := (-1) ^ b.val

/-- The single-qubit Pauli `X`, indexed by `𝔽₂`. -/
def pauliX : Matrix (ZMod 2) (ZMod 2) ℂ := fun a b => if a = b + 1 then 1 else 0

/-- The single-qubit Pauli `Z`, indexed by `𝔽₂`. -/
def pauliZ : Matrix (ZMod 2) (ZMod 2) ℂ := fun a b => if a = b then sgn a else 0

/-- The single-qubit Pauli `Y` exactly as printed on p. 6: `Y = [[0, -i], [i, 0]]`. -/
def pauliY : Matrix (ZMod 2) (ZMod 2) ℂ :=
  fun a b => if a = b then 0 else if a = 0 then -Complex.I else Complex.I

/-- `X^{a} Z^{b}` for bits `a, b`. -/
def pauliXZ (a b : ZMod 2) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  (if a = 1 then pauliX else 1) * (if b = 1 then pauliZ else 1)

/-- Tensor product `⊗_{j} M_j` of single-qubit matrices, as a matrix on `ℂ^{2^n}`
(entry `(a, b)` is `∏_j (M_j)_{a_j b_j}`). -/
def tensorQ {n : ℕ} (M : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) : Matrix (Bits n) (Bits n) ℂ :=
  fun a b => ∏ j, M j (a j) (b j)

/-- The Pauli matrix `σ_{x,z} := i^{x·z} ⊗_{j} X^{x_j} Z^{z_j}` (p. 6), with `x · z` the integer
dot product read mod 4. -/
noncomputable def pauli {n : ℕ} (x z : Bits n) : Matrix (Bits n) (Bits n) ℂ :=
  iPow (dot4 x z) • tensorQ (fun j => pauliXZ (x j) (z j))

/-- A single-qubit Pauli measurement basis. -/
inductive PauliBasis
  | X
  | Y
  | Z
  deriving DecidableEq

instance : Fintype PauliBasis where
  elems := {PauliBasis.X, PauliBasis.Y, PauliBasis.Z}
  complete := by intro b; cases b <;> simp

/-- The observable of a single-qubit Pauli basis. -/
def PauliBasis.obs : PauliBasis → Matrix (ZMod 2) (ZMod 2) ℂ
  | .X => pauliX
  | .Y => pauliY
  | .Z => pauliZ

/-- The rank-one spectral projection `(I + (-1)^y σ)/2` of a single-qubit Pauli basis. -/
noncomputable def PauliBasis.proj (b : PauliBasis) (y : ZMod 2) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  (1 / 2 : ℂ) • (1 + sgn y • b.obs)

/-- A setting of a Pauli basis measurement on `n` qubits: one basis per qubit. -/
abbrev PauliSetting (n : ℕ) := Fin n → PauliBasis

/-- Born probability of outcome `y ∈ 𝔽₂ⁿ` when one copy of `ρ` is measured in the product Pauli
basis `θ` (p. 6): `tr(ρ ⊗_j (I + (-1)^{y_j} σ_j)/2)`. -/
noncomputable def bornProb {n : ℕ} (ρ : Matrix (Bits n) (Bits n) ℂ) (θ : PauliSetting n)
    (y : Bits n) : ℝ :=
  (Matrix.trace (ρ * tensorQ (fun j => (θ j).proj (y j)))).re

/-- An `n`-qubit quantum state (density matrix): positive semidefinite with unit trace. -/
def IsDensity {n : ℕ} (ρ : Matrix (Bits n) (Bits n) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-! ### Prefix/suffix bookkeeping (qubits `0, …, ℓ-1` carry the prefix) -/

/-- The first `ℓ` bits of `x ∈ 𝔽₂ⁿ` (meaningful for `ℓ ≤ n`). -/
def prefixBits {n : ℕ} (ℓ : ℕ) (x : Bits n) : Bits ℓ :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else 0

/-- The last `m` bits of `x ∈ 𝔽₂ⁿ` after a prefix of length `ℓ` (meaningful for `ℓ + m = n`). -/
def suffixBits {n : ℕ} (ℓ m : ℕ) (x : Bits n) : Bits m :=
  fun i => if h : ℓ + i.val < n then x ⟨ℓ + i.val, h⟩ else 0

/-- The string `s y ∈ 𝔽₂ⁿ` with prefix `s ∈ 𝔽₂^ℓ` and suffix `y ∈ 𝔽₂^m` (meaningful for
`ℓ + m = n`). -/
def joinBits {ℓ m : ℕ} (n : ℕ) (s : Bits ℓ) (y : Bits m) : Bits n :=
  fun i => if h : i.val < ℓ then s ⟨i.val, h⟩
    else if h' : i.val - ℓ < m then y ⟨i.val - ℓ, h'⟩ else 0

/-- The one-bit extension `s b` of a prefix `s ∈ 𝔽₂^L` (meaningful for `L' = L + 1`). -/
def childBits {L : ℕ} (L' : ℕ) (s : Bits L) (b : ZMod 2) : Bits L' :=
  fun i => if h : i.val < L then s ⟨i.val, h⟩ else b

/-- First bit of a string (meaningful for a nonempty string). -/
def headBit {J : ℕ} (y : Bits J) : ZMod 2 := if h : 0 < J then y ⟨0, h⟩ else 0

/-- The string with its first bit removed (meaningful for `J = J' + 1`). -/
def tailBits {J : ℕ} (J' : ℕ) (y : Bits J) : Bits J' :=
  fun i => if h : i.val + 1 < J then y ⟨i.val + 1, h⟩ else 0

/-- The unnormalized block `(⟨s| ⊗ I) ρ (|s⟩ ⊗ I)` of `ρ` at prefix `s ∈ 𝔽₂^ℓ`, a matrix on the
remaining `m` qubits (`ℓ + m = n`). -/
def prefixBlock {n : ℕ} (ℓ m : ℕ) (ρ : Matrix (Bits n) (Bits n) ℂ) (s : Bits ℓ) :
    Matrix (Bits m) (Bits m) ℂ :=
  fun y y' => ρ (joinBits n s y) (joinBits n s y')

/-- The prefix mass `tr((|s⟩⟨s| ⊗ I) ρ)`, the probability of observing prefix `s` when the
first `ℓ` qubits are measured in the computational basis. -/
noncomputable def prefixMass {n : ℕ} (ℓ m : ℕ) (ρ : Matrix (Bits n) (Bits n) ℂ) (s : Bits ℓ) :
    ℝ :=
  (Matrix.trace (prefixBlock ℓ m ρ s)).re

/-! ### Linear algebra -/

/-- Inner product `⟨a|b⟩ = ∑_i conj(a_i) b_i`. -/
def braket {ι : Type*} [Fintype ι] (a b : ι → ℂ) : ℂ := ∑ i, star (a i) * b i

/-- Squared Euclidean norm `‖v‖₂² = ∑_i |v_i|²`. -/
noncomputable def normSq2 {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- Schatten-∞ (spectral, ℓ²-operator) norm `‖A‖_∞`. -/
noncomputable def opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ := ‖A‖

/-- `A` is an orthogonal projection: `A² = A = A†`. -/
def IsOrthProj {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ) : Prop :=
  P * P = P ∧ P.conjTranspose = P

/-- The columns of `U` are orthonormal (`U` is an isometry / partial unitary): `U† U = I`. -/
def IsIsometry {ι κ : Type*} [Fintype ι] [DecidableEq κ] (U : Matrix ι κ ℂ) : Prop :=
  U.conjTranspose * U = 1

/-- `v` is a top (unit) eigenvector of `A`: `‖v‖ = 1`, `A v = μ v` for a real `μ`, and every
eigenvalue of `A` has real part at most `μ`. -/
def IsTopEigvec {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v : ι → ℂ) : Prop :=
  normSq2 v = 1 ∧ ∃ μ : ℝ, A.mulVec v = (μ : ℂ) • v ∧
    ∀ (w : ι → ℂ) (μ' : ℂ), w ≠ 0 → A.mulVec w = μ' • w → μ'.re ≤ μ

/-- `P` is the orthogonal projection onto a top-`k` eigenspace of the Hermitian matrix `A`
(ties broken arbitrarily): `P` is an orthogonal projection of rank `k` commuting with `A`, and
the Rayleigh quotient of `A` on any unit vector of `range P` is at least that on any unit vector
of `ker P`. -/
def IsTopKProj {ι : Type*} [Fintype ι] [DecidableEq ι] (A P : Matrix ι ι ℂ) (k : ℕ) : Prop :=
  IsOrthProj P ∧ P.rank = k ∧ P * A = A * P ∧
    ∀ u w : ι → ℂ, P.mulVec u = u → P.mulVec w = 0 → normSq2 u = 1 → normSq2 w = 1 →
      (braket w (A.mulVec w)).re ≤ (braket u (A.mulVec u)).re

/-- The `i`-th largest eigenvalue (0-based, counted with multiplicity) of a Hermitian matrix,
`0` for an index beyond the dimension. -/
noncomputable def sortedEig {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (i : ℕ) : ℝ :=
  if h : i < Fintype.card ι then hA.eigenvalues₀ ⟨i, h⟩ else 0

/-! ### The spectral primitive (§2, p. 5: spectral computations in the real RAM model) -/

/-- An exact eigensolver: to each square matrix it assigns eigenvalues and a matrix of
eigenvectors; for a Hermitian input the columns are an orthonormal eigenbasis, sorted by
eigenvalue in non-increasing order. Degenerate eigenspaces (and the zero matrix) may be split
arbitrarily (p. 15), which is why every guarantee is stated for **every** chooser. -/
structure SpectralChooser where
  /-- eigenvalues and eigenvector columns -/
  eig : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ → (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℂ
  /-- the specification on Hermitian inputs -/
  spec : ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ), A.IsHermitian →
    IsIsometry (eig d A).2 ∧
    A * (eig d A).2 = (eig d A).2 * Matrix.diagonal (fun i => ((eig d A).1 i : ℂ)) ∧
    Antitone (eig d A).1

/-- Symmetric `m × m` matrices over `𝔽₂`, `Sym_m(𝔽₂)`. -/
abbrev SymF2 (m : ℕ) := {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.IsSymm}

end QuantumOnePCA369.PauliPCA


