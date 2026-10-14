-- Prove2me | Definitions.Def_QAlgorithms_Defs_Measurement
-- name    : QAlgorithms_Defs_Measurement
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:41:49.686382+00:00
-- url     : https://prove2.me/theorems/0f8e9c73-80c2-4843-824d-9e39c9c637b1
-- title:
--   Basis states, product states, sequential measurement, mixed states (shared definition layer)
-- statement:
--   Basis states, product states, sequential measurement, mixed states (shared definition layer)
--
--   ### QAlgorithms.IsBasisState
--
--   This defines a property of a vector. Fix an index type $\iota$ with decidable equality; no finiteness is assumed. A vector $\psi$ in the complex Euclidean space $\mathbb{C}^\iota$ is called a *basis state* when it is a unit-modulus scalar multiple of a computational basis vector:
--
--   $$
--   \exists\, k \in \iota,\ \exists\, \alpha \in \mathbb{C}:\quad |\alpha| = 1 \ \text{ and } \ \psi = \alpha\,|k\rangle .
--   $$
--
--   Here $|k\rangle$ is the standard basis vector with coordinate $1$ at index $k$ and $0$ elsewhere.
--
--   Consequences of this definition:
--
--   - The zero vector is never a basis state.
--   - Every basis state has norm $1$.
--   - A global phase $\alpha$ is permitted.
--
--   ### QAlgorithms.prodState
--
--   Given a number of qubits $q \in \mathbb{N}$ and a family $\varphi_0, \dots, \varphi_{q-1}$ of single-qubit vectors, this defines a vector $\Phi$ on $q$ qubits. Each $\varphi_i$ is a vector in $\mathbb{C}^{\{0,1\}}$, with coordinates indexed by $\mathrm{false}=0$ and $\mathrm{true}=1$. The vector $\Phi$ lies in $\mathbb{C}^{\{0,1\}^q}$, and its amplitude at a bit string $z = (z_0, \dots, z_{q-1})$ is
--
--   $$
--   \Phi_z = \prod_{i=0}^{q-1} (\varphi_i)_{z_i},
--   $$
--
--   where $(\varphi_i)_{z_i}$ is the coordinate of $\varphi_i$ at $z_i$. In other words, $\Phi = \varphi_0 \otimes \cdots \otimes \varphi_{q-1}$, with wire $0$ as the first tensor factor.
--
--   Edge cases:
--
--   - No normalization of the $\varphi_i$ is assumed.
--   - For $q = 0$ there is a single (empty) bit string, and its amplitude is the empty product $1$.
--
--   ### QAlgorithms.collapseQubit
--
--   Given a $q$-qubit vector $\psi \in \mathbb{C}^{\{0,1\}^q}$, a wire $k \in \{0,\dots,q-1\}$ and a bit $x \in \{0,1\}$, this defines the post-measurement vector obtained by keeping only the outcome $x$ on wire $k$.
--
--   First define the probability
--
--   $$
--   p = \sum_{j \in \{0,1\}^q,\ j_k = x} |\langle j|\psi\rangle|^2 = \sum_{j:\, j_k = x} |\psi_j|^2 .
--   $$
--
--   The result is the vector with coordinates
--
--   $$
--   \big(\mathrm{collapse}(\psi,k,x)\big)_j = \frac{1}{\sqrt{p}}\cdot\begin{cases}\psi_j & \text{if } j_k = x,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   Points to note:
--
--   - $\psi$ is not assumed to be a unit vector. Because of this, $p$ is the squared norm of the projected vector rather than a normalized probability.
--   - Whenever $p > 0$, the result has norm $1$.
--   - If $p = 0$, the convention $1/\sqrt{0} = 0^{-1} = 0$ applies, so the result is the zero vector.
--
--   ### QAlgorithms.seqMeasProb
--
--   This defines a function $\mathrm{SMP}(\psi, L, y)$ by recursion on a list of wires. Its inputs are:
--
--   - a $q$-qubit vector $\psi \in \mathbb{C}^{\{0,1\}^q}$;
--   - a finite list $L$ of wires in $\{0,\dots,q-1\}$, which may contain repetitions;
--   - a bit string $y \in \{0,1\}^q$.
--
--   The recursion is:
--
--   $$
--   \mathrm{SMP}(\psi, [\,], y) = 1, \qquad
--   \mathrm{SMP}(\psi, k :: L', y) = \Big(\sum_{j:\, j_k = y_k} |\psi_j|^2\Big)\cdot \mathrm{SMP}\big(\mathrm{collapse}(\psi, k, y_k),\, L',\, y\big).
--   $$
--
--   Here $\mathrm{collapse}$ is the post-measurement vector defined in `collapseQubit` above: the coordinates with $j_k = y_k$ are kept, the rest are set to $0$, and the result is divided by the square root of the kept weight, with division by $0$ giving the zero vector. Thus $\mathrm{SMP}$ is the product of the successive outcome weights obtained by measuring the listed wires in order, each time requiring outcome $y_k$ on wire $k$.
--
--   What the definition implies:
--
--   - Only the bits of $y$ at wires appearing in $L$ are used.
--   - $\psi$ is not assumed normalized.
--   - If some weight along the way is $0$, the subsequent vector is $0$, and the product is $0$.
--
--   ### QAlgorithms.tvDist
--
--   For a finite index set $\iota$ and two arbitrary real-valued functions $P, Q : \iota \to \mathbb{R}$, this defines
--
--   $$
--   \mathrm{tv}(P,Q) = \frac{1}{2}\sum_{j \in \iota} |P_j - Q_j| .
--   $$
--
--   $P$ and $Q$ are not required to be nonnegative or to sum to $1$. For empty $\iota$ the value is $0$.
--
--   ### QAlgorithms.traceRight
--
--   Let $\alpha, \beta$ be index types with $\beta$ finite; $\alpha$ need not be finite. Given a complex matrix $M$ indexed by pairs in $\alpha \times \beta$, this defines the $\alpha \times \alpha$ matrix with entries
--
--   $$
--   (\mathrm{Tr}_R M)_{j,k} = \sum_{h \in \beta} M_{(j,h),(k,h)} .
--   $$
--
--   This is the partial trace over the second (right) tensor factor. For empty $\beta$ it is the zero matrix.
--
--   ### QAlgorithms.ensembleDensity
--
--   Given an index type $\iota$, a number $m \in \mathbb{N}$, real weights $p_0,\dots,p_{m-1}$ and vectors $\psi_0,\dots,\psi_{m-1} \in \mathbb{C}^\iota$, this defines the $\iota \times \iota$ matrix
--
--   $$
--   \rho = \sum_{j=0}^{m-1} p_j\, |\psi_j\rangle\langle\psi_j|, \qquad \text{i.e. } \rho_{a,b} = \sum_{j} p_j\, (\psi_j)_a\, \overline{(\psi_j)_b} .
--   $$
--
--   No conditions are imposed on the inputs:
--
--   - The weights may be negative.
--   - The weights need not sum to $1$.
--   - The vectors need not be normalized.
--   - For $m = 0$, $\rho$ is the zero matrix.
--
--   ### QAlgorithms.qubitsAppendEquiv
--
--   For $a, b \in \mathbb{N}$, this is an explicit bijection between $(a+b)$-bit strings and pairs consisting of an $a$-bit string and a $b$-bit string:
--
--   $$
--   \{0,1\}^{a+b} \longrightarrow \{0,1\}^a \times \{0,1\}^b .
--   $$
--
--   - **Forward map:** a string $z$ is sent to $\big((z_0,\dots,z_{a-1}),\ (z_a,\dots,z_{a+b-1})\big)$. So wire $i < a$ goes to position $i$ of the first part, and wire $a + j$ goes to position $j$ of the second part.
--   - **Inverse map:** a pair $(u, v)$ is sent to the concatenation $u\,v$.
--
--   The definition includes proofs that these two maps are mutually inverse.
--
--   ### QAlgorithms.withZeroAncillas
--
--   Given $q, w \in \mathbb{N}$ and a complex matrix $\rho$ indexed by $q$-bit strings, this defines a matrix $\tilde\rho$ indexed by $(q+w)$-bit strings.
--
--   Write each $(q+w)$-bit string as $y = (y', y'')$ via the split of `qubitsAppendEquiv`. Here $y'$ is the first $q$ bits and $y''$ is the last $w$ bits. The entries are
--
--   $$
--   \tilde\rho_{y,z} = \begin{cases} \rho_{y',z'} & \text{if } y'' = 0^w \text{ and } z'' = 0^w,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   That is, $\tilde\rho = \rho \otimes |0^w\rangle\langle 0^w|$, with the $w$ ancilla wires appended after the $q$ original wires. No property of $\rho$, such as being a density matrix, is assumed. For $w = 0$, $\tilde\rho$ coincides with $\rho$ under the identification of $(q+0)$-bit strings with $q$-bit strings.
--
--   ### QAlgorithms.densityProb
--
--   For any index type $\iota$, any complex $\iota \times \iota$ matrix $\sigma$ and any index $z \in \iota$, this is the real part of the diagonal entry:
--
--   $$
--   \mathrm{dp}(\sigma, z) = \operatorname{Re} \sigma_{z,z} .
--   $$
--
--   No positivity or trace condition on $\sigma$ is assumed. Consequently, this number need not lie in $[0,1]$.
--
--   ### QAlgorithms.densityMean
--
--   For a finite index set $\iota$, a complex $\iota \times \iota$ matrix $\sigma$ and a real function $Y : \iota \to \mathbb{R}$, this defines
--
--   $$
--   \mathrm{mean}(\sigma, Y) = \sum_{z \in \iota} \operatorname{Re}(\sigma_{z,z})\, Y(z) .
--   $$
--
--   No condition on $\sigma$ is assumed; in particular the weights $\operatorname{Re}\sigma_{z,z}$ need not be nonnegative or sum to $1$.
--
--   ### QAlgorithms.densityVariance
--
--   For a finite index set $\iota$, a complex $\iota \times \iota$ matrix $\sigma$ and a real function $Y : \iota \to \mathbb{R}$, let $\mu = \sum_{z} \operatorname{Re}(\sigma_{z,z})\, Y(z)$, as in `densityMean`. This defines
--
--   $$
--   \mathrm{var}(\sigma, Y) = \sum_{z \in \iota} \operatorname{Re}(\sigma_{z,z})\,\big(Y(z) - \mu\big)^2 .
--   $$
--
--   No condition on $\sigma$ is assumed. If the diagonal real parts are not a probability vector, this expression need not equal a variance and may be negative.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Measurement.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Stabilizer
/-!
# Basis states, product states, sequential measurement, mixed states (shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapter 1.

Conventions are the frozen ones of `QAlgorithms.Defs.Basic`: an `n`-qubit register is indexed by
`Qubits n = Fin n → Bool`, wire `i` is the source's qubit `i + 1`, and the first qubit is the most
significant bit (Nannicini p.14: "the first qubit corresponds to the most significant bit").
Two-register objects put register `A` first.
-/

namespace QAlgorithms

open scoped ComplexConjugate

/-- Nannicini p.13, Def. 1.16: a state `ψ` is a *basis state* if `ψ = α_k |k⟩` for some basis
index `k` and some `α_k ∈ ℂ` with `|α_k|² = 1`; otherwise it is a superposition. Generic in the
index type, so that it applies to a `q`-qubit register (`Qubits q`) and to a single qubit
(`Bool`). A basis state is automatically a unit vector. -/
def IsBasisState {ι : Type*} [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) : Prop :=
  ∃ (k : ι) (α : ℂ), ‖α‖ = 1 ∧ ψ = α • ket k

/-- Nannicini pp.14–15, §1.2.1: the tensor product `|φ_1⟩ ⊗ ⋯ ⊗ |φ_q⟩` of `q` single-qubit
vectors, with amplitude `∏_k φ_k(j_k)` on the basis string `j`; wire `i` carries the source's
qubit `i + 1` (the first qubit is the most significant one, as for `bitsToNat`). -/
noncomputable def prodState {q : ℕ} (φ : Fin q → EuclideanSpace ℂ Bool) :
    EuclideanSpace ℂ (Qubits q) :=
  WithLp.toLp 2 fun z => ∏ i, φ i (z i)

/-- Nannicini p.19, Postulate 3: the state after a measurement gate on wire `k` of the
`q`-qubit state `ψ = Σ_j α_j |j⟩` returns `x`, namely
`Σ_{j : j_k = x} α_j / √(Σ_{ℓ : ℓ_k = x} |α_ℓ|²) |j⟩`. The outcome probability
`Σ_{j : j_k = x} |α_j|²` is the frozen `probEvent ψ (fun j => j k = x)`.
Junk value: when that probability is `0` the inverse square root is `0` and the result is the zero
vector; such an outcome has probability `0`, so every product that uses it carries weight `0`. -/
noncomputable def collapseQubit {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (k : Fin q) (x : Bool) :
    EuclideanSpace ℂ (Qubits q) :=
  ((Real.sqrt (probEvent ψ fun j => j k = x))⁻¹ : ℂ) •
    WithLp.toLp 2 fun j => if j k = x then ψ j else 0

/-- Nannicini pp.19–20, Postulate 3 and Prop. 1.27: the probability that measuring the wires of the
list `l` one at a time, in list order (head first), each measurement followed by the Postulate 3
collapse, returns the bit `y k` on every measured wire `k`. Values of `y` off `l` are ignored.
`seqMeasProb ψ [] y = 1` and
`seqMeasProb ψ (k :: l) y = Pr_ψ(Q_k = y_k) · seqMeasProb (collapse of ψ) l y`. -/
noncomputable def seqMeasProb {q : ℕ} : EuclideanSpace ℂ (Qubits q) → List (Fin q) → Qubits q → ℝ
  | _, [], _ => 1
  | ψ, k :: l, y => probEvent ψ (fun j => j k = y k) * seqMeasProb (collapseQubit ψ k (y k)) l y

/-- Nannicini p.31, Def. 1.47: the total variation distance `d_TV(P, Q) = ½ Σ_j |p_j − q_j|` of two
discrete distributions on the same finite sample space, given by their probability vectors. -/
noncomputable def tvDist {ι : Type*} [Fintype ι] (P Q : ι → ℝ) : ℝ :=
  2⁻¹ * ∑ j, |P j - Q j|

/-- Nannicini pp.37–38, Defs. 1.62 and 1.64: the partial trace `Tr_B` over the **second**
register `B` of a two-register operator, `(Tr_B M)_{jk} = Σ_h M_{(j,h),(k,h)}` (the linear
extension of `Tr_B(|j⟩⟨k| ⊗ |h⟩⟨ℓ|) = |j⟩⟨k| ⟨ℓ|h⟩`). The reduced density matrix of register `A`
is `ρ^(A) = traceRight ρ^(AB)`. (The frozen `traceLeft` traces out the first register.) -/
def traceRight {α β : Type*} [Fintype β] (M : Matrix (α × β) (α × β) ℂ) : Matrix α α ℂ :=
  Matrix.of fun j k => ∑ h, M (j, h) (k, h)

/-- Nannicini p.35, Def. 1.55: the density matrix `ρ = Σ_{j=1}^m p_j |ψ_j⟩⟨ψ_j|` of the ensemble
`{p_j, |ψ_j⟩}` (0-based here). The ensemble conditions (`p_j ≥ 0`, `Σ p_j = 1`, each `ψ_j` a unit
vector) are hypotheses of the statements that use it. -/
noncomputable def ensembleDensity {ι : Type*} {m : ℕ} (p : Fin m → ℝ)
    (ψ : Fin m → EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  ∑ j, (p j : ℂ) • pureDensity (ψ j)

/-- Nannicini p.14 (§1.2.1) and p.172 (Lem. 7.39): a register of `a + b` qubits viewed as two
registers, the first `a` wires forming the first register:
`z ↦ (z_1 … z_a, z_{a+1} … z_{a+b})`, inverse `Fin.append` (as in the frozen `inputState`). -/
def qubitsAppendEquiv (a b : ℕ) : Qubits (a + b) ≃ Qubits a × Qubits b where
  toFun z := (fun i => z (Fin.castAdd b i), fun j => z (Fin.natAdd a j))
  invFun p := Fin.append p.1 p.2
  left_inv z := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  right_inv p := by
    rcases p with ⟨u, v⟩
    simp

/-- Nannicini p.35 (§1.4) and p.174 (Rem. 7.42): the density matrix `ρ ⊗ |0^w⟩⟨0^w|` on `q + w`
qubits, one copy of the `q`-qubit state `ρ` on the first `q` wires and `w` ancillas in `|0⟩` on
the last `w` wires. -/
def withZeroAncillas {q : ℕ} (ρ : Matrix (Qubits q) (Qubits q) ℂ) (w : ℕ) :
    Matrix (Qubits (q + w)) (Qubits (q + w)) ℂ :=
  Matrix.of fun y z =>
    if (qubitsAppendEquiv q w y).2 = (fun _ => false) ∧ (qubitsAppendEquiv q w z).2 = (fun _ => false)
    then ρ (qubitsAppendEquiv q w y).1 (qubitsAppendEquiv q w z).1 else 0

/-- Nannicini p.35, Rem. 1.59: the probability `⟨z|σ|z⟩` of the outcome `z` when every qubit of a
register in the mixed state `σ` is measured (the real part of the diagonal entry, which is real for
a density matrix). A circuit `W` maps `ρ` to `W ρ W†` (§1.4). -/
noncomputable def densityProb {ι : Type*} (σ : Matrix ι ι ℂ) (z : ι) : ℝ :=
  (σ z z).re

/-- Nannicini p.173 (Prop. 7.41) and p.174 (Rem. 7.42): the expected value `Σ_z ⟨z|σ|z⟩ Y(z)` of
the classical output `Y(z)` computed from a final measurement of a register in the state `σ`. -/
noncomputable def densityMean {ι : Type*} [Fintype ι] (σ : Matrix ι ι ℂ) (Y : ι → ℝ) : ℝ :=
  ∑ z, densityProb σ z * Y z

/-- Nannicini p.173, Prop. 7.41: the variance `Σ_z ⟨z|σ|z⟩ (Y(z) − E[Y])²` of that output; the
source's standard deviation is its square root. -/
noncomputable def densityVariance {ι : Type*} [Fintype ι] (σ : Matrix ι ι ℂ) (Y : ι → ℝ) : ℝ :=
  ∑ z, densityProb σ z * (Y z - densityMean σ Y) ^ 2

/-! ### Sanity tests -/

example {ι : Type*} [DecidableEq ι] (i : ι) : IsBasisState (ket i) :=
  ⟨i, 1, by simp, by simp⟩

example (q : ℕ) : prodState (fun _ : Fin q => ket false) = zeroKet q := by
  ext z
  simp only [prodState, zeroKet, ket]
  by_cases h : z = fun _ => false
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ false := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    rw [EuclideanSpace.single_apply, if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [EuclideanSpace.single_apply, hi])

example {q : ℕ} (ψ : EuclideanSpace ℂ (Qubits q)) (k : Fin q) (y : Qubits q) :
    seqMeasProb ψ [k] y = probEvent ψ (fun j => j k = y k) := by
  simp [seqMeasProb]

example {ι : Type*} [Fintype ι] (P : ι → ℝ) : tvDist P P = 0 := by
  simp [tvDist]

example {α β : Type*} [Fintype β] (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    traceRight (Matrix.kronecker A B) = B.trace • A := by
  ext j k
  simp [traceRight, Matrix.kronecker, Matrix.trace, Finset.mul_sum, mul_comm]

example {ι : Type*} (ψ : EuclideanSpace ℂ ι) :
    ensembleDensity (fun _ : Fin 1 => (1 : ℝ)) (fun _ => ψ) = pureDensity ψ := by
  simp [ensembleDensity]

example {q w : ℕ} (ρ : Matrix (Qubits q) (Qubits q) ℂ) (y z : Qubits q) :
    withZeroAncillas ρ w (Fin.append y fun _ => false) (Fin.append z fun _ => false) = ρ y z := by
  simp [withZeroAncillas, qubitsAppendEquiv]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (z : ι) :
    densityProb (pureDensity ψ) z = prob ψ z := by
  simp [densityProb, pureDensity, prob, ket, EuclideanSpace.inner_single_left, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

example {ι : Type*} [Fintype ι] (σ : Matrix ι ι ℂ) : densityMean σ (fun _ => 0) = 0 := by
  simp [densityMean]

end QAlgorithms


