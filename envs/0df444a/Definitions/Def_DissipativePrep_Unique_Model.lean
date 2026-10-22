-- Prove2me | Definitions.Def_DissipativePrep_Unique_Model
-- name    : DissipativePrep_Unique_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:25.986837+00:00
-- url     : https://prove2.me/theorems/69623cb1-a751-48f1-9f2d-55d7a5344576
-- title:
--   Eq. (2), §II, §IV, pp. 1–4 — Lindblad generator, dark space, qubit lowering operators, tensor eigenoperators and relaxation time
-- statement:
--   This file fixes the model of Kraus et al. on top of the general GKSL layer (P16): `LindbladData`, the generator `gkslGenerator`, the semigroup $e^{t\mathcal L}$, and the predicates `stationary`, `attractive`, `lazy`.
--
--   1. **The master equation (Eq. (2)).** For a Hermitian $d\times d$ matrix $H$, jump operators $c_1,\dots,c_m$ and rates $g_1,\dots,g_m$, the Liouvillian is
--   $$\mathcal L_{H,c_l}(\rho) = -i[H,\rho] + \sum_l g_l\,\bigl(2c_l\rho c_l^\dagger - c_l^\dagger c_l\rho - \rho c_l^\dagger c_l\bigr).$$
--   It is encoded as the GKSL data `krausData H c g` with drift $H$ and jump operators $\sqrt{2g_l}\,c_l$; in P16's normalization $\sum_k V_k X V_k^\dagger - \tfrac12\{V_k^\dagger V_k, X\} - i[H,X]$ this is exactly the right-hand side above when $g_l \ge 0$.
--   2. **Notation of §II.** $P = \sum_l g_l c_l^\dagger c_l$, $Q = P - iH$, and $\mathcal E(\rho) = 2\sum_l g_l c_l\rho c_l^\dagger$, so that $\mathcal L(\rho) = \mathcal E(\rho) - Q^\dagger\rho - \rho Q$.
--   3. **Dark space.** For a real number $E$, $D_E = K(P)\cap\ker(H - E)$ is the subspace of vectors $\psi$ with $c_l\psi = 0$ for every $l$ and $H\psi = E\psi$. This is the paper's set $D = K(P)\cap ES(H)$ of dark states in the situation of p. 3 where "all the states in $D$ correspond to the same eigenvalue of the Hamiltonian".
--   4. **The construction of §IV.** On $n$ qubits (basis indexed by $\{0,\dots,2^n-1\}$, qubit $1$ the most significant bit), $\sigma_-^{(k)} = \mathbb 1\otimes\dots\otimes|0\rangle_k\langle 1|\otimes\dots\otimes\mathbb 1$ lowers qubit $k$ from $|1\rangle$ to $|0\rangle$. For a unitary $U$, the jump operators are $c_k = U\sigma_-^{(k)}U^\dagger$, the target state is $|\Psi\rangle = U|0^n\rangle$, and `prepData U g H` is the process $\mathcal L_{H,c_k}$ with rates $g_k$.
--   5. **Spectrum and relaxation (§IV.A).** The four one-qubit eigenoperators are $|0\rangle\langle0|$, $\sigma_x$, $\sigma_y$, and $\sigma_z$, with eigenvalues $0$, $-g$, $-g$, and $-2g$. Their tensor products give the explicit $n$-qubit eigenoperators. For a Liouvillian $G$, the relaxation rates are the numbers $-\operatorname{Re}\mu$ over its nonzero eigenvalues $\mu$; a finite positive relaxation time $T$ satisfies $T = 1/r$ where $r>0$ is the least such rate.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** States are vectors of `EuclideanSpace ℂ (Fin d)`, operators are complex $d\times d$ matrices, and $|0^n\rangle$ is the basis vector of index $0$. The factor $\sqrt{2g_l}$ (not $\sqrt{g_l}$) is what makes P16's ½-anticommutator generator agree with Eq. (2); a sorry-free check of this identity was run outside the proposal.
-- source:
--   Kraus et al., Preparation of entangled states by quantum Markov processes, arXiv:0803.1463v3, pp. 1–4, Eq. (2), §II (p. 2), standing assumption of Theorem 2 (p. 3), §IV and §IV.A (p. 4)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

/-- Eq. (2), p. 1: the GKSL data of `L(ρ) = −i[H, ρ] + Σ_l g_l (2 c_l ρ c_l† − c_l†c_l ρ − ρ c_l†c_l)`,
in the normalization of P16's `gkslGenerator` (½-anticommutator): jump operators `√(2 g_l) · c_l`,
drift `H`. -/
def krausData {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) : LindbladData d where
  count := m
  jump := fun l => ((Real.sqrt (2 * g l) : ℝ) : ℂ) • c l
  drift := H
  drift_hermitian := hH

/-- §II, p. 2: `P = Σ_l g_l c_l† c_l`. -/
def Pop {d m : ℕ} (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ l, ((g l : ℝ) : ℂ) • ((c l)ᴴ * c l)

/-- §II, p. 2: `Q = P − iH`. -/
def Qop {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (c : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (g : Fin m → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Pop c g - Complex.I • H

/-- §II, p. 2: the completely positive part `E(ρ) = 2 Σ_l g_l c_l ρ c_l†`. -/
def Eop {d m : ℕ} (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ l, ((2 * g l : ℝ) : ℂ) • (c l * ρ * (c l)ᴴ)

/-- §II, p. 2 and p. 3: the dark space `D = K(P) ∩ ES(H)` for one eigenvalue `E` of `H`
("all the states in D correspond to the same eigenvalue of the Hamiltonian", p. 3):
the vectors annihilated by every jump operator `c_l` that are eigenvectors of `H` with
eigenvalue `E` (together with `0`). -/
def darkSpace {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (c : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (E : ℝ) : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  (⨅ l, LinearMap.ker (Matrix.toEuclideanLin (c l))) ⊓
    LinearMap.ker (Matrix.toEuclideanLin H - (E : ℂ) • LinearMap.id)

/-- §IV, p. 4: `σ_-^{(k)} = 1 ⊗ … ⊗ |0⟩_k⟨1| ⊗ … ⊗ 1` on the bit-string basis
(`false` = `|0⟩`, `true` = `|1⟩`): it sends `|… 1_k …⟩` to `|… 0_k …⟩` and kills `|… 0_k …⟩`. -/
def lowerQ {n : ℕ} (k : Fin n) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => if y k = true ∧ x = Function.update y k false then 1 else 0

/-- `σ_-^{(k)}` transported to the index type `Fin (2 ^ n)` (wire `0` = most significant bit). -/
def lower {n : ℕ} (k : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex (bitsEquivFin n) (bitsEquivFin n) (lowerQ k)

/-- §IV, p. 4: the jump operators `c_k = U d_k U† = U σ_-^{(k)} U†`. -/
def jumpOps {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (k : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  U * lower k * Uᴴ

/-- §IV, p. 4: the target state `|Ψ⟩ = U |0^n⟩`. -/
def target {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : EuclideanSpace ℂ (Fin (2 ^ n)) :=
  act U (ket (0 : Fin (2 ^ n)))

/-- §IV, p. 4: the process `L_{H, c_k}` with `c_k = U σ_-^{(k)} U†` and rates `g_k`. -/
def prepData {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ)
    (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hH : H.IsHermitian) : LindbladData (2 ^ n) :=
  krausData H hH (jumpOps U) g

/-- §IV.A, p. 4: the relaxation rates of a Liouvillian `G`: the numbers `−Re μ` for the
eigenvalues `μ ≠ 0` of `G`. -/
def relaxRates {d : ℕ} (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) : Set ℝ :=
  {r | ∃ μ : ℂ, G.HasEigenvalue μ ∧ μ ≠ 0 ∧ r = -μ.re}

/-- §IV.A, p. 4: `T` is the relaxation time of `G`, "the inverse of the minimum of the negative
real part of [the eigenvalues] different than zero". -/
def IsRelaxTime {d : ℕ} (G : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) (T : ℝ) : Prop :=
  ∃ r, IsLeast (relaxRates G) r ∧ 0 < r ∧ T = 1 / r

/-- §IV.A, p. 4: the four one-qubit eigenoperators in the order
`|0⟩⟨0|`, `σ_x`, `σ_y`, `σ_z`, written in the Boolean qubit basis. -/
def localEigenoperator (i : Fin 4) (x y : Bool) : ℂ :=
  if i = 0 then
    if x = false ∧ y = false then 1 else 0
  else if i = 1 then
    if x ≠ y then 1 else 0
  else if i = 2 then
    if x = false ∧ y = true then -Complex.I
    else if x = true ∧ y = false then Complex.I else 0
  else if x = y then
    if x = false then 1 else -1
  else 0

/-- §IV.A, p. 4: `λ₀ = 0`, `λ₁ = λ₂ = -g`, `λ₃ = -2g`. -/
def localEigenvalue (g : ℝ) (i : Fin 4) : ℂ :=
  if i = 0 then 0 else if i = 3 then ((-2 * g : ℝ) : ℂ) else ((-g : ℝ) : ℂ)

/-- §IV.A, p. 4: the tensor product `σ_{i₁}^{(1)} ⊗ ⋯ ⊗ σ_{iₙ}^{(n)}`
in the bit-string basis, transported to `Fin (2 ^ n)`. -/
def tensorEigenoperator {n : ℕ} (i : Fin n → Fin 4) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex (bitsEquivFin n) (bitsEquivFin n)
    (Matrix.of fun x y => ∏ k, localEigenoperator (i k) (x k) (y k))

end DissipativePrep.Unique


