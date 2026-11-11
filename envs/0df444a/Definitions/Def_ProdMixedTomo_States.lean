-- Prove2me | Definitions.Def_ProdMixedTomo_States
-- name    : ProdMixedTomo_States
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:02.885605+00:00
-- url     : https://prove2.me/theorems/04a8663f-21ff-40a2-8a99-ad7bef6259c8
-- title:
--   Qubits, density matrices, product mixed states $\mathcal M_n$, Pauli matrices and the projectors $P(b)$
-- statement:
--   The computational basis of $n$ qubits is indexed by $\{0,1\}^n$. An $n$-qubit **density matrix** is a positive semidefinite $\rho\in\mathbb C^{2^n\times 2^n}$ with $\operatorname{tr}\rho=1$. For one-qubit matrices $\pi_1,\dots,\pi_n\in\mathbb C^{2\times2}$ the tensor product is
--   $$
--   (\pi_1\otimes\cdots\otimes\pi_n)(x,y)=\prod_{j=1}^n \pi_j(x_j,y_j),\qquad x,y\in\{0,1\}^n,
--   $$
--   and the **product mixed states** are
--   $$
--   \mathcal M_n=\{\pi_1\otimes\cdots\otimes\pi_n:\ \pi_i\in\mathbb C^{2\times 2},\ \pi_i\succeq0,\ \operatorname{tr}\pi_i=1\}.
--   $$
--   ($\mathcal M_n$ is the published `GeoQAC.IsProductState` on the qubit set $\{1,\dots,n\}$.) The Pauli matrices (the published `CompNonlocal.pauli`) are $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$, $Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$, and for $c\in\mathbb R^3$, $c\cdot\sigma=c_0X+c_1Y+c_2Z$; every one-qubit state is $\tfrac12(I+c\cdot\sigma)$ with $\|c\|_2\le1$. For a direction $b\in\mathbb R^3\setminus\{0\}$, the projector onto the $+b$ eigenvector is
--   $$
--   P(b)=\tfrac12\Bigl(I+\tfrac{b}{\|b\|_2}\cdot\sigma\Bigr),
--   $$
--   and $P(0):=P(e_Z)=|0\rangle\langle0|$. The pair $\{P(b),I-P(b)\}$ is the projective single-qubit measurement along $b$; for $b=e_X$ it is $\{(I+X)/2,(I-X)/2\}$ of Algorithm 1.
--
--   These are the state-side objects of the whole mission.
--
--   **Formalization Note** The basis is `Fin n → Bool` (`false` = 0); the tensor product is the entrywise product above (the Kronecker product in this indexing). $P(0)$ is a convention that only makes the machine's measurement and the output decoder total.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Problem 1, p.13 (PDF p.15); proof of Theorem 3.1, pp.17–18 (PDF pp.19–20)

import Mathlib
import Definitions.Def_CompNonlocal_pauli
import Definitions.Def_GeoQAC_IsProductState

open scoped ComplexOrder

namespace ProdMixedTomo

/-!
# Qubits, density matrices, product mixed states, Pauli matrices and Bloch projectors

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Problem 1, p.13 (PDF p.15)
(`M_n = {π₁ ⊗ ⋯ ⊗ πₙ : πᵢ ∈ ℂ^{2×2}, πᵢ ⪰ 0, tr πᵢ = 1}`), and proof of Theorem 3.1, pp.17–18
(PDF pp.19–20) (`π_j = ½(I + c_j·σ_j)`, the POVMs `{(I ± P)/2}`).

**Formalization Note.**
* The computational basis of `n` qubits is indexed by `Fin n → Bool` (`false` ↔ `|0⟩`,
  `true` ↔ `|1⟩`); a one-qubit matrix is a `Matrix Bool Bool ℂ`.
* `M_n` is the published `GeoQAC.IsProductState` (b7e328d1) on `V = Fin n`.
* The tensor product `π₁ ⊗ ⋯ ⊗ πₙ` is the entrywise product
  `(⨂ π)(x, y) = ∏ⱼ πⱼ(xⱼ, yⱼ)`, which is the Kronecker product in this indexing.
* The Pauli matrices `X = [[0,1],[1,0]]`, `Y = [[0,−i],[i,0]]`, `Z = [[1,0],[0,−1]]` are the
  published `CompNonlocal.pauli 0, 1, 2` (same `Bool` indexing, `false` ↔ `|0⟩`); for `b ∈ ℝ³`,
  `b·σ = b₀X + b₁Y + b₂Z`.
* The projector along a direction `b ≠ 0` is `P(b) = ½(I + (b/‖b‖)·σ)`; for `b = 0` we set
  `P(0) := P(e_Z) = |0⟩⟨0|` (a convention, needed only to make the machine's measurement and
  output decoding total).
-/

/-- The basis index of `n` qubits, equivalently the Boolean cube `{0,1}ⁿ`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- An `n`-qubit matrix. -/
abbrev QMat (n : ℕ) := Matrix (Cube n) (Cube n) ℂ

/-- A density matrix: positive semidefinite with unit trace. -/
def IsDensity {κ : Type*} [Fintype κ] (ρ : Matrix κ κ ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The tensor product `π₁ ⊗ ⋯ ⊗ πₙ` of one-qubit matrices, entrywise. -/
def prodMat {n : ℕ} (π : Fin n → Matrix Bool Bool ℂ) : QMat n :=
  Matrix.of fun x y => ∏ j, π j (x j) (y j)

/-- `M_n`, the product mixed states on `n` qubits (Problem 1, p.13): the matrices
`(x, y) ↦ ∏ⱼ πⱼ(xⱼ, yⱼ)` with every `πⱼ` positive semidefinite of trace one, i.e. the published
`GeoQAC.IsProductState` on the qubit set `Fin n` (same `Bool` indexing, mixed factors allowed). -/
def ProductMixed (n : ℕ) : Set (QMat n) :=
  {σ | GeoQAC.IsProductState (V := Fin n) σ}

/-- `c·σ = c₀X + c₁Y + c₂Z` for a real vector `c ∈ ℝ³`. -/
noncomputable def blochOp (c : Fin 3 → ℝ) : Matrix Bool Bool ℂ :=
  (c 0 : ℂ) • CompNonlocal.pauli 0 + (c 1 : ℂ) • CompNonlocal.pauli 1 +
    (c 2 : ℂ) • CompNonlocal.pauli 2

/-- The one-qubit matrix `½(I + c·σ)` with Bloch vector `c`. -/
noncomputable def qubitOf (c : Fin 3 → ℝ) : Matrix Bool Bool ℂ :=
  (1 / 2 : ℂ) • (1 + blochOp c)

/-- The Euclidean norm of `b ∈ ℝ³`. -/
noncomputable def bnorm (b : Fin 3 → ℝ) : ℝ := Real.sqrt (∑ k, b k ^ 2)

/-- The unit vector `e_Z = (0, 0, 1)`. -/
def eZ : Fin 3 → ℝ := ![0, 0, 1]

/-- The projector `P(b) = ½(I + (b/‖b‖)·σ)` onto the `+b` eigenvector; `P(0) := P(e_Z)`. -/
noncomputable def proj (b : Fin 3 → ℝ) : Matrix Bool Bool ℂ :=
  if b = 0 then qubitOf eZ else qubitOf ((bnorm b)⁻¹ • b)

end ProdMixedTomo


