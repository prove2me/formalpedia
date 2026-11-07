-- Prove2me | Definitions.Def_ShadowBootstrap_braket
-- name    : ShadowBootstrap_braket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:04.839303+00:00
-- url     : https://prove2.me/theorems/4fcc938a-31d0-43be-9857-d4d631da14a1
-- title:
--   Vectors and norms: $\langle u|v\rangle$, $\|v\|_2^2$, $|u\rangle\langle v|$, $\|A\|_F^2$, $\|A\|_{op}$, histograms
-- statement:
--   Basic vector and matrix notation of §3.1 (p.8). For vectors $u, v$ indexed by a finite set (here bit strings $z \in \{0,1\}^n$), the inner product is $\langle u|v\rangle = \sum_z \overline{u_z}\, v_z$ and the squared Euclidean norm is $\|v\|_2^2 = \sum_z |v_z|^2$; $v$ is a **unit vector** when $\|v\|_2 = 1$. The outer product $|u\rangle\langle v|$ is the matrix with entries $u_a\overline{v_b}$, so a unit vector $|\psi\rangle$ gives the density matrix $\psi = |\psi\rangle\langle\psi|$ and the infidelity of two pure states is $1 - \operatorname{Tr}(\psi\sigma) = 1 - |\langle\psi|\sigma\rangle|^2$.
--
--   For a square complex matrix $A$, $\|A\|_F^2 = \sum_{a,b} |A_{ab}|^2$ is the squared Frobenius norm and $\|A\|_{op} = \sup_{\|v\|_2 = 1}\|Av\|_2$ the operator norm. The **histogram** of outcomes $b_1, \dots, b_S$ assigns to each bit string $z$ the number of shots with $b_a = z$ (§3.4, p.10); bit strings that were never observed get count $0$.
--
--   These are the quantities in which every bound of the paper is stated.
--
--   **Formalization Note** The operator norm is Mathlib's $\ell^2$ operator norm on matrices (`Matrix.Norms.L2Operator`).
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), §3.1, p.8; §3.4, p.10

import Mathlib

open scoped Matrix

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
§3.1, p.8: the inner product `⟨u|v⟩ = Σ_z \overline{u_z} v_z` of two state vectors, so that the
infidelity of pure states is `1 − Tr(ψσ) = 1 − |⟨ψ|σ⟩|²`.

**Formalization Note** A state vector is a function from a finite index type (in this mission the
bit strings `Bits n = Fin n → Fin 2`) to `ℂ`. The module also fixes the squared Euclidean norm
`‖v‖₂²`, unit vectors, the outer product `|u⟩⟨v|`, the squared Frobenius norm `‖A‖_F²`, the
operator norm `‖A‖_op` (Mathlib's `ℓ²` operator norm, `Matrix.Norms.L2Operator`), and the
histogram of a list of outcomes (§3.4, p.10). -/
def braket {α : Type} [Fintype α] (u v : α → ℂ) : ℂ :=
  ∑ z, star (u z) * v z

/-- The squared Euclidean norm `‖v‖₂² = Σ_z |v_z|²` (§3.1, p.8). -/
noncomputable def vnormSq {α : Type} [Fintype α] (v : α → ℂ) : ℝ :=
  ∑ z, ‖v z‖ ^ 2

/-- `v` is a unit vector: `‖v‖₂ = 1`. -/
def IsUnitVec {α : Type} [Fintype α] (v : α → ℂ) : Prop :=
  vnormSq v = 1

/-- The outer product `|u⟩⟨v|`, the matrix with entries `u_a \overline{v_b}`. For a unit vector
`ψ`, `ketbra ψ ψ` is the density matrix `ψ = |ψ⟩⟨ψ|` (§3.1, p.8). -/
def ketbra {α : Type} (u v : α → ℂ) : Matrix α α ℂ :=
  Matrix.vecMulVec u (star v)

/-- The squared Frobenius norm `‖A‖_F² = Σ_{a,b} |A_{ab}|²` (§3.1, p.8). -/
noncomputable def frobSq {α : Type} [Fintype α] (A : Matrix α α ℂ) : ℝ :=
  ∑ a, ∑ b, ‖A a b‖ ^ 2

open scoped Matrix.Norms.L2Operator in
/-- The operator norm `‖A‖_op` (§3.1, p.8): Mathlib's `ℓ²` operator norm
`sup_{‖v‖₂ = 1} ‖Av‖₂` on square complex matrices. -/
noncomputable def opNorm {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) : ℝ :=
  ‖A‖

/-- The histogram of the outcomes `b₁, …, b_S` (§3.4, p.10): the number of shots `a` with
`b_a = z`. Absent keys read as `0`, as in the paper's dictionary representation. -/
def histOf {α : Type} [DecidableEq α] {S : ℕ} (bs : Fin S → α) (z : α) : ℕ :=
  (Finset.univ.filter fun a => bs a = z).card

end ShadowBootstrap


