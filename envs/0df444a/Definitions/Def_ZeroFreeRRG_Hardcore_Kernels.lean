-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
-- name    : ZeroFreeRRG_Hardcore_Kernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:35:35.671965+00:00
-- url     : https://prove2.me/theorems/f7bcb52a-a355-4b50-afb6-d7286d158e81
-- title:
--   Spin systems, interaction kernels π, P, M, K, nonconstant eigenvalues, nontrivial parameters and Condition 2
-- statement:
--   The paper treats two spin systems in one framework (Definition 2.4). The **hardcore model** has spin space $\Omega=\{0,1\}$ (unoccupied, occupied) and parameter $t=\alpha$; the **antiferromagnetic Potts model** with $q\ge2$ colours has $\Omega=[q]$ and parameter $t=\beta$. Each comes with a symmetric edge-marginal matrix $P(t)$, eqs. (6)–(7):
--   $$P_\alpha=\begin{pmatrix}1-2\alpha&\alpha\\ \alpha&0\end{pmatrix},\qquad P_\beta=\frac{\mathbf 1\mathbf 1^{\top}+(\beta-1)I_q}{q(q-1+\beta)}.$$
--   From $P$ one forms the vertex marginal $\pi(t)=P(t)\mathbf 1$ (so $\pi_\alpha=(1-\alpha,\alpha)$ and $\pi=U_q$ for Potts), the normalized interaction kernel $M_{ij}(t)=P_{ij}(t)/(\pi_i(t)\pi_j(t))$ and the tree broadcasting operator $K_t=\operatorname{diag}(\pi(t))^{-1}P(t)$. $K_t$ leaves $\{f:\pi(t)^\top f=0\}$ invariant; its eigenvalues there are the **nonconstant eigenvalues** $\kappa_2(t),\dots,\kappa_{|\Omega|}(t)$.
--
--   A **nontrivial parameter** is $\alpha\in(0,1/2)$ for hardcore or $\beta\in[0,1)$ for Potts; §4.3 and §5.2 use the positive ones, $\alpha\in(0,1/2)$ or $\beta\in(0,1)$. The independent-spin endpoints are $\alpha=0$ and $\beta=1$.
--
--   **Condition 2** (strict Kesten–Stigum stability, p. 29) at $(d,t)$:
--   $$(d-1)\max_{a\ge2}|\kappa_a(t)|^2<1 .$$
--
--   These objects feed the normalized partition function, the cavity functional and the moment computations of the mission.
--
--   **Formalization Note.** `Model` has the two constructors `hardcore` and `potts q`; `Model.Valid` asks $q\ge2$. `Model.P`, `pi`, `M`, `K` are defined over any field, and are used over $\mathbb R$ at real parameters and over $\mathbb C$ at complex ones (the holomorphic extension of Definition 2.4). Hardcore index `0` is "unoccupied". `nonconstEig m z` is the *set* of eigenvalues of $K_z$ on $\pi(z)^\perp$; multiplicities play no role in any statement using it. Division by zero is Lean's $x/0=0$, relevant only where $\pi$ has a zero entry, which the statements exclude.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), pp. 15–16, Definition 2.4 and eqs. (6)–(7); p. 29, Condition 2

import Mathlib

open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- The two spin systems of the paper (Chen, Wang, Zhang, arXiv:2610.40510, §2.4, pp. 15–16): the
hardcore model and the antiferromagnetic `q`-state Potts model. -/
inductive Model : Type
  | hardcore : Model
  | potts (q : ℕ) : Model

/-- The spin space `Ω`: `{0, 1}` (unoccupied, occupied) for hardcore, `[q]` for Potts. -/
def Model.Spin : Model → Type
  | .hardcore => Fin 2
  | .potts q => Fin q

instance (m : Model) : Fintype m.Spin := by cases m <;> unfold Model.Spin <;> infer_instance
instance (m : Model) : DecidableEq m.Spin := by cases m <;> unfold Model.Spin <;> infer_instance

/-- A model is admissible when its spin space has at least two elements: always for hardcore,
`q ≥ 2` for Potts. -/
def Model.Valid : Model → Prop
  | .hardcore => True
  | .potts q => 2 ≤ q

/-- The symmetric edge-marginal matrix `P(t)` of eqs. (6)–(7) (p. 16), over any field (it is used
over `ℝ` and over `ℂ`): hardcore `P_α = [[1 − 2α, α], [α, 0]]`; Potts
`P_β = (𝟙𝟙ᵀ + (β − 1) I) / (q (q − 1 + β))`. -/
noncomputable def Model.P {𝕜 : Type*} [Field 𝕜] : (m : Model) → 𝕜 → Matrix m.Spin m.Spin 𝕜
  | .hardcore => fun α => fun i j =>
      if i.val = 0 ∧ j.val = 0 then 1 - 2 * α
      else if i.val = 1 ∧ j.val = 1 then 0 else α
  | .potts q => fun β => fun i j =>
      ((1 : 𝕜) + if i = j then β - 1 else 0) / ((q : 𝕜) * ((q : 𝕜) - 1 + β))

/-- The vertex marginal `π(t) = P(t) 𝟙` (Definition 2.4). For hardcore this is `(1 − α, α)`, for
Potts the uniform law `U_q`. -/
noncomputable def Model.pi {𝕜 : Type*} [Field 𝕜] (m : Model) (t : 𝕜) : m.Spin → 𝕜 :=
  fun i => ∑ j, m.P t i j

/-- The normalized interaction kernel `M_{ij}(t) = P_{ij}(t) / (π_i(t) π_j(t))` (Definition 2.4). -/
noncomputable def Model.M {𝕜 : Type*} [Field 𝕜] (m : Model) (t : 𝕜) : Matrix m.Spin m.Spin 𝕜 :=
  fun i j => m.P t i j / (m.pi t i * m.pi t j)

/-- The tree broadcasting operator `K_t = diag(π(t))⁻¹ P(t)` (Definition 2.4). -/
noncomputable def Model.K {𝕜 : Type*} [Field 𝕜] (m : Model) (t : 𝕜) : Matrix m.Spin m.Spin 𝕜 :=
  fun i j => m.P t i j / m.pi t i

/-- The set of nonconstant eigenvalues `κ_2(z), …, κ_{|Ω|}(z)` of `K_z` (Definition 2.4): the
eigenvalues of `K_z` on its invariant subspace `{f ∈ ℂ^Ω : π(z)ᵀ f = 0}`.

**Formalization Note.** The source lists them with algebraic multiplicity; every statement of this
mission uses them only through `max_a |κ_a|`, `κ_a ≤ 0 for all a ≥ 2`, so the set of values is
used. -/
def Model.nonconstEig (m : Model) (z : ℂ) : Set ℂ :=
  {κ | ∃ f : m.Spin → ℂ, f ≠ 0 ∧ ∑ i, m.pi z i * f i = 0 ∧ (m.K z).mulVec f = κ • f}

/-- A *nontrivial parameter* (p. 16): `α ∈ (0, 1/2)` for hardcore, `β ∈ [0, 1)` for Potts. -/
def Model.Nontrivial : Model → ℝ → Prop
  | .hardcore, t => 0 < t ∧ t < 1 / 2
  | .potts _, t => 0 ≤ t ∧ t < 1

/-- The positive nontrivial parameters of §4.3 and §5.2 (pp. 31, 39): `α ∈ (0, 1/2)` for hardcore,
`β ∈ (0, 1)` for Potts, where `Z_G(t) > 0` on every multigraph. -/
def Model.PosParam : Model → ℝ → Prop
  | .hardcore, t => 0 < t ∧ t < 1 / 2
  | .potts _, t => 0 < t ∧ t < 1

/-- Condition 2 (strict Kesten–Stigum stability, p. 29) at `(d, t)`:
`(d − 1) max_{a ≥ 2} |κ_a(t)|² < 1`, i.e. every nonconstant eigenvalue `κ` of `K_t` has
`(d − 1)|κ|² < 1`. -/
def Condition2 (m : Model) (d : ℕ) (t : ℝ) : Prop :=
  ∀ κ ∈ m.nonconstEig (t : ℂ), ((d : ℝ) - 1) * ‖κ‖ ^ 2 < 1

end ZeroFreeRRG.Hardcore


