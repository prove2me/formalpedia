-- Prove2me | Definitions.Def_MulticutLShaped_SimpleRecourse_Model
-- name    : MulticutLShaped_SimpleRecourse_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:36:56.862888+00:00
-- url     : https://prove2.me/theorems/028f2d19-8f7e-4967-8b15-bff0cb75ccaf
-- title:
--   The simple recourse problem (3), (19)–(20) and the equivalent LP (25)
-- statement:
--   This file sets up the **simple recourse problem** of Birge and Louveaux (1988), §5, and the linear program (25) it is equivalent to.
--
--   **Data.** First-stage data are a cost vector $c\in\mathbb R^{n_1}$, a matrix $A\in\mathbb R^{m_1\times n_1}$ and a vector $b\in\mathbb R^{m_1}$; the first-stage feasible set is
--   $$
--   K_1=\{x\in\mathbb R^{n_1} \mid Ax=b,\ x\ge 0\}.
--   $$
--   The technology matrix $T\in\mathbb R^{m_2\times n_1}$ is deterministic; $T_i$ denotes its $i$-th row and $\chi=Tx\in\mathbb R^{m_2}$ is the **tender**. For each row $i=1,\dots,m_2$ the random vector $\xi_i=(q_i^+,q_i^-,h_i)$ takes $J$ values $\xi_{ij}=(q^+_{ij},q^-_{ij},h_{ij})$, $j=1,\dots,J$, with probabilities $p_{ij}\ge 0$, $\sum_j p_{ij}=1$. Write $q_{ij}=q^+_{ij}+q^-_{ij}$. Throughout, $q_{ij}\ge 0$ for all $i,j$.
--
--   **Second stage.** For a cost pair $(q^+,q^-)$, a right-hand side $h$ and a tender component $\chi_i$, the one-row recourse problem (20) is
--   $$
--   \psi(\chi_i;q^+,q^-,h)=\min\{q^+y^+ + q^-y^- \mid y^+-y^-=h-\chi_i,\ y^+\ge 0,\ y^-\ge 0\},
--   $$
--   taken as an infimum in the extended reals. Then $\psi_i(\chi_i,\xi_{ij})=\psi(\chi_i;q^+_{ij},q^-_{ij},h_{ij})$,
--   $$
--   \Psi_i(\chi_i)=E\,\psi_i(\chi_i,\xi_i)=\sum_{j=1}^J p_{ij}\,\psi_i(\chi_i,\xi_{ij}),\qquad \Psi(\chi)=\sum_{i=1}^{m_2}\Psi_i(\chi_i),
--   $$
--   the latter by the separability (19) $\psi(\chi,\xi)=\sum_i\psi_i(\chi_i,\xi_i)$; only the marginal distributions of the $\xi_i$ enter. The objective of problem (3) is $z(x)=cx+\Psi(Tx)$, and $x$ is **optimal** if $x\in K_1$ and $z(x)\le z(x')$ for all $x'\in K_1$.
--
--   **The LP (25).** In the variables $(x,\chi,u)$ with $u=(u_{ij})$, (25) is
--   $$
--   \min\ cx+\sum_{i=1}^{m_2}\sum_{j=1}^J p_{ij}q^-_{ij}(\chi_i-h_{ij})+\sum_{i=1}^{m_2}\sum_{j=1}^J u_{ij}
--   $$
--   subject to $Ax=b$, $x\ge 0$, $Tx-\chi=0$, $u_{ij}\ge p_{ij}q_{ij}(h_{ij}-\chi_i)$ and $u_{ij}\ge 0$ for all $i,j$. The file defines its feasible set, its objective and its optimal solutions.
--
--   These objects are the model on which the multicut algorithm for simple recourse problems and its iteration bound are stated.
--
--   **Formalization Note.** The assumption $q_{ij}\ge 0$ is a field of the data structure; the paper uses it without stating it (without it (20) is unbounded below). $\psi$ is defined as the LP's infimum, not by its closed form, which is a separate theorem ((22)–(23)). Expectations are finite sums over the $J$ realizations, computed in `EReal`; under $q_{ij}\ge0$ every value is finite. The constraint $x\ge 0$ of (3) is kept in (25), whose display omits it.
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 385, Eq. (3); pp. 388-389, Section 5, Eqs. (19), (20), (25)

import Mathlib

namespace MulticutLShaped.SimpleRecourse

/-- Data of the simple recourse problem (3), (19)–(20) of Birge–Louveaux (1988), pp. 385, 388–389,
with first-stage data `c ∈ ℝ^{n1}`, `A ∈ ℝ^{m1×n1}`, `b ∈ ℝ^{m1}`, the non-stochastic technology
matrix `T ∈ ℝ^{m2×n1}`, and, for each row `i : Fin m2`, the `J` realizations
`ξ_ij = (q⁺_ij, q⁻_ij, h_ij)` of `ξ_i` with probabilities `p_ij`.
`hq` is the standing assumption `q_ij = q⁺_ij + q⁻_ij ≥ 0` (implicit in the paper: without it the
second-stage LP (20) is unbounded below). -/
structure Instance (n1 m1 m2 J : ℕ) where
  c : Fin n1 → ℝ
  A : Matrix (Fin m1) (Fin n1) ℝ
  b : Fin m1 → ℝ
  T : Matrix (Fin m2) (Fin n1) ℝ
  qplus : Fin m2 → Fin J → ℝ
  qminus : Fin m2 → Fin J → ℝ
  h : Fin m2 → Fin J → ℝ
  p : Fin m2 → Fin J → ℝ
  p_nonneg : ∀ i j, 0 ≤ p i j
  p_sum : ∀ i, ∑ j, p i j = 1
  hq : ∀ i j, 0 ≤ qplus i j + qminus i j

variable {n1 m1 m2 J : ℕ}

/-- `q_ij = q⁺_ij + q⁻_ij` (p. 389). -/
def Instance.q (inst : Instance n1 m1 m2 J) (i : Fin m2) (j : Fin J) : ℝ :=
  inst.qplus i j + inst.qminus i j

/-- The first-stage feasible set `K₁ = {x | Ax = b, x ≥ 0}` of (3). -/
def K1 (inst : Instance n1 m1 m2 J) : Set (Fin n1 → ℝ) :=
  {x | inst.A.mulVec x = inst.b ∧ ∀ k, 0 ≤ x k}

/-- The optimal value of the one-row simple recourse LP (20),
`ψ(χ; q⁺, q⁻, h) = min { q⁺ y⁺ + q⁻ y⁻ | y⁺ − y⁻ = h − χ, y⁺ ≥ 0, y⁻ ≥ 0 }`,
as an infimum in `EReal` (so `⊥` if the LP were unbounded below). -/
noncomputable def psiVal (qp qm h χ : ℝ) : EReal :=
  sInf {z : EReal | ∃ yp ym : ℝ, 0 ≤ yp ∧ 0 ≤ ym ∧ yp - ym = h - χ ∧
    z = ((qp * yp + qm * ym : ℝ) : EReal)}

/-- `ψ_i(χ_i, ξ_ij)` of (20) at the `j`-th realization `ξ_ij = (q⁺_ij, q⁻_ij, h_ij)`. -/
noncomputable def psi (inst : Instance n1 m1 m2 J) (i : Fin m2) (j : Fin J) (χi : ℝ) : EReal :=
  psiVal (inst.qplus i j) (inst.qminus i j) (inst.h i j) χi

/-- `Ψ_i(χ_i) = E ψ_i(χ_i, ξ_i) = Σ_j p_ij ψ_i(χ_i, ξ_ij)`. -/
noncomputable def PsiI (inst : Instance n1 m1 m2 J) (i : Fin m2) (χi : ℝ) : EReal :=
  ∑ j, (inst.p i j : EReal) * psi inst i j χi

/-- The expected recourse function `Ψ(χ) = E ψ(χ, ξ) = Σ_i Ψ_i(χ_i)` of (3), using the separability
(19). Only the marginal laws of the `ξ_i` enter. -/
noncomputable def Psi (inst : Instance n1 m1 m2 J) (χ : Fin m2 → ℝ) : EReal :=
  ∑ i, PsiI inst i (χ i)

/-- The objective `z(x) = cx + Ψ(Tx)` of (3), the tender being `χ = Tx`. -/
noncomputable def z (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) : EReal :=
  ((inst.c ⬝ᵥ x : ℝ) : EReal) + Psi inst (inst.T.mulVec x)

/-- `x` is an optimal solution of the simple recourse problem (3), (19)–(20). -/
def IsOptimal (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) : Prop :=
  x ∈ K1 inst ∧ ∀ x' ∈ K1 inst, z inst x ≤ z inst x'

/-- Feasibility for the LP (25) in the variables `(x, χ, u)`: `Ax = b`, `x ≥ 0` (from (3); omitted
in the display of (25)), `Tx − χ = 0`, `u_ij ≥ p_ij q_ij (h_ij − χ_i)` and `u_ij ≥ 0`. -/
def Feasible25 (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) (χ : Fin m2 → ℝ)
    (u : Fin m2 → Fin J → ℝ) : Prop :=
  inst.A.mulVec x = inst.b ∧ (∀ k, 0 ≤ x k) ∧ inst.T.mulVec x - χ = 0 ∧
    (∀ i j, inst.p i j * inst.q i j * (inst.h i j - χ i) ≤ u i j) ∧ (∀ i j, 0 ≤ u i j)

/-- The objective of (25):
`cx + Σ_i Σ_j p_ij q⁻_ij (χ_i − h_ij) + Σ_i Σ_j u_ij`. -/
def obj25 (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) (χ : Fin m2 → ℝ)
    (u : Fin m2 → Fin J → ℝ) : ℝ :=
  inst.c ⬝ᵥ x + ∑ i, ∑ j, inst.p i j * inst.qminus i j * (χ i - inst.h i j) + ∑ i, ∑ j, u i j

/-- `(x, χ, u)` is an optimal solution of the LP (25). -/
def IsOptimal25 (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) (χ : Fin m2 → ℝ)
    (u : Fin m2 → Fin J → ℝ) : Prop :=
  Feasible25 inst x χ u ∧
    ∀ x' χ' u', Feasible25 inst x' χ' u' → obj25 inst x χ u ≤ obj25 inst x' χ' u'

end MulticutLShaped.SimpleRecourse


