-- Prove2me | Definitions.Def_ChoicePAC_MidPoint_Assumptions
-- name    : ChoicePAC_MidPoint_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:16.98566+00:00
-- url     : https://prove2.me/theorems/c33b0459-7433-4af3-a1db-3ddec6c673be
-- title:
--   Assumptions 2.1–2.2 and the App. B.1 matrix decomposition ($J_\lambda, J_y, J_0$, $W$, $H$, $Y_\Delta$)
-- statement:
--   **Assumptions** (Sec. 2.2, p. 316). Write the constraints of $\mathrm{DLP}[C,\lambda]$ as the rows of $\bar A$ (right-hand side $C$), the rows of $P$ (right-hand side $\lambda$) and $-x_j \le 0$.
--
--   1. *Nondegeneracy.* Every basic feasible solution, i.e. every feasible point whose active constraints span $\mathbb R^n$, has exactly $n$ active constraints.
--   2. *Assumption 2.1.* $\mathrm{DLP}[C,\lambda]$ is nondegenerate and has a unique optimal solution $Y$.
--   3. *Assumption 2.2.* For every optimal solution $z$ of
--   $$\max\ \bar r^\top x \quad\text{s.t.}\quad Px \le \lambda,\ x \ge 0, \qquad (3)$$
--   we have $\bar A z \not\le C$.
--
--   **Decomposition** (App. B.1, p. 332), relative to an optimal solution $Y$:
--   - $J_\lambda = \{j : Y_j = \lambda_{q(j)}\}$, $J_y = \{j : 0 < Y_j < \lambda_{q(j)}\}$, $J_0 = \{j : Y_j = 0\}$;
--   - $B_A = \{i : (\bar A Y)_i = C_i\}$ (binding resources) and $B_P = \{q : (PY)_q = \lambda_q\}$ (binding types), with $B_1$ the binding types having an offer in $J_\lambda$ and $B_2 = B_P\setminus B_1$;
--   - the augmented matrix
--   $$W = \begin{bmatrix} \bar A_{B,y} \\ P_{B_2,y}\end{bmatrix},$$
--   rows $B_A \sqcup B_2$, columns $J_y$;
--   - $H$, the $B_A$-columns of $W^{-1}$;
--   - the perturbed point $Y_\Delta$ with $Y_{\Delta,j} = Y_j$ for $j \notin J_y$ and $Y_{\Delta,y} = Y_y - H\Delta_B$ (App. B.2, p. 333).
--
--   These objects carry the perturbation analysis behind the proof of Theorem 5.3.
--
--   **Formalization Note** Nondegeneracy follows Bertsimas–Tsitsiklis (the paper's reference [2]). The paper's "without loss of generality … rearrange" is only an ordering of index sets; Lean uses subtypes of `Finset`s instead of permutations. $W^{-1}$ is the inverse function of $x \mapsto Wx$ (`Function.invFun`), which is the matrix inverse whenever $W$ is invertible (Observation B.2); $H$ needs no proof to be defined.
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, Assumptions 2.1–2.2, p. 316; App. B.1, p. 332; App. B.2, p. 333

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model

namespace ChoicePAC.MidPoint

open Matrix

namespace Instance

variable {NT n m : ℕ} (I : Instance NT n m)

/-- The constraints of `DLP[C, λ]` (2), indexed by `Fin m ⊕ Fin NT ⊕ Fin n`, written as
`row r ⬝ x ≤ rhs r`: the rows of `Ā` (right-hand side `C`), the rows of `P` (right-hand side `λ`),
and `−x_j ≤ 0`. -/
noncomputable def dlpRow : Fin m ⊕ Fin NT ⊕ Fin n → (Fin n → ℝ)
  | Sum.inl i => fun j => I.Abar i j
  | Sum.inr (Sum.inl q) => fun j => I.P q j
  | Sum.inr (Sum.inr j₀) => fun j => if j = j₀ then -1 else 0

/-- Right-hand sides of the constraints of `DLP[C, λ]`. -/
def dlpRhs : Fin m ⊕ Fin NT ⊕ Fin n → ℝ
  | Sum.inl i => I.C i
  | Sum.inr (Sum.inl q) => I.lam q
  | Sum.inr (Sum.inr _) => 0

open Classical in
/-- The constraints of `DLP[C, λ]` active (binding) at `x`. -/
noncomputable def dlpActive (x : Fin n → ℝ) : Finset (Fin m ⊕ Fin NT ⊕ Fin n) :=
  Finset.univ.filter (fun r => I.dlpRow r ⬝ᵥ x = I.dlpRhs r)

/-- `DLP[C, λ]` is nondegenerate (Bertsimas–Tsitsiklis, Def. 2.10): every basic feasible solution
— a feasible point whose active constraints span `ℝⁿ` — has exactly `n` active constraints. -/
def DLPNondegenerate : Prop :=
  ∀ x, I.DLPFeasible I.C I.lam x →
    Submodule.span ℝ (I.dlpRow '' ↑(I.dlpActive x)) = ⊤ → (I.dlpActive x).card = n

/-- Assumption 2.1 (p. 316): `DLP[C, λ]` is nondegenerate and has a unique optimal solution. -/
def Assumption21 : Prop :=
  I.DLPNondegenerate ∧ ∃! Y, I.IsDLPOptimal I.C I.lam Y

/-- Assumption 2.2 (p. 316): for every optimal solution `z` of
`max r̄ ⬝ x  s.t.  P x ≤ λ, x ≥ 0` (3), we have `Ā z ≰ C`. -/
def Assumption22 : Prop :=
  ∀ z : Fin n → ℝ,
    (I.P *ᵥ z ≤ I.lam ∧ 0 ≤ z ∧
      ∀ x : Fin n → ℝ, I.P *ᵥ x ≤ I.lam → 0 ≤ x → I.rbar ⬝ᵥ x ≤ I.rbar ⬝ᵥ z) →
    ¬ (I.Abar *ᵥ z ≤ I.C)

/-! ### Matrix decomposition relative to an optimal solution `Y` (App. B.1, p. 332) -/

open Classical in
/-- `J_λ = {j : Y_j = λ_{q(j)}}` (full components). -/
noncomputable def Jlam (Y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Y j = I.lam (I.typ j))

open Classical in
/-- `J_y = {j : 0 < Y_j < λ_{q(j)}}` (fractional components). -/
noncomputable def Jy (Y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => 0 < Y j ∧ Y j < I.lam (I.typ j))

open Classical in
/-- `J_0 = {j : Y_j = 0}` (zero components). -/
noncomputable def J0 (Y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Y j = 0)

open Classical in
/-- `B` for `Ā`: the resources whose capacity constraint binds at `Y`, `(Ā Y)_i = C_i`. -/
noncomputable def BA (Y : Fin n → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (I.Abar *ᵥ Y) i = I.C i)

open Classical in
/-- `B` for `P`: the customer types whose demand constraint binds at `Y`, `(P Y)_q = λ_q`. -/
noncomputable def BP (Y : Fin n → ℝ) : Finset (Fin NT) :=
  Finset.univ.filter (fun q => (I.P *ᵥ Y) q = I.lam q)

open Classical in
/-- `B_1`: the binding types that have an offer in `J_λ` (the rows of `P_{B_1}`, whose
`J_λ`-block is the identity). -/
noncomputable def B1 (Y : Fin n → ℝ) : Finset (Fin NT) :=
  (I.BP Y).filter (fun q => ∃ j ∈ I.Jlam Y, I.typ j = q)

/-- `B_2 = B_P \ B_1`: the binding types with no offer in `J_λ`. -/
noncomputable def B2 (Y : Fin n → ℝ) : Finset (Fin NT) := I.BP Y \ I.B1 Y

/-- The augmented matrix `W = [Ā_{B,y}; P_{B_2,y}]` (App. B.1, p. 332): rows indexed by the binding
resources and the types of `B_2`, columns by `J_y`. -/
noncomputable def Wmat (Y : Fin n → ℝ) : Matrix (↥(I.BA Y) ⊕ ↥(I.B2 Y)) ↥(I.Jy Y) ℝ :=
  fun r j => match r with
    | Sum.inl i => I.Abar i j
    | Sum.inr q => I.P q j

/-- `H`, the `B`-columns of `W⁻¹` (App. B.2, p. 333): `H j i = (W⁻¹ e_i)_j` for a binding resource
`i`, where `W⁻¹` is the inverse of the map `x ↦ W x` (meaningful when `W` is invertible,
Observation B.2). -/
noncomputable def Hmat (Y : Fin n → ℝ) : Matrix ↥(I.Jy Y) ↥(I.BA Y) ℝ :=
  fun j i => Function.invFun (I.Wmat Y).mulVec (Pi.single (Sum.inl i) 1) j

open Classical in
/-- The perturbed solution `Y_Δ` (App. B.2, p. 333): `Y_{Δ,j} = Y_j` for `j ∈ J_λ ∪ J_0` (indeed for
every `j ∉ J_y`) and `Y_{Δ,y} = Y_y − H Δ_B`. -/
noncomputable def Ypert (Y : Fin n → ℝ) (Δ : Fin m → ℝ) : Fin n → ℝ :=
  fun j => if h : j ∈ I.Jy Y then Y j - ∑ i : ↥(I.BA Y), I.Hmat Y ⟨j, h⟩ i * Δ i else Y j

end Instance

end ChoicePAC.MidPoint


