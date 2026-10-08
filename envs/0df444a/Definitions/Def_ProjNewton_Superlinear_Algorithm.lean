-- Prove2me | Definitions.Def_ProjNewton_Superlinear_Algorithm
-- name    : ProjNewton_Superlinear_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:19.012307+00:00
-- url     : https://prove2.me/theorems/430b03ac-1648-4e19-93c4-fb0dc311ed36
-- title:
--   Critical points, active sets and the projected Newton iteration (32)–(37)
-- statement:
--   For the problem $\min\{f(x):x\in\mathbb R_+^n\}$, a **critical point** is a feasible $x$ with nonnegative partial derivatives, each equal to zero where $x^i>0$. Let $I^+(x)=\{i:x^i=0,\ \partial_i f(x)>0\}$ and let $B(x)=\{i:x^i=0\}$. A matrix is diagonal with respect to an index set when every off-diagonal entry in a row indexed by that set is zero.
--
--   Fix $\varepsilon>0$, a positive diagonal matrix $M=\operatorname{diag}(\mu)$, $0<\beta<1$ and $0<\sigma<1/2$. At $x_k$, put $w_k=\|x_k-[x_k-M\nabla f(x_k)]^+\|$, $\varepsilon_k=\min(\varepsilon,w_k)$ and $I_k^+=\{i:0\le x_k^i\le\varepsilon_k,\ \partial_i f(x_k)>0\}$. A chosen positive definite symmetric $D_k$ is diagonal with respect to $I_k^+$. With $p_k=D_k\nabla f(x_k)$ and $x_k(a)=[x_k-ap_k]^+$, the next iterate is
--
--   $$x_{k+1}=x_k(\beta^{m_k}),$$
--
--   where $m_k$ is the **first** nonnegative integer satisfying the two-sum Armijo inequality (37). The definitions also record the bounded-set gradient Lipschitz condition (A), the scaled quadratic-form bounds (B), the local second-order and strict-complementarity condition (C), and the modified Hessian $H_k$ of Proposition 4. This interface fixes the exact algorithm analyzed in the mission.
--
--   **Formalization Note** The run starts at $x_0\ge0$; matrix choices form a sequence. The Armijo right side uses $p_k$ outside $I_k^+$ and the actual projected displacement on $I_k^+$. The derivative and norm conventions are those of `Geometry`.
-- source:
--   Bertsekas, Projected Newton Methods for Optimization Problems with Simple Constraints, SIAM J. Control Optim. 20(2) (1982), pp. 225–236, (17)–(19), (32)–(41), (62)–(64), Proposition 4 definition of H_k

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Geometry

namespace ProjNewton.Superlinear

open Matrix Filter Topology Finset

variable {n : ℕ}

/-- The componentwise first order condition (3), including feasibility. -/
def IsCritical (f : Vec n → ℝ) (x : Vec n) : Prop :=
  x ∈ orthant n ∧ (∀ i, 0 ≤ pd f x i) ∧ ∀ i, 0 < x i → pd f x i = 0

/-- The index set (17). -/
noncomputable def Iplus (f : Vec n → ℝ) (x : Vec n) : Finset (Fin n) :=
  {i | x i = 0 ∧ 0 < pd f x i}

/-- The row condition (18); symmetry supplies the corresponding columns. -/
def DiagonalWrt (D : Matrix (Fin n) (Fin n) ℝ) (I : Finset (Fin n)) : Prop :=
  ∀ i ∈ I, ∀ j, j ≠ i → D i j = 0

/-- The binding set (62). -/
noncomputable def B (x : Vec n) : Finset (Fin n) := {i | x i = 0}

/-- The scaled gradient p=D∇f(x). -/
noncomputable def dir (f : Vec n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (x : Vec n) : Fin n → ℝ := D *ᵥ (fun i => pd f x i)

/-- The projected arc (19), (34). -/
noncomputable def arc (f : Vec n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (x : Vec n) (a : ℝ) : Vec n :=
  posPart (x - a • WithLp.toLp 2 (dir f D x))

/-- The projected gradient residual with M=diag μ. -/
noncomputable def w (f : Vec n → ℝ) (μ : Fin n → ℝ) (x : Vec n) : ℝ :=
  ‖x - posPart (x - WithLp.toLp 2 (fun i => μ i * pd f x i))‖

/-- The enlarged active set (32), using εₖ=min(ε,wₖ). -/
noncomputable def Ik (f : Vec n → ℝ) (μ : Fin n → ℝ) (ε : ℝ)
    (x : Vec n) : Finset (Fin n) :=
  {i | 0 ≤ x i ∧ x i ≤ min ε (w f μ x) ∧ 0 < pd f x i}

/-- The braces on the right of (37), before multiplication by σ. -/
noncomputable def armijoRHS (f : Vec n → ℝ) (μ : Fin n → ℝ) (ε : ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) (a : ℝ) : ℝ :=
  a * ∑ i ∈ (Ik f μ ε x)ᶜ, pd f x i * dir f D x i +
    ∑ i ∈ Ik f μ ε x, pd f x i * (x i - arc f D x a i)

/-- The trial-step inequality (37). -/
def Armijo (f : Vec n → ℝ) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) (m : ℕ) : Prop :=
  σ * armijoRHS f μ ε D x (β ^ m) ≤ f x - f (arc f D x (β ^ m))

/-- The first-acceptable-trial iteration (35)–(37). -/
def IsRun (f : Vec n → ℝ) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n) : Prop :=
  x 0 ∈ orthant n ∧ ∀ k, ∃ m : ℕ, Armijo f μ ε β σ (D k) (x k) m ∧
    (∀ m' < m, ¬ Armijo f μ ε β σ (D k) (x k) m') ∧
    x (k + 1) = arc f (D k) (x k) (β ^ m)

/-- The fixed parameters of the algorithm on pp. 228–229. -/
structure Params (μ : Fin n → ℝ) (ε β σ : ℝ) : Prop where
  eps_pos : 0 < ε
  mu_pos : ∀ i, 0 < μ i
  beta_mem : β ∈ Set.Ioo (0 : ℝ) 1
  sigma_mem : σ ∈ Set.Ioo (0 : ℝ) (1 / 2)

/-- The matrix-selection rule stated before (32). -/
def AdmissibleScaling (f : Vec n → ℝ) (μ : Fin n → ℝ) (ε : ℝ)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n) : Prop :=
  ∀ k, (D k).PosDef ∧ DiagonalWrt (D k) (Ik f μ ε (x k))

/-- Assumption (A), including its restriction to bounded sets. -/
def AssumptionA (f : Vec n → ℝ) : Prop :=
  ∀ S : Set (Vec n), Bornology.IsBounded S →
    ∃ L : NNReal, LipschitzOnWith L (gradient f) S

/-- Assumption (B), equation (41). -/
def AssumptionB (f : Vec n → ℝ) (μ : Fin n → ℝ)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n)
    (lam1 lam2 : ℝ) (q₁ q₂ : ℕ) : Prop :=
  0 < lam1 ∧ 0 < lam2 ∧ ∀ k (z : Fin n → ℝ),
    lam1 * w f μ (x k) ^ q₁ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (D k *ᵥ z) ∧
    z ⬝ᵥ (D k *ᵥ z) ≤ lam2 * w f μ (x k) ^ q₂ * (z ⬝ᵥ z)

/-- Assumption (C), with local minimality supplied separately. -/
def AssumptionC (f : Vec n → ℝ) (xs : Vec n) : Prop :=
  (∃ δ > 0, ContDiffOn ℝ 2 f (Metric.ball xs δ) ∧
    ∃ m₁ m₂ : ℝ, 0 < m₁ ∧ 0 < m₂ ∧
      ∀ x ∈ Metric.ball xs δ, ∀ z : Fin n → ℝ, z ≠ 0 →
        (∀ i ∈ B xs, z i = 0) →
          m₁ * (z ⬝ᵥ z) ≤ hessForm f x z ∧
          hessForm f x z ≤ m₂ * (z ⬝ᵥ z)) ∧
  ∀ i ∈ B xs, 0 < pd f xs i

/-- The matrix Hₖ in Proposition 4. -/
noncomputable def Hmat (f : Vec n → ℝ) (μ : Fin n → ℝ) (ε : ℝ)
    (x : Vec n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i ≠ j ∧ (i ∈ Ik f μ ε x ∨ j ∈ Ik f μ ε x)
    then 0 else pd2 f x i j

end ProjNewton.Superlinear


