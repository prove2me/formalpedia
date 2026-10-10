-- Prove2me | Definitions.Def_DDMomentDRO_Type3_Setting
-- name    : DDMomentDRO_Type3_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:39.023236+00:00
-- url     : https://prove2.me/theorems/05161580-9cab-4022-8c2e-a0a5e8e67edc
-- title:
--   (2), (14), (15), (C-21), pp. 6, 12, 38 — stage data, the Type 3 ambiguity set, stage values, SDP values and the Lagrangian
-- statement:
--   This file fixes the objects of one stage $t$ of the Bellman equations (2) of Yu and Shen under the Type 3 (Delage–Ye-type) ambiguity set (14).
--
--   **Stage data.** The state is $x \in \mathbb R^I$ (binary on the page), the stage variable is $y \in \mathbb R^{I\times J}$, and $S \subseteq \mathbb R^I \times \mathbb R^{I\times J}$ is the stage feasible set $X_t(x_{t-1},\xi_t)$ with stage cost $g(x,y)$. The next-stage random vector has the finite support $\{\xi^1,\dots,\xi^K\} \subset \mathbb R^J$ (Assumption 3), and $Q^k(x) = Q_{t+1}(x,\xi^k)$ is the next-stage value at scenario $k$. The decision-dependent estimates are a mean $\mu(x) \in \mathbb R^J$ and a matrix $\Sigma(x) \in \mathbb R^{J\times J}$, and $\gamma,\eta$ are the size parameters.
--
--   **Ambiguity set (14).** For a weight vector $p \in \mathbb R^K$ write $\bar\xi(p) = \sum_k p_k \xi^k$ and $M_k(x) = (\xi^k-\mu(x))(\xi^k-\mu(x))^\top$. Then
--   $$\mathcal P^{D_3}(x) = \Big\{p \in \mathbb R^K : \sum_{k} p_k = 1,\ (\bar\xi(p)-\mu(x))^\top\Sigma(x)^{-1}(\bar\xi(p)-\mu(x)) \le \gamma,\ \sum_k p_k M_k(x) \preceq \eta\Sigma(x),\ p \ge 0\Big\}.$$
--   A **Slater point** at $x$ is a $p \ge 0$ with $\sum_k p_k = 1$ satisfying the second condition with $<$ and the third with $\prec$ (strict matrix order).
--
--   **Stage values.** The worst-case values at $x$ are $\{\sum_k p_k Q^k(x) : p \in \mathcal P^{D_3}(x)\}$, and the stage values are the numbers $g(x,y) + w$ with $(x,y) \in S$ and $w$ the **greatest** worst-case value at $x$ (the inner maximum of (2), attained). "$Q_t = q$" means that $q$ is the least stage value.
--
--   **SDP values (15).** With the Frobenius product $A \bullet B = \operatorname{tr}(A^\top B)$ and the block matrix $Z = \begin{pmatrix} z_1 & z_2\\ z_2^\top & z_3\end{pmatrix}$, a dual point $(s,z_1,z_2,z_3,Y)$ is feasible at $x$ when $Z \succeq 0$, $Y \succeq 0$ and
--   $$s - 2 z_2^\top \xi^k + M_k(x) \bullet Y \ge Q^k(x) \quad \text{for all } k,$$
--   and its objective is $s + \Sigma(x)\bullet z_1 - 2\mu(x)^\top z_2 + \gamma z_3 + \eta\,\Sigma(x)\bullet Y$. The SDP values are $g(x,y)$ plus this objective, over $(x,y) \in S$ and feasible dual points.
--
--   **Lagrangian (C-21).** For $p \in \mathbb R^K$, $\tau \in \mathbb R^J$, $s \in \mathbb R$, $u \in \mathbb R^J$,
--   $$L = \sum_k p_k Q^k(x) - s\Big(\sum_k p_k - 1\Big) + u^\top(\tau - \bar\xi(p)) + \begin{pmatrix}\Sigma(x) & \tau-\mu(x)\\ (\tau-\mu(x))^\top & \gamma\end{pmatrix}\bullet Z + \Big(\eta\Sigma(x) - \sum_k p_k M_k(x)\Big)\bullet Y,$$
--   and the Lagrangian values are the values of $L$ over $p \ge 0$, $\tau \in \mathbb R^J$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Indices are 0-based (`Fin K`, `Fin J`). Matrix inequalities are Mathlib's `PosSemidef`/`PosDef` of the difference, which include symmetry. `(Sig x)⁻¹` is Mathlib's inverse, which is junk (zero) for a singular matrix; every theorem therefore assumes $\Sigma(x) \succ 0$. The condition $p \ge 0$ is part of the set: the page's (14) omits it, but Assumption 3 calls $p$ a probability and the proof's (C-20f) states it. The page imposes affine dependence (12) of $\mu,\Sigma$ on $x$ only later, for the MILP (16); here $\mu$ and $\Sigma$ are arbitrary functions. $Q^k$ is a free real function: the stage theorems use nothing about the recursion. Minima and maxima are encoded by `IsLeast`/`IsGreatest`, never by `sInf`/`sSup`.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, pp. 5–6, (2), Assumption 3; p. 12, (14), Theorem 3, (15); p. 38, (C-20), (C-21), (C-22)

import Mathlib

namespace DDMomentDRO.Type3

open Matrix

/-- Frobenius inner product `A • B = trace (Aᵀ B)`. -/
def frob {n : Type*} [Fintype n] (A B : Matrix n n ℝ) : ℝ := (Aᵀ * B).trace

/-- The mean `∑ₖ pₖ ξᵏ` of the support points under the weights `p`. -/
def meanVec {J K : ℕ} (ξ : Fin K → Fin J → ℝ) (p : Fin K → ℝ) : Fin J → ℝ :=
  ∑ k, p k • ξ k

/-- The outer product `(ξᵏ - μ(x))(ξᵏ - μ(x))ᵀ`. -/
def outerDev {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (x : Fin I → ℝ) (k : Fin K) : Matrix (Fin J) (Fin J) ℝ :=
  Matrix.vecMulVec (ξ k - μ x) (ξ k - μ x)

/-- The centred second-moment matrix `∑ₖ pₖ (ξᵏ - μ(x))(ξᵏ - μ(x))ᵀ`. -/
def secondMoment {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (x : Fin I → ℝ) (p : Fin K → ℝ) : Matrix (Fin J) (Fin J) ℝ :=
  ∑ k, p k • outerDev ξ μ x k

/-- The Type 3 ambiguity set (14), together with `p ≥ 0` (C-20f). -/
def amb3 {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ) (x : Fin I → ℝ) :
    Set (Fin K → ℝ) :=
  {p | ∑ k, p k = 1 ∧
    (meanVec ξ p - μ x) ⬝ᵥ ((Sig x)⁻¹ *ᵥ (meanVec ξ p - μ x)) ≤ γ ∧
    (η • Sig x - secondMoment ξ μ x p).PosSemidef ∧
    ∀ k, 0 ≤ p k}

/-- A Slater point of (14) at `x`: a probability vector satisfying (14b) and (14c) strictly. -/
def IsSlaterPoint {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ) (x : Fin I → ℝ)
    (p : Fin K → ℝ) : Prop :=
  (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧
    (meanVec ξ p - μ x) ⬝ᵥ ((Sig x)⁻¹ *ᵥ (meanVec ξ p - μ x)) < γ ∧
    (η • Sig x - secondMoment ξ μ x p).PosDef

/-- Values `∑ₖ pₖ Qᵏ_{t+1}(x)` of the inner maximization of (2) over the Type 3 set. -/
def wcVal {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (γ η : ℝ) (x : Fin I → ℝ) : Set ℝ :=
  {v | ∃ p, p ∈ amb3 ξ μ Sig γ η x ∧ v = ∑ k, p k * Qn x k}

/-- Values `g(x, y) + max_p ∑ₖ pₖ Qᵏ_{t+1}(x)` of the stage-t Bellman equation (2), over
feasible `(x, y)` at which the inner maximum is attained. -/
def stageVals {I J K : ℕ} (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (Qn : (Fin I → ℝ) → Fin K → ℝ)
    (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ) : Set ℝ :=
  {v | ∃ x y w, (x, y) ∈ S ∧ IsGreatest (wcVal Qn ξ μ Sig γ η x) w ∧ v = g x y + w}

/-- The symmetric block matrix `(A v; vᵀ c)` of size `(J + 1) × (J + 1)`. -/
def block2 {J : ℕ} (A : Matrix (Fin J) (Fin J) ℝ) (v : Fin J → ℝ) (c : ℝ) :
    Matrix (Fin J ⊕ Unit) (Fin J ⊕ Unit) ℝ :=
  Matrix.fromBlocks A (Matrix.replicateCol Unit v) (Matrix.replicateRow Unit v) (fun _ _ => c)

/-- The objective (15a) without the stage cost:
`s + Σ(x) • z₁ - 2 μ(x)ᵀ z₂ + γ z₃ + η Σ(x) • Y`. -/
def dualObj3 {I J : ℕ} (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ) (x : Fin I → ℝ)
    (s : ℝ) (z1 : Matrix (Fin J) (Fin J) ℝ) (z2 : Fin J → ℝ) (z3 : ℝ)
    (Y : Matrix (Fin J) (Fin J) ℝ) : ℝ :=
  s + frob (Sig x) z1 - 2 * (μ x ⬝ᵥ z2) + γ * z3 + η * frob (Sig x) Y

/-- Feasibility for (15b)–(15c) at `x`. -/
def DualFeas3 {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (x : Fin I → ℝ)
    (s : ℝ) (z1 : Matrix (Fin J) (Fin J) ℝ) (z2 : Fin J → ℝ) (z3 : ℝ)
    (Y : Matrix (Fin J) (Fin J) ℝ) : Prop :=
  (block2 z1 z2 z3).PosSemidef ∧ Y.PosSemidef ∧
    ∀ k, Qn x k ≤ s - 2 * (z2 ⬝ᵥ ξ k) + frob (outerDev ξ μ x k) Y

/-- Objective values (15a) of the mixed-integer SDP (15) at its feasible points. -/
def dualVals3 {I J K : ℕ} (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (Qn : (Fin I → ℝ) → Fin K → ℝ)
    (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ) : Set ℝ :=
  {v | ∃ x y s z1 z2 z3 Y, (x, y) ∈ S ∧ DualFeas3 Qn ξ μ x s z1 z2 z3 Y ∧
    v = g x y + dualObj3 μ Sig γ η x s z1 z2 z3 Y}

/-- The Lagrangian `L(p, τ, s, u, Z, Y)` of (C-20), first line of (C-21). -/
def lagr {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (γ η : ℝ) (x : Fin I → ℝ) (p : Fin K → ℝ) (τ : Fin J → ℝ) (s : ℝ) (u : Fin J → ℝ)
    (z1 : Matrix (Fin J) (Fin J) ℝ) (z2 : Fin J → ℝ) (z3 : ℝ)
    (Y : Matrix (Fin J) (Fin J) ℝ) : ℝ :=
  ∑ k, p k * Qn x k - s * (∑ k, p k - 1) + u ⬝ᵥ (τ - meanVec ξ p)
    + frob (block2 (Sig x) (τ - μ x) γ) (block2 z1 z2 z3)
    + frob (η • Sig x - secondMoment ξ μ x p) Y

/-- Values of the Lagrangian over the domain `p ≥ 0`, `τ ∈ ℝ^J` of the inner problem of (C-22). -/
def lagrVals {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (γ η : ℝ) (x : Fin I → ℝ) (s : ℝ) (u : Fin J → ℝ)
    (z1 : Matrix (Fin J) (Fin J) ℝ) (z2 : Fin J → ℝ) (z3 : ℝ)
    (Y : Matrix (Fin J) (Fin J) ℝ) : Set ℝ :=
  {v | ∃ (p : Fin K → ℝ) (τ : Fin J → ℝ), (∀ k, 0 ≤ p k) ∧
    v = lagr Qn ξ μ Sig γ η x p τ s u z1 z2 z3 Y}

end DDMomentDRO.Type3


