-- Prove2me | Definitions.Def_PHLowerBound_TwoStage_Setting
-- name    : PHLowerBound_TwoStage_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:27.361427+00:00
-- url     : https://prove2.me/theorems/655ac06b-1ecf-4692-848b-d929589a46b1
-- title:
--   §2–§3 — two-stage SMIP, scenario and bundle subproblems, and PHA runs
-- statement:
--   Let $\Xi$ be the finite set of scenarios, with probabilities $p_\xi>0$ summing to one. A two-stage stochastic mixed-integer program has first-stage cost $c$, constraints $Ax\ge b$, second-stage costs $g(\xi)$, and recourse constraints $Wy\ge r(\xi)-T(\xi)x$. With $p_1\le n_1$ and $p_2\le n_2$, the first $p_1$ coordinates of $x\in\mathbb R^{n_1}$ and the first $p_2$ coordinates of $y\in\mathbb R^{n_2}$ are nonnegative integers; the remaining coordinates are free reals. The matrix $W$ is common to all scenarios.
--
--   The scenario set $X(\xi)$ consists of pairs $(x,y)$ satisfying these constraints. The extensive scenario formulation uses a common first-stage vector $\hat x$ and scenario copies $(x(\xi),y(\xi))$, with the printed implementability equations $p_\xi x(\xi)-p_\xi\hat x=0$. Its objective and optimal value are
--
--   $$z^*=\inf_{(\hat x,(x(\xi),y(\xi)))\text{ feasible}}\sum_{\xi\in\Xi}p_\xi\bigl(c^\top x(\xi)+g(\xi)^\top y(\xi)\bigr).$$
--
--   The scenario dual value $D_\xi(v)$ minimizes $c^\top x+g(\xi)^\top y+v^\top x$ over $X(\xi)$, and $D(w)=\sum_\xi p_\xi D_\xi(w(\xi))$. A finite run of Algorithm 1 starts from zero prices and unpenalized scenario minimizers, then aggregates $\hat x^\nu$, updates prices with coefficient $\rho$, and uses the quadratic term $(\rho/2)\|x-\hat x^\nu\|_2^2$ in later scenario subproblems.
--
--   For a partition $B$ of $\Xi$, each bundle $\beta$ has probability $P_\beta=\sum_{\xi\in\beta}p_\xi$, a feasible set $X(\beta)$ sharing one first-stage vector, and an objective with second-stage weights $p_\xi/P_\beta$. The analogous bundle value $D_\beta$, aggregate bound $D_B$, and finite Algorithm 2 runs use these same weights and the printed price update with $\rho$.
--
--   These definitions are the model used by the mission's lower-bound theorems and can be reused for other finite-support two-stage SMIPs.
--
--   **Formalization Note** All infima take values in the extended reals so an unbounded subproblem has value $-\infty$. A run is a prefix through its last computed price update. The displayed norm is represented by the sum of squared coordinates. Components of a bundle's recourse function outside that bundle are unconstrained and unused. The paper's slips in Algorithm 2 are read as $w^0(\beta)=0$ and $\hat x^\nu=\sum_{\beta\in B}P_\beta x^\nu(\beta)$; equal bundle sizes are not imposed.
-- source:
--   Gade et al., Obtaining Lower Bounds from the Progressive Hedging Algorithm for Stochastic Mixed-Integer Programs, author manuscript SAND2013-9195J (OSTI 1310314), pp. 3–10, (1)–(18), (21)–(26), Algorithms 1–2

import Mathlib

namespace PHLowerBound.TwoStage

open Matrix
attribute [local instance] Classical.decEq

/-- The mixed-integer restriction in (3), (6), (16), and (17). -/
def mixedInt (n p : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ j : Fin n, (j : ℕ) < p → 0 ≤ x j ∧ ∃ k : ℤ, x j = k}

/-- The finite-support, fixed-recourse two-stage SMIP of §2. -/
structure SMIP (Ξ : Type*) [Fintype Ξ] (n₁ p₁ n₂ p₂ m₁ m₂ : ℕ) where
  first_integer_dim : p₁ ≤ n₁
  second_integer_dim : p₂ ≤ n₂
  p : Ξ → ℝ
  p_pos : ∀ ξ, 0 < p ξ
  p_sum : ∑ ξ, p ξ = 1
  c : Fin n₁ → ℝ
  A : Matrix (Fin m₁) (Fin n₁) ℝ
  b : Fin m₁ → ℝ
  g : Ξ → Fin n₂ → ℝ
  W : Matrix (Fin m₂) (Fin n₂) ℝ
  T : Ξ → Matrix (Fin m₂) (Fin n₁) ℝ
  r : Ξ → Fin m₂ → ℝ

variable {Ξ : Type*} [Fintype Ξ] {n₁ p₁ n₂ p₂ m₁ m₂ : ℕ}

/-- The scenario feasible set X(ξ), p. 5. -/
def SMIP.X (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) (ξ : Ξ) :
    Set ((Fin n₁ → ℝ) × (Fin n₂ → ℝ)) :=
  {z | z.1 ∈ mixedInt n₁ p₁ ∧ z.2 ∈ mixedInt n₂ p₂ ∧
    P.b ≤ P.A *ᵥ z.1 ∧ P.r ξ - P.T ξ *ᵥ z.1 ≤ P.W *ᵥ z.2}

/-- The EFS feasible set (13)–(17), including weighted nonanticipativity (15). -/
def SMIP.EFSFeasible (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) :
    Set ((Fin n₁ → ℝ) × (Ξ → (Fin n₁ → ℝ) × (Fin n₂ → ℝ))) :=
  {v | v.1 ∈ mixedInt n₁ p₁ ∧ (∀ ξ, v.2 ξ ∈ P.X ξ) ∧
    ∀ ξ, P.p ξ • (v.2 ξ).1 - P.p ξ • v.1 = 0}

/-- The EFS objective (12). -/
noncomputable def SMIP.efsObj (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (v : (Fin n₁ → ℝ) × (Ξ → (Fin n₁ → ℝ) × (Fin n₂ → ℝ))) : ℝ := by
  classical
  exact ∑ ξ, P.p ξ * (P.c ⬝ᵥ (v.2 ξ).1 + P.g ξ ⬝ᵥ (v.2 ξ).2)

/-- The optimal EFS value. `EReal` preserves unbounded infima. -/
noncomputable def SMIP.zStar (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) : EReal :=
  ⨅ v ∈ P.EFSFeasible, ((P.efsObj v : ℝ) : EReal)

/-- The standing attainment assumption of §3.1. -/
def SMIP.HasOptimalSolution (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) : Prop :=
  ∃ v ∈ P.EFSFeasible, ∀ v' ∈ P.EFSFeasible, P.efsObj v ≤ P.efsObj v'

/-- The scenario subproblem value (18). -/
noncomputable def SMIP.Dξ (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) (ξ : Ξ)
    (v : Fin n₁ → ℝ) : EReal :=
  ⨅ z ∈ P.X ξ, ((P.c ⬝ᵥ z.1 + P.g ξ ⬝ᵥ z.2 + v ⬝ᵥ z.1 : ℝ) : EReal)

/-- The decomposed lower bound of Proposition 1. -/
noncomputable def SMIP.D (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (w : Ξ → Fin n₁ → ℝ) : EReal := by
  classical
  exact ∑ ξ, ((P.p ξ : ℝ) : EReal) * P.Dξ ξ (w ξ)

/-- The unpenalized scenario objective in Algorithm 1, Step 1. -/
noncomputable def SMIP.scenarioObj (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) (ξ : Ξ)
    (z : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)) : ℝ :=
  P.c ⬝ᵥ z.1 + P.g ξ ⬝ᵥ z.2

/-- The perturbed scenario objective in Algorithm 1, Step 5. -/
noncomputable def SMIP.scenarioProxObj (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (ξ : Ξ) (ρ : ℝ) (xhat w : Fin n₁ → ℝ)
    (z : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)) : ℝ :=
  P.scenarioObj ξ z + w ⬝ᵥ z.1 + ρ / 2 * ∑ j, (z.1 j - xhat j) ^ 2

/-- A prefix through iteration `N` of Algorithm 1. -/
def SMIP.IsPHARun (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) (ρ : ℝ)
    (x : ℕ → Ξ → Fin n₁ → ℝ) (y : ℕ → Ξ → Fin n₂ → ℝ)
    (xhat : ℕ → Fin n₁ → ℝ) (w : ℕ → Ξ → Fin n₁ → ℝ) (N : ℕ) : Prop :=
  w 0 = 0 ∧
  (∀ ξ, (x 1 ξ, y 1 ξ) ∈ P.X ξ ∧
    ∀ z ∈ P.X ξ, P.scenarioObj ξ (x 1 ξ, y 1 ξ) ≤ P.scenarioObj ξ z) ∧
  (∀ ν, 1 ≤ ν → ν ≤ N →
    xhat ν = ∑ ξ, P.p ξ • x ν ξ) ∧
  (∀ ν, 1 ≤ ν → ν ≤ N → ∀ ξ,
    w ν ξ = w (ν - 1) ξ + ρ • (x ν ξ - xhat ν)) ∧
  (∀ ν, 1 ≤ ν → ν < N → ∀ ξ,
    (x (ν + 1) ξ, y (ν + 1) ξ) ∈ P.X ξ ∧
    ∀ z ∈ P.X ξ,
      P.scenarioProxObj ξ ρ (xhat ν) (w ν ξ) (x (ν + 1) ξ, y (ν + 1) ξ) ≤
        P.scenarioProxObj ξ ρ (xhat ν) (w ν ξ) z)

/-- The probability mass of a bundle β. -/
noncomputable def SMIP.Pβ (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) (β : Finset Ξ) : ℝ := by
  classical
  exact ∑ ξ ∈ β, P.p ξ

/-- The bundle feasible set X(β) of §3.3. -/
def SMIP.Xβ (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) (β : Finset Ξ) :
    Set ((Fin n₁ → ℝ) × (Ξ → Fin n₂ → ℝ)) :=
  {z | z.1 ∈ mixedInt n₁ p₁ ∧ P.b ≤ P.A *ᵥ z.1 ∧
    ∀ ξ ∈ β, z.2 ξ ∈ mixedInt n₂ p₂ ∧
      P.r ξ - P.T ξ *ᵥ z.1 ≤ P.W *ᵥ z.2 ξ}

/-- The normalized bundle cost of (21). -/
noncomputable def SMIP.bundleObj (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) (β : Finset Ξ)
    (z : (Fin n₁ → ℝ) × (Ξ → Fin n₂ → ℝ)) : ℝ := by
  classical
  exact P.c ⬝ᵥ z.1 + ∑ ξ ∈ β, P.p ξ / P.Pβ β * (P.g ξ ⬝ᵥ z.2 ξ)

/-- The bundle subproblem value (26). -/
noncomputable def SMIP.Dβ (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂) (β : Finset Ξ)
    (v : Fin n₁ → ℝ) : EReal :=
  ⨅ z ∈ P.Xβ β, ((P.bundleObj β z + v ⬝ᵥ z.1 : ℝ) : EReal)

/-- The bundle lower bound in Proposition 3. -/
noncomputable def SMIP.DB (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (B : Finpartition (Finset.univ : Finset Ξ))
    (w : Finset Ξ → Fin n₁ → ℝ) : EReal := by
  classical
  exact ∑ β ∈ B.parts, ((P.Pβ β : ℝ) : EReal) * P.Dβ β (w β)

/-- The perturbed bundle objective in Algorithm 2, Step 5. -/
noncomputable def SMIP.bundleProxObj (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (β : Finset Ξ) (ρ : ℝ) (xhat w : Fin n₁ → ℝ)
    (z : (Fin n₁ → ℝ) × (Ξ → Fin n₂ → ℝ)) : ℝ :=
  P.bundleObj β z + w ⬝ᵥ z.1 + ρ / 2 * ∑ j, (z.1 j - xhat j) ^ 2

/-- A prefix through iteration `N` of Algorithm 2. -/
def SMIP.IsBundlePHARun (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (B : Finpartition (Finset.univ : Finset Ξ)) (ρ : ℝ)
    (x : ℕ → Finset Ξ → Fin n₁ → ℝ) (y : ℕ → Finset Ξ → Ξ → Fin n₂ → ℝ)
    (xhat : ℕ → Fin n₁ → ℝ) (w : ℕ → Finset Ξ → Fin n₁ → ℝ) (N : ℕ) : Prop :=
  (∀ β ∈ B.parts, w 0 β = 0) ∧
  (∀ β ∈ B.parts, (x 1 β, y 1 β) ∈ P.Xβ β ∧
    ∀ z ∈ P.Xβ β, P.bundleObj β (x 1 β, y 1 β) ≤ P.bundleObj β z) ∧
  (∀ ν, 1 ≤ ν → ν ≤ N →
    xhat ν = ∑ β ∈ B.parts, P.Pβ β • x ν β) ∧
  (∀ ν, 1 ≤ ν → ν ≤ N → ∀ β ∈ B.parts,
    w ν β = w (ν - 1) β + ρ • (x ν β - xhat ν)) ∧
  (∀ ν, 1 ≤ ν → ν < N → ∀ β ∈ B.parts,
    (x (ν + 1) β, y (ν + 1) β) ∈ P.Xβ β ∧
    ∀ z ∈ P.Xβ β,
      P.bundleProxObj β ρ (xhat ν) (w ν β) (x (ν + 1) β, y (ν + 1) β) ≤
        P.bundleProxObj β ρ (xhat ν) (w ν β) z)

end PHLowerBound.TwoStage


