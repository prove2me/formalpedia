-- Prove2me | Definitions.Def_AffinePolicies_SqrtBound_Setting
-- name    : AffinePolicies_SqrtBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:15:32.874896+00:00
-- url     : https://prove2.me/theorems/c297f217-1ced-4b1e-90dd-4e2a7ee24850
-- title:
--   (1), (38), (48), Fig. 1, (60)–(63) — two-stage adaptive LP Π_Adapt(𝒰), affine policies, Algorithm 𝒜 and the k-uncertain model
-- statement:
--   This file fixes the objects of §5 of Bertsimas and Goyal. The two-stage problem (1), $z_{Adapt}$, affine policies and $z_{Aff}$ are imported from the shared setting file `AffinePolicies.Simplex.Setting` (recalled here for the reader).
--
--   **The two-stage problem (1).** Let $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}$, $d\in\mathbb R^{n_2}$ and let $\mathcal U\subseteq\mathbb R^m$ be the uncertainty set of right-hand sides. A first-stage decision $x\in\mathbb R^{n_1}$ together with a second-stage rule $b\mapsto y(b)\in\mathbb R^{n_2}$ is **feasible** for $\Pi_{Adapt}(\mathcal U)$ if
--   $$x\ge 0,\qquad y(b)\ge 0,\qquad Ax+By(b)\ge b\quad\text{for all } b\in\mathcal U .$$
--   A real $t$ **bounds the worst-case cost** of $(x,y)$ if $c^Tx+d^Ty(b)\le t$ for every $b\in\mathcal U$. The optimal value is
--   $$z_{Adapt}(\mathcal U)=\inf\{t : \text{some feasible }(x,y)\text{ has worst-case cost at most } t\},$$
--   which equals the paper's $\min\,c^Tx+\max_{b\in\mathcal U}d^Ty(b)$. An **affine policy** is a rule $y(b)=Pb+q$ with $P\in\mathbb R^{n_2\times m}$, $q\in\mathbb R^{n_2}$; it must satisfy $Pb+q\ge 0$ on $\mathcal U$ like any second-stage rule. $z_{Aff}(\mathcal U)$ is the same infimum taken over feasible solutions with an affine second stage. Optimal adaptive and optimal affine solutions are those that achieve every cost bound achieved by any competitor of their class.
--
--   **Algorithm $\mathcal A$ (Fig. 1).** Given $\mu\in\mathbb R^m$ (in the paper $\mu_j=\max\{b_j : b\in\mathcal U\}$, display (38)), write $\sum_{j\in J}b_j/\mu_j$ for the scaled sum over an index set $J$. Starting from $b^0=0$ and $J_1^0=\{1,\dots,m\}$, iteration $k$ is executed while some $b\in\mathcal U$ has $\sum_{j\in J_1^{k-1}}b_j/\mu_j>\sqrt m$; it picks a maximizer $u^k\in\mathcal U$ of that scaled sum, sets $b^k_j=b^{k-1}_j+u^k_j$ for $j\in J_1^{k-1}$ and $b^k_j=b^{k-1}_j$ otherwise, and removes from $J_1$ every $j$ with $b^k_j\ge\mu_j$ (these join $J_2$). Because the maximizers are not unique, a run is recorded as a sequence of choices $u^1,u^2,\dots$: a **complete run with $K$ iterations** is one in which iterations $1,\dots,K$ are executed with maximizing choices and the loop test fails for $J_1^K$. The algorithm outputs $\beta=u^1+\dots+u^K$, $J_1=J_1^K$ and $J_2=\{1,\dots,m\}\setminus J_1$.
--
--   **The policy of the proof of Theorem 4.** For a second-stage rule $y^*$, points $\beta^1,\dots,\beta^m$, a vector $\mu$ and an index set $J$, the affine policy
--   $$\tilde y(b)=\sum_{j\in J}\frac{b_j}{\mu_j}\,y^*(\beta^j)+\hat y,\qquad \hat y=\frac{2\sqrt m}{K}\sum_{k=1}^K y^*(u^k)\quad\text{(48)}.$$
--
--   **The $k$-uncertain model (60)–(63).** With $k$ uncertain right-hand sides $b\in\mathcal U\subseteq\mathbb R^k$ and $l=m-k$ fixed ones $b^0\in\mathbb R^l$: $(x,y)$ is feasible if $x\ge0$ and, for each $b\in\mathcal U$, $y(b)\ge0$, $A_1x+B_1y(b)\ge b$ and $A_2x+B_2y(b)\ge b^0$. $z^k_{Adapt}(\mathcal U)$ and $z^k_{Aff}(\mathcal U)$ are the corresponding worst-case cost infima, and $z(\Pi_2)=\min\{c^Tx+d^Ty : A_2x+B_2y\ge b^0,\ x,y\ge0\}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The declarations `Feasible`, `CostLE`, `zAdapt`, `affinePolicy`, `zAff`, `IsOptimalAdapt` and `IsOptimalAff` live in `AffinePolicies.Simplex` (module `Definitions.Def_AffinePolicies_Simplex_Setting`), shared by every mission of the series; this file defines Algorithm $\mathcal A$, the policy of (48) and the $k$-uncertain model on top of them. Vectors are `Fin m → ℝ` with the componentwise order, and indices are 0-based. The optimal values are infima of epigraph sets of reals; by Lean's convention `sInf ∅ = 0`, so they equal $0$ (a junk value) when no feasible solution has a finite worst-case cost; the theorems rule this case out by their hypotheses or conclusions. The algorithm state after $k$ iterations is computed by recursion from the choice sequence `u` (`u 0` is unused, $u^k$ is `u k`); step 2(d) is read as $J_1^k=\{j\in J_1^{k-1}: b^k_j<\mu_j\}$. In $\hat y$, Lean's division by $K=0$ gives $0$, which is the paper's empty sum. The paper's $A_2\in\mathbb R^{(m-k)\times n_2}$ is a misprint for $(m-k)\times n_1$.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, (1) PDF p. 2; (38) PDF p. 26; Fig. 1 (Algorithm A) PDF p. 29; (48) PDF p. 30; (60)–(63) and (Π₁), (Π₂) PDF pp. 32–33

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

namespace AffinePolicies.SqrtBound

open Matrix

section AlgorithmA

variable {m : ℕ}

/-- The scaled sum `Σ_{j ∈ J} b_j / μ_j`. -/
noncomputable def scaledSum (μ : Fin m → ℝ) (J : Finset (Fin m)) (b : Fin m → ℝ) : ℝ :=
  ∑ j ∈ J, b j / μ j

/-- The state `(bᵏ, J₁ᵏ)` of Algorithm 𝒜 (Fig. 1) after `k` iterations with the choices
`u 1, …, u k` (steps 1, 2(c), 2(d)); `u 0` is never used. Step 2(d) is read as
`J₁ᵏ = {j ∈ J₁^{k−1} : b_jᵏ < μ_j}`. -/
noncomputable def algState (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) :
    ℕ → (Fin m → ℝ) × Finset (Fin m)
  | 0 => (0, Finset.univ)
  | k + 1 =>
    let s := algState μ u k
    let b' : Fin m → ℝ := fun j => if j ∈ s.2 then s.1 j + u (k + 1) j else s.1 j
    (b', s.2.filter (fun j => b' j < μ j))

/-- The vector `bᵏ` of Algorithm 𝒜 after `k` iterations. -/
noncomputable def bvec (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) : Fin m → ℝ :=
  (algState μ u k).1

/-- The index set `J₁ᵏ` of Algorithm 𝒜 after `k` iterations (`J₂ᵏ` is its complement). -/
noncomputable def J1 (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) : Finset (Fin m) :=
  (algState μ u k).2

/-- The test of the while loop (step 2): some `b ∈ U` has `Σ_{j ∈ J} b_j / μ_j > √m`. -/
def LoopCond (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (J : Finset (Fin m)) : Prop :=
  ∃ b ∈ U, Real.sqrt m < scaledSum μ J b

/-- Iteration `k + 1` of Algorithm 𝒜 is executed with choice `u (k + 1)`: the loop test holds
for `J₁ᵏ`, and `u (k + 1)` maximizes `Σ_{j ∈ J₁ᵏ} b_j / μ_j` over `b ∈ U` (steps 2, 2(b)). -/
def IsIteration (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) : Prop :=
  LoopCond U μ (J1 μ u k) ∧ u (k + 1) ∈ U ∧
    ∀ b ∈ U, scaledSum μ (J1 μ u k) b ≤ scaledSum μ (J1 μ u k) (u (k + 1))

/-- A complete run of Algorithm 𝒜 with exactly `K` iterations (steps 2 and 3): iterations
`1, …, K` are executed and the loop test fails for `J₁ᴷ`. -/
def IsRun (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (K : ℕ) (u : ℕ → Fin m → ℝ) : Prop :=
  (∀ k < K, IsIteration U μ u k) ∧ ¬ LoopCond U μ (J1 μ u K)

/-- The output `β = u¹ + ⋯ + u^K` of Algorithm 𝒜 (step 4). -/
def betaSum (u : ℕ → Fin m → ℝ) (K : ℕ) : Fin m → ℝ :=
  ∑ k ∈ Finset.Icc 1 K, u k

end AlgorithmA

section Construction

variable {m n₂ : ℕ}

/-- The linear part of the affine policy of the proof of Theorem 4: column `j` is
`y*(βʲ) / μ_j` for `j ∈ J` and `0` otherwise, so `P b = Σ_{j ∈ J} (b_j / μ_j) y*(βʲ)`. -/
noncomputable def thmPolicyP (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (bstar : Fin m → Fin m → ℝ)
    (μ : Fin m → ℝ) (J : Finset (Fin m)) : Matrix (Fin n₂) (Fin m) ℝ :=
  Matrix.of fun i j => if j ∈ J then ys (bstar j) i / μ j else 0

/-- The constant part `ŷ = (2√m / K) Σ_{k=1}^{K} y*(uᵏ)` of the affine policy of the proof of
Theorem 4, display (48) (it is `0` when `K = 0`, the empty sum). -/
noncomputable def thmPolicyq (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (u : ℕ → Fin m → ℝ) (K : ℕ) :
    Fin n₂ → ℝ :=
  (2 * Real.sqrt m / K) • ∑ k ∈ Finset.Icc 1 K, ys (u k)

end Construction

section KModel

variable {k l n₁ n₂ : ℕ}

/-- `(x, y)` is feasible for `Π^k_Adapt(U)`, displays (60)–(63): `k` uncertain right-hand sides
`b ∈ U ⊆ ℝ^k` and `l` (the paper's `m − k`) fixed right-hand sides `b⁰ ∈ ℝ^l`; `x ≥ 0` and, for
every `b ∈ U`, `y(b) ≥ 0`, `A₁ x + B₁ y(b) ≥ b` and `A₂ x + B₂ y(b) ≥ b⁰`. -/
def FeasibleK (A₁ : Matrix (Fin k) (Fin n₁) ℝ) (A₂ : Matrix (Fin l) (Fin n₁) ℝ)
    (B₁ : Matrix (Fin k) (Fin n₂) ℝ) (B₂ : Matrix (Fin l) (Fin n₂) ℝ) (b0 : Fin l → ℝ)
    (U : Set (Fin k → ℝ)) (x : Fin n₁ → ℝ) (y : (Fin k → ℝ) → Fin n₂ → ℝ) : Prop :=
  0 ≤ x ∧ ∀ b ∈ U, 0 ≤ y b ∧ b ≤ A₁ *ᵥ x + B₁ *ᵥ y b ∧ b0 ≤ A₂ *ᵥ x + B₂ *ᵥ y b

/-- `z^k_Adapt(U)`, display (60), as an epigraph infimum. -/
noncomputable def zAdaptK (A₁ : Matrix (Fin k) (Fin n₁) ℝ) (A₂ : Matrix (Fin l) (Fin n₁) ℝ)
    (B₁ : Matrix (Fin k) (Fin n₂) ℝ) (B₂ : Matrix (Fin l) (Fin n₂) ℝ) (b0 : Fin l → ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin k → ℝ)) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin k → ℝ) → Fin n₂ → ℝ),
    FeasibleK A₁ A₂ B₁ B₂ b0 U x y ∧ AffinePolicies.Simplex.CostLE c d U x y t}

/-- `z^k_Aff(U)`: the epigraph infimum of `Π^k_Adapt(U)` over affine policies `b ↦ P b + q`. -/
noncomputable def zAffK (A₁ : Matrix (Fin k) (Fin n₁) ℝ) (A₂ : Matrix (Fin l) (Fin n₁) ℝ)
    (B₁ : Matrix (Fin k) (Fin n₂) ℝ) (B₂ : Matrix (Fin l) (Fin n₂) ℝ) (b0 : Fin l → ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin k → ℝ)) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin k) ℝ) (q : Fin n₂ → ℝ),
    FeasibleK A₁ A₂ B₁ B₂ b0 U x (AffinePolicies.Simplex.affinePolicy P q) ∧ AffinePolicies.Simplex.CostLE c d U x (AffinePolicies.Simplex.affinePolicy P q) t}

/-- `z(Π₂)`: the optimal value of the deterministic problem
`min cᵀx + dᵀy s.t. A₂ x + B₂ y ≥ b⁰, x, y ≥ 0` (PDF p. 33). -/
noncomputable def zDet (A₂ : Matrix (Fin l) (Fin n₁) ℝ) (B₂ : Matrix (Fin l) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (b0 : Fin l → ℝ) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ),
    0 ≤ x ∧ 0 ≤ y ∧ b0 ≤ A₂ *ᵥ x + B₂ *ᵥ y ∧ c ⬝ᵥ x + d ⬝ᵥ y ≤ t}

end KModel

end AffinePolicies.SqrtBound


