-- Prove2me | Definitions.Def_PooledRationing_AsymFeas_Setting
-- name    : PooledRationing_AsymFeas_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:57.864416+00:00
-- url     : https://prove2.me/theorems/56412e79-c44b-4710-9f9e-afcba682d6c5
-- title:
--   §1.1–§2, pp. 3–13 — policies, finite mixtures, service level (9), feasibility (11a), Definition 1, Obj(11), (14), (16), (18)
-- statement:
--   This file fixes the common model of the paper's single-period capacity rationing problem (§1.1 and §2) at a given capacity level.
--
--   A firm serves $n$ customers $j\in\mathcal N$ from $m$ resources $i\in\mathcal M$. The demand vector $\tilde{\mathbf D}=(\tilde D_1,\dots,\tilde D_n)$ has a joint law $F$. For a capacity vector $\mathbf c$ and a realized demand $\mathbf D$, $P(\mathbf c,\mathbf D)$ is the set of feasible pairs $(\mathbf s,\mathbf y)$, where $s_j$ is the fulfilled demand of customer $j$ and $y_{ij}$ is the amount of resource $i$ allocated to customer $j$. The allocation cost $f(\mathbf y)$ is linear, $R_j(s_j,D_j)$ is the service measure of customer $j$, and $\beta_j$ is its target service level.
--
--   1. A **deterministic policy** $\phi$ assigns to every demand $\mathbf D$ a feasible decision $\phi(\mathbf c,\mathbf D)=(\mathbf s(\phi,\mathbf c,\mathbf D),\mathbf y(\phi,\mathbf c,\mathbf D))\in P(\mathbf c,\mathbf D)$, measurably in $\mathbf D$.
--   2. A **randomized policy** $\lambda$ is a finite probability mixture: weights $\lambda_1,\dots,\lambda_k\ge0$ with $\sum_i\lambda_i=1$ on deterministic policies $\phi_1,\dots,\phi_k$.
--   3. The **service level** (9) and the **expected allocation cost** of $\lambda$ are
--   $$
--   S_j(\lambda)=\sum_{i}\lambda_i\,\mathbb E_{\tilde{\mathbf D}}\big[R_j(s_j(\phi_i,\mathbf c,\tilde{\mathbf D}),\tilde D_j)\big],\qquad
--   C(\lambda)=\sum_{i}\lambda_i\,\mathbb E_{\tilde{\mathbf D}}\big[f(\mathbf y(\phi_i,\mathbf c,\tilde{\mathbf D}))\big].
--   $$
--   4. The capacity $\mathbf c$ is **feasible**, constraint (11a), if some $\lambda$ has $S_j(\lambda)\ge\beta_j$ for every $j$. It is **asymptotically feasible** (Definition 1, (8)) if for every $\epsilon>0$ some $\lambda_\epsilon$ has $S_j(\lambda_\epsilon)\ge\beta_j-\epsilon$ for every $j$.
--   5. $\mathrm{Obj}(11)$ is the value of the semi-infinite program (11): the infimum of $C(\lambda)$ over all $\lambda$ satisfying (11a).
--   6. For weights $\mathbf w$ and a demand $\mathbf D$, the **maximum weighted service** of (18) and the **Max-Weighted-Service value** $g$ of (16) are
--   $$
--   M(\mathbf w;\mathbf D)=\max_{(\mathbf s,\mathbf y)\in P(\mathbf c,\mathbf D)}\sum_{j}w_jR_j(s_j,D_j),\qquad
--   g(\mathbf w,\mathbf c;\mathbf D)=\min_{(\mathbf s,\mathbf y)\in P(\mathbf c,\mathbf D)} f(\mathbf y)-\sum_{j}w_jR_j(s_j,D_j).
--   $$
--   7. The **dual functional** (14) of a deterministic policy is
--   $$
--   F(\mathbf w,\phi)=\mathbb E_{\tilde{\mathbf D}}\big[f(\mathbf y(\phi,\mathbf c,\tilde{\mathbf D}))\big]-\sum_j w_j\,\mathbb E_{\tilde{\mathbf D}}\big[R_j(s_j(\phi,\mathbf c,\tilde{\mathbf D}),\tilde D_j)\big].
--   $$
--
--   These are the objects in which both main results of the paper, the feasibility criterion (Theorem 1) and the asymptotic optimality of the Max-Weighted-Service policy (Theorem 3), are stated.
--
--   **Formalization Note** Customers and resources are indexed by `Fin n` and `Fin m`, from $0$. A decision is the pair $(\mathbf s,\mathbf y)$ in this order (the paper also writes $(\mathbf y,\mathbf s)$), with `y i j` the allocation of resource $i$ to customer $j$. The feasible-set map $P$ is an arbitrary set-valued map, of which (1)–(4) are instances; its properties (Assumption 1b) are theorem hypotheses. Policies are defined only at the fixed capacity $\mathbf c$ of each theorem, are required to be measurable (so that the expectations make sense, which the paper leaves implicit), and must be feasible at every $\mathbf D\in\mathbb R^n$, so the theorems supply nonempty feasible sets. The paper's probability measure $\lambda$ on the set $\Phi$ of deterministic policies is replaced by a finite mixture: every quantity here depends on $\lambda$ only through finitely many expectations, and the mean of a probability measure on a set in $\mathbb R^{n+1}$ lies in its convex hull, so finite mixtures reach exactly the same values. The service measure $R_j$ is a function on $\mathbb R\times\mathbb R$; the theorems require it to be nonnegative and measurable. Expectations are Bochner integrals, which are $0$ for non-integrable integrands, and the maximum, minimum and infimum are real `sSup`/`sInf`, which are $0$ on empty or unbounded sets; every theorem using them carries the integrability, nonemptiness and boundedness hypotheses that make them the paper's values.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), pp. 3–6, 10–13, (1)–(6), Definition 1 and (8), (9)–(11), (14), (16), (18)

import Mathlib

namespace PooledRationing.AsymFeas

open MeasureTheory

/-- A fulfilment vector and a resource-to-customer allocation. -/
abbrev Sol (n m : ℕ) := (Fin n → ℝ) × (Fin m → Fin n → ℝ)

/-- A measurable feasible decision at every realized demand, for a fixed capacity. -/
structure DetPolicy {n m : ℕ}
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ) where
  toFun : (Fin n → ℝ) → Sol n m
  measurable' : Measurable toFun
  mem' : ∀ D, toFun D ∈ P c D

/-- A randomized policy represented by a finite probability mixture. -/
structure RandPolicy {n m : ℕ}
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ) where
  k : ℕ
  wt : Fin k → ℝ
  pol : Fin k → DetPolicy P c
  wt_nonneg : ∀ i, 0 ≤ wt i
  wt_sum : ∑ i, wt i = 1

/-- Expected service of customer `j` under a deterministic policy. -/
noncomputable def detService {n m : ℕ} (F : Measure (Fin n → ℝ))
    (R : Fin n → ℝ → ℝ → ℝ) {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)}
    {c : Fin m → ℝ} (φ : DetPolicy P c) (j : Fin n) : ℝ :=
  ∫ D, R j ((φ.toFun D).1 j) (D j) ∂F

/-- Expected allocation cost under a deterministic policy. -/
noncomputable def detCost {n m : ℕ} (F : Measure (Fin n → ℝ))
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)}
    {c : Fin m → ℝ} (φ : DetPolicy P c) : ℝ :=
  ∫ D, f (φ.toFun D).2 ∂F

/-- Expected service under a finite randomization. -/
noncomputable def service {n m : ℕ} (F : Measure (Fin n → ℝ))
    (R : Fin n → ℝ → ℝ → ℝ) {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)}
    {c : Fin m → ℝ} (lam : RandPolicy P c) (j : Fin n) : ℝ :=
  ∑ i, lam.wt i * detService F R (lam.pol i) j

/-- Expected allocation cost under a finite randomization. -/
noncomputable def cost {n m : ℕ} (F : Measure (Fin n → ℝ))
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)}
    {c : Fin m → ℝ} (lam : RandPolicy P c) : ℝ :=
  ∑ i, lam.wt i * detCost F f (lam.pol i)

/-- Feasibility of all individual service targets, equation (11a). -/
def IsFeasible {n m : ℕ} (F : Measure (Fin n → ℝ))
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ) : Prop :=
  ∃ lam : RandPolicy P c, ∀ j, β j ≤ service F R lam j

/-- Asymptotic feasibility, Definition 1 and equation (8). -/
def IsAsymFeasible {n m : ℕ} (F : Measure (Fin n → ℝ))
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ lam : RandPolicy P c, ∀ j, β j - ε ≤ service F R lam j

/-- The value of the constrained allocation-cost problem (11). -/
noncomputable def obj11 {n m : ℕ} (F : Measure (Fin n → ℝ))
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ) : ℝ :=
  sInf {v | ∃ lam : RandPolicy P c,
    (∀ j, β j ≤ service F R lam j) ∧ cost F f lam = v}

/-- Weighted realized service at one feasible decision. -/
def weightedService {n m : ℕ} (R : Fin n → ℝ → ℝ → ℝ)
    (w D : Fin n → ℝ) (x : Sol n m) : ℝ :=
  ∑ j, w j * R j (x.1 j) (D j)

/-- The maximum weighted service of equation (18). -/
noncomputable def maxWeightedValue {n m : ℕ}
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m))
    (c : Fin m → ℝ) (R : Fin n → ℝ → ℝ → ℝ)
    (w D : Fin n → ℝ) : ℝ :=
  sSup (weightedService R w D '' P c D)

/-- The deterministic objective in equation (16). -/
def mwsObjective {n m : ℕ} (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (w D : Fin n → ℝ) (x : Sol n m) : ℝ :=
  f x.2 - ∑ j, w j * R j (x.1 j) (D j)

/-- The minimum value in equation (16). -/
noncomputable def g {n m : ℕ}
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m))
    (c : Fin m → ℝ) (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (w D : Fin n → ℝ) : ℝ :=
  sInf (mwsObjective f R w D '' P c D)

/-- The deterministic dual functional in equation (14). -/
noncomputable def Fdual {n m : ℕ} (F : Measure (Fin n → ℝ))
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (w : Fin n → ℝ)
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)}
    {c : Fin m → ℝ} (φ : DetPolicy P c) : ℝ :=
  detCost F f φ - ∑ j, w j * detService F R φ j

end PooledRationing.AsymFeas


