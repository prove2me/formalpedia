-- Prove2me | Definitions.Def_CascadeCC_Model
-- name    : CascadeCC_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:09.159468+00:00
-- url     : https://prove2.me/theorems/6622f230-737a-4ece-bf0c-ce982aec60b6
-- title:
--   The Cascade Click model, DET, stationary optimality, and the value of a rate policy
-- statement:
--   An instance has $J$ products in a fixed order, an arrival probability $\lambda\in[0,1]$, continuation probabilities $\zeta_j\in(0,1]$, and a rate bound $u\in(0,1]$. In each period at most one customer arrives. She examines the products from the first on: at product $j$ she buys with the conditional purchase rate $\alpha_j$, and otherwise continues to product $j+1$ with probability $\zeta_j$.
--
--   For each product, $p_j$ is the inverse of the rate function: strictly decreasing on $(0,u]$ with $p_j(u)=0$, the lowest price. The conditional revenue rate is $r_j(\alpha)=\alpha p_j(\alpha)$. Assumption A3 is part of the instance: $r_j$ is strictly concave on $(0,u]$ with a maximizer $\alpha_j^{\max}\in(0,u)$, and it has derivatives $r_j',r_j''$ with $|r_j''|\le w$.
--
--   Under rates $a\in[0,u]^J$, the arrival rate at product $j$ and its expected purchase rate are
--
--   $$
--   \sigma_j(a)=\lambda\prod_{i<j}(1-a_i)\zeta_i,\qquad v_j(a)=\sigma_j(a)a_j .
--   $$
--
--   **DET.** A schedule $\alpha=(\alpha_t)_{t\le N}$ is feasible for inventory $Y$ if all its rates lie in $[0,u]$ and $\sum_t\sigma_j(\alpha_t)\alpha_{tj}\le Y_j$ for every $j$. Its objective is $\sum_t\sum_j\sigma_j(\alpha_t)r_j(\alpha_{tj})$, and $V^D$ is the supremum of the objective over feasible schedules. The rates $a$ are a **stationary optimal solution** for $(T,y)$ if $a\in[0,u]^J$, $T v_j(a)\le y_j$, and every feasible schedule has objective at most $T\tilde V(a)$, where $\tilde V(a)=\sum_j\sigma_j(a)r_j(a_j)$.
--
--   **The stochastic system.** A period's outcome is a sold product $j$, with probability $v_j(a)$, or no sale, with the remaining probability. A rate policy maps past outcomes to rates; its value $V^\pi$ is the expected sum of the prices paid, under the path law of the policy.
--
--   This module holds the common language of the mission: the benchmark of the goal is DET, and its policies are rate policies.
--
--   **Formalization Note** The action is the rate. Rate $0$ is the turn-off price $\bar p_j$: `r j 0 = 0` by construction, and a period's revenue at rate $0$ has probability $0$. Concavity is on $(0,u]$, the printed form for $\Omega_\alpha=(0,u]$ and the weaker one for $[0,u]$. The twice differentiability of $\alpha_j$ in A1, and A2, are not fields; nonnegativity of $p_j$ on $(0,u]$ follows from the two fields on $p_j$. Products and periods are 0-based. The printed recursion on pp.10 and 14 has an index slip; the product formula is the form of pp.20 and 24. `detValue` is a real `sSup`, and the feasible set is nonempty and the objective bounded above on it when $Y\ge0$ (proved in the verification file).
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, §3, pp.9–12 (Assumptions A1–A3, p.12); Figure 1, p.10; (1a), p.11; DET (11), p.17; S^D(y), p.18; (13), p.20; p.21

import Mathlib
import Definitions.Def_CascadeCC_PathLaw

namespace CascadeCC

/-- The Cascade Click model with `J` products in a fixed order (Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, §3, pp.9–12, Assumptions A1–A3,
p.12).

Fields: the arrival probability `lam` = λ ∈ [0, 1] (p.9); the continuation probabilities
`zeta j` = ζ_j ∈ (0, 1] (p.10); the rate bound `u` ∈ (0, 1] (p.11); the inverse `price j` = p_j of the
conditional purchase rate function, strictly decreasing on (0, u] with p_j(u) = 0, that is α_j(0) = u
(p.12, A1); and the data of A3 for r_j(α) = α p_j(α): strict concavity on (0, u], a maximizer
`alphaMax j` in (0, u), derivatives `r' j`, `r'' j` and a bound `w` on |r''|.

**Formalization Note** The action is the rate, not the price (A1 makes them equivalent; §4.2, p.14, does
the same). The field `price j 0` is never used with positive probability or weight: rate 0 is the
turn-off p̄_j, with revenue `r j 0 = 0`. Concavity is stated on (0, u], which covers Ω_α = (0, u] as
printed and is the weaker hypothesis for Ω_α = [0, u]. Nonnegativity of `price` on (0, u] follows from
`price_anti` and `price_u`. The twice differentiability of α_j in A1, and A2, are not fields: they
concern the price parametrization, which the rate formulation does not use. Derivatives are one-sided
at `u`. -/
structure Instance (J : ℕ) where
  /-- The arrival probability λ. -/
  lam : ℝ
  lam_mem : lam ∈ Set.Icc (0 : ℝ) 1
  /-- The continuation probability ζ_j. -/
  zeta : Fin J → ℝ
  zeta_mem : ∀ j, zeta j ∈ Set.Ioc (0 : ℝ) 1
  /-- The largest conditional purchase rate. -/
  u : ℝ
  u_mem : u ∈ Set.Ioc (0 : ℝ) 1
  /-- The price p_j(α) of product `j` at conditional purchase rate α. -/
  price : Fin J → ℝ → ℝ
  price_anti : ∀ j, StrictAntiOn (price j) (Set.Ioc 0 u)
  price_u : ∀ j, price j u = 0
  concave : ∀ j, StrictConcaveOn ℝ (Set.Ioc 0 u) (fun x => x * price j x)
  /-- The unconstrained maximizer α_j^max of A3. -/
  alphaMax : Fin J → ℝ
  alphaMax_mem : ∀ j, alphaMax j ∈ Set.Ioo 0 u
  alphaMax_le : ∀ j, ∀ x ∈ Set.Ioc 0 u, x * price j x ≤ alphaMax j * price j (alphaMax j)
  /-- The first derivative of r_j. -/
  r' : Fin J → ℝ → ℝ
  /-- The second derivative of r_j. -/
  r'' : Fin J → ℝ → ℝ
  /-- The bound on |r_j''| (called ω on pp.ec12–13). -/
  w : ℝ
  hasDeriv_r : ∀ j, ∀ x ∈ Set.Ioc 0 u,
    HasDerivWithinAt (fun x => x * price j x) (r' j x) (Set.Ioc 0 u) x
  hasDeriv_r' : ∀ j, ∀ x ∈ Set.Ioc 0 u, HasDerivWithinAt (r' j) (r'' j x) (Set.Ioc 0 u) x
  r''_le : ∀ j, ∀ x ∈ Set.Ioc 0 u, |r'' j x| ≤ w

variable {J : ℕ}

/-- The conditional revenue rate r_j(α) = α p_j(α) (SSRN abstract_id=3362921, p.11 and A3, p.12). By
construction `M.r j 0 = 0`, the revenue of the turn-off. -/
def Instance.r (M : Instance J) (j : Fin J) (x : ℝ) : ℝ := x * M.price j x

/-- The arrival rate σ_j(a) = λ ∏_{i<j} (1 − a_i) ζ_i at product `j` under conditional purchase rates
`a`, the solution of σ_1 = λ, σ_{j+1} = σ_j (1 − a_j) ζ_j (SSRN abstract_id=3362921, Figure 1, p.10,
pp.20, 24, (EC.19)).

**Formalization Note** The recursion printed on pp.10 and 14 has an index slip, (1 − a_j) for
(1 − a_{j−1}) at σ_j; this is the corrected form, the one the paper's analysis uses. Products are
0-based. -/
noncomputable def arrival (M : Instance J) (a : Fin J → ℝ) (j : Fin J) : ℝ :=
  M.lam * ∏ i ∈ Finset.univ.filter (fun i : Fin J => i < j), ((1 - a i) * M.zeta i)

/-- The expected purchase rate σ_j(a) a_j of product `j` (SSRN abstract_id=3362921, p.10). -/
noncomputable def purchase (M : Instance J) (a : Fin J → ℝ) (j : Fin J) : ℝ :=
  arrival M a j * a j

/-- The one-period objective ∑_j σ_j(a) r_j(a_j) of (13a) (SSRN abstract_id=3362921, p.20). -/
noncomputable def statObjective (M : Instance J) (a : Fin J → ℝ) : ℝ :=
  ∑ j, arrival M a j * M.r j (a j)

/-- Feasibility in DET (11), in rates, for `N` periods and inventory `Y`: all rates lie in [0, u] and
∑_t σ_j(α_t) α_tj ≤ Y_j (SSRN abstract_id=3362921, (11), p.17; (EC.19), p.ec4).

**Formalization Note** Rate 0 is the turn-off, which the paper includes through S^D(y), pp.14, 18. Periods
are 0-based. -/
def Feasible (M : Instance J) (N : ℕ) (Y : Fin J → ℝ) (α : Fin N → Fin J → ℝ) : Prop :=
  (∀ t j, α t j ∈ Set.Icc 0 M.u) ∧ ∀ j, ∑ t, purchase M (α t) j ≤ Y j

/-- The objective of DET: ∑_t ∑_j σ_j(α_t) r_j(α_tj) (SSRN abstract_id=3362921, (11), p.17). -/
noncomputable def detObjective (M : Instance J) (N : ℕ) (α : Fin N → Fin J → ℝ) : ℝ :=
  ∑ t, ∑ j, arrival M (α t) j * M.r j (α t j)

/-- The value V^D of DET for `N` periods and inventory `Y` (SSRN abstract_id=3362921, (11), p.17).

**Formalization Note** It is a real `sSup`; the feasible set contains α = 0 for Y ≥ 0 and the objective is
bounded above on it, so this is a true supremum (`Solutions/verification/CascadeCC_Bounds.lean`). The
paper's `max` is attained only under an extra condition: see `lemma_4_stationary_optimum`. -/
noncomputable def detValue (M : Instance J) (N : ℕ) (Y : Fin J → ℝ) : ℝ :=
  sSup (detObjective M N '' {α | Feasible M N Y α})

/-- `a` is a stationary optimal solution of DET for horizon `T` and inventory `y`, the paper's a^D
(SSRN abstract_id=3362921, Lemma 4, p.20, (13), p.20, and p.21): rates in [0, u], the constant schedule is
feasible, T σ_j(a) a_j ≤ y_j (13b), and it is at least as good as every feasible schedule. -/
def IsStationaryOptimal (M : Instance J) (T : ℕ) (y : Fin J → ℝ) (a : Fin J → ℝ) : Prop :=
  (∀ j, a j ∈ Set.Icc 0 M.u) ∧ (∀ j, (T : ℝ) * purchase M a j ≤ y j) ∧
    ∀ α : Fin T → Fin J → ℝ, Feasible M T y α → detObjective M T α ≤ (T : ℝ) * statObjective M a

/-- The law of one period's outcome under rates `a`: `some j` means product `j` is sold, with probability
σ_j(a) a_j, and `none` means no sale (no arrival, abandonment, or no purchase)
(SSRN abstract_id=3362921, §3, p.11: D_tj ∈ {0, 1}, at most one sale, E[D_tj | F_t] = σ_j α_j). -/
noncomputable def outcomeProb (M : Instance J) (a : Fin J → ℝ) : Option (Fin J) → ℝ
  | some j => purchase M a j
  | none => 1 - ∑ j, purchase M a j

/-- The revenue of one period: the price paid if a product is sold, the term p_tj D_tj of (1a)
(SSRN abstract_id=3362921, p.11). -/
noncomputable def periodRevenue (M : Instance J) (a : Fin J → ℝ) : Option (Fin J) → ℝ
  | some j => M.price j (a j)
  | none => 0

/-- A rate policy maps the outcomes so far, oldest first, to the conditional purchase rates of the
period, so it is non-anticipating by construction (SSRN abstract_id=3362921, p.11). -/
abbrev RatePolicy (J : ℕ) := List (Option (Fin J)) → Fin J → ℝ

/-- The probability of a path of `N` outcomes under a rate policy. -/
noncomputable def pathProb (M : Instance J) (N : ℕ) (π : RatePolicy J)
    (ω : Fin N → Option (Fin J)) : ℝ :=
  pathMass (outcomeProb M) π ω

/-- The expected total revenue V^π of a rate policy over `N` periods, E[∑_t ∑_j p_tj D_tj], (1a)
(SSRN abstract_id=3362921, pp.11, 22).

**Formalization Note** The expectation is the finite sum over the paths of outcomes. -/
noncomputable def policyValue (M : Instance J) (N : ℕ) (π : RatePolicy J) : ℝ :=
  ∑ ω : Fin N → Option (Fin J),
    pathProb M N π ω * ∑ t : Fin N, periodRevenue M (π (pathPrefix ω t)) (ω t)

end CascadeCC


