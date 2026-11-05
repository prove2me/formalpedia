-- Prove2me | Definitions.Def_RailwayRM_Model
-- name    : RailwayRM_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:37.864456+00:00
-- url     : https://prove2.me/theorems/6e2c8af2-5df6-40ad-a8d8-7998357fbe2f
-- title:
--   The railway pricing and capacity model: instances, paths, policies, $P_S$, $P_D$ and the $\kappa$-scaling
-- statement:
--   A railway sells tickets for travel on one day over a sales horizon of $T$ periods. There are $L$ legs, $M$ trains and $N$ itineraries; $\bar S_n$ is the set of legs of itinerary $n$, and $S_\ell$ the set of itineraries using leg $\ell$. A coach has $k$ seats and costs $c_o$. A standing passenger costs $c_s$ on each leg. Train $m$ uses at most $\bar b_m$ coaches and at least $\underline b_m$ unreserved coaches.
--
--   **Demand.** For each itinerary $n$, $\Lambda_n$ is a convex set of rate vectors $(\vec x_n,y_n)$ with nonnegative entries, containing $0$, and $\vec\zeta_n$ is the price map. The revenue rate is $r_n(\vec x_n,y_n)=(\vec x_n,y_n)\cdot\vec\zeta_n(\vec x_n,y_n)$, and $r=\sum_n r_n$ is jointly concave on $\prod_n\Lambda_n$. Rates of all itineraries sum to at most $1$. A buyer of an unreserved ticket for $n$ travels on train $m$ with probability $\delta_{n,m}$, where $\sum_m\delta_{n,m}=1$.
--
--   **Paths.** In each period exactly one outcome occurs: nothing, a reserved sale $(n,m)$ with probability $x_{n,m}$, or an unreserved sale $(n,m)$ with probability $\delta_{n,m}y_n$. A full path lists one outcome per period. The observed path erases the train of unreserved sales, which is known only on the day of travel. $\bar X_{\ell,m}[1,t]$ counts reserved tickets through period $t$ using leg $\ell$ of train $m$, and $\bar Y_{\ell,m}[1,T]$ counts unreserved tickets using leg $\ell$ whose buyer travels on train $m$.
--
--   **The problem $P_S$.** A policy chooses the rates of period $t$ from the observed outcomes before $t$, and the final coaches $b_{u,m}\in\mathbb N$ from the whole observed path. Its expected profit is
--   $$\mathbb E\Big[\sum_{t=1}^T\sum_{n=1}^N r_n(\vec x_n(t),y_n(t))-\sum_{m=1}^M c_o\Big\lceil\frac{\max_\ell\bar X_{\ell,m}[1,T]}{k}\Big\rceil-\sum_{m=1}^M c_ob_{u,m}-\sum_{m=1}^M\sum_{\ell=1}^L c_s\big[\bar Y_{\ell,m}[1,T]-b_{u,m}k\big]^+\Big].$$
--   It is feasible when $\bar X_{\ell,m}[1,T]+b_{u,m}k\le\bar b_mk$ and $b_{u,m}\ge\underline b_m$ on every path of positive probability. $J_S$ is the supremum of the profits of feasible policies.
--
--   **The problem $P_D$.** It maximizes
--   $$\sum_n r_n(\vec x_n,y_n)T-\sum_m\frac{c_oT}{k}\max_\ell\bar x_{\ell,m}-\sum_m c_ob_{u,m}-\sum_m\sum_\ell c_s(\bar y_{\ell,m}T-b_{u,m}k)^+$$
--   over $(\vec x_n,y_n)\in\Lambda_n$ and real $b_{u,m}\ge\max(\underline b_m,0)$ with $\bar x_{\ell,m}T+b_{u,m}k\le\bar b_mk$, where $\bar x_{\ell,m}=\sum_{n\in S_\ell}x_{n,m}$ and $\bar y_{\ell,m}=\sum_{n\in S_\ell}\delta_{n,m}y_n$.
--
--   **Scaling.** The $\kappa$-scaled instance has $T\mapsto\kappa T$, $\bar b_m\mapsto\kappa\bar b_m$, $\underline b_m\mapsto\kappa\underline b_m$ and all other data unchanged.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Rates are the decision variables, so the demand map is not a field and a price is recovered by $\vec\zeta_n$. Trains, legs and itineraries are indexed by `Fin`. Expectations are finite sums over paths. The ceiling is the usual one, not footnote 2's $\lfloor x\rfloor+1$. The incidence is arbitrary, and boundedness and differentiability of $r$ are not required, so every instance of the paper is an instance here. Period $t$ of the paper is the index $t-1$ of `Fin T`.
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), §2, pp. 10–15 (conditions 1–4 p. 11; (P_S) p. 13; (1)–(2) p. 14; (P_D) p. 15), and the scaling of p. 17

import Mathlib

open Finset

namespace RailwayRM

/-!
The railway model of Manchiraju, Dawande, Janakiraman and Raghunathan, *Dynamic Pricing and
Capacity Optimization in Railways*, SSRN 4112672 (2023-08-22), §2, pp. 10–15: the instance data,
the outcome paths, the policies, the stochastic problem `P_S`, the deterministic problem `P_D`, and
the `κ`-scaling of p. 17.
-/

/-- A rate vector `(x⃗_n, y_n)` of one itinerary: the reserved demand rates on the `M` trains and
the unreserved demand rate (SSRN 4112672, 2023-08-22, §2.1, p. 11). -/
abbrev Rate (M : ℕ) := (Fin M → ℝ) × ℝ

/-- A rate vector for all `N` itineraries. -/
abbrev Rates (M N : ℕ) := Fin N → Rate M

/-- The revenue rate `r_n(x⃗_n, y_n) = (x⃗_n, y_n) · ζ⃗_n(x⃗_n, y_n)` of regularity condition 4
(SSRN 4112672, 2023-08-22, §2.1, p. 11), for a price map `price = ζ⃗_n`. -/
noncomputable def revRate {M : ℕ} (price : Rate M → Rate M) (v : Rate M) : ℝ :=
  ∑ m, v.1 m * (price v).1 m + v.2 * (price v).2

/-- An instance of the railway problem (SSRN 4112672, 2023-08-22, §2, pp. 10–14), with `L` legs,
`M` trains and `N` itineraries.

* `T` periods, `k` seats per coach;
* `legs n` is `S̄_n`, the set of legs used by itinerary `n`, so `n ∈ S_ℓ` iff `ℓ ∈ legs n`;
* `δ n m` is the probability that a buyer of an unreserved ticket for `n` travels on `m` (p. 12);
* `co` is the cost of a coach and `cs` the penalty per standing passenger per leg (p. 13);
* `bMax m`, `bMin m` are `b̄_m` and `b̲_m` (p. 13);
* `Λ n` is the set `Λ^C_n` of feasible demand rates and `ζ n` the price map (conditions 1–2, p. 11).

**Formalization Note.** Rates are the decision variables, as condition 2 allows, so the demand map
`λ⃗_n` is not a field and prices are recovered by `ζ n`. Condition 3 (the null price) is the field
`zero_mem`. The revenue of the rate `0` is `0` by the definition of `revRate`, which also covers an
infinite null price. `one_customer` is "at most one customer arrives during each period" (p. 11).
The incidence `legs` is arbitrary, and boundedness and differentiability of `r` and `λ⃗_n`
(conditions 1 and 4) are not required, so every instance of the paper is an instance here. -/
structure Instance (L M N : ℕ) where
  T : ℕ
  k : ℕ
  T_pos : 1 ≤ T
  k_pos : 1 ≤ k
  legs : Fin N → Finset (Fin L)
  δ : Fin N → Fin M → ℝ
  δ_nonneg : ∀ n m, 0 ≤ δ n m
  δ_sum : ∀ n, ∑ m, δ n m = 1
  co : ℝ
  cs : ℝ
  co_nonneg : 0 ≤ co
  cs_nonneg : 0 ≤ cs
  bMax : Fin M → ℕ
  bMin : Fin M → ℕ
  bMin_le : ∀ m, bMin m ≤ bMax m
  Λ : Fin N → Set (Rate M)
  ζ : Fin N → Rate M → Rate M
  Λ_convex : ∀ n, Convex ℝ (Λ n)
  zero_mem : ∀ n, (0 : Rate M) ∈ Λ n
  rate_nonneg : ∀ n, ∀ v ∈ Λ n, (∀ m, 0 ≤ v.1 m) ∧ 0 ≤ v.2
  one_customer : ∀ v : Rates M N, (∀ n, v n ∈ Λ n) → ∑ n, (∑ m, (v n).1 m + (v n).2) ≤ 1
  concave : ConcaveOn ℝ (Set.univ.pi Λ) (fun v : Rates M N => ∑ n, revRate (ζ n) (v n))

/-- What happens in one period: nothing, a reserved sale for itinerary `n` on train `m`, or an
unreserved sale for itinerary `n` whose buyer will travel on train `m`
(SSRN 4112672, 2023-08-22, §2.1–2.2, pp. 11–12). -/
inductive Outcome (M N : ℕ) where
  | none : Outcome M N
  | res (n : Fin N) (m : Fin M) : Outcome M N
  | unres (n : Fin N) (m : Fin M) : Outcome M N
  deriving DecidableEq, Fintype

/-- What the firm sees of one period: the train of an unreserved buyer is "known only on the day of
travel" (SSRN 4112672, 2023-08-22, §2.2, pp. 12–13). -/
inductive ObsOutcome (M N : ℕ) where
  | none : ObsOutcome M N
  | res (n : Fin N) (m : Fin M) : ObsOutcome M N
  | unres (n : Fin N) : ObsOutcome M N
  deriving DecidableEq, Fintype

/-- Erase the train of an unreserved outcome. -/
def Outcome.obs {M N : ℕ} : Outcome M N → ObsOutcome M N
  | .none => .none
  | .res n m => .res n m
  | .unres n _ => .unres n

namespace Instance

variable {L M N : ℕ} (I : Instance L M N)

/-- The revenue rate `r_n` of itinerary `n` (condition 4, p. 11). -/
noncomputable def rev (n : Fin N) (v : Rate M) : ℝ := revRate (I.ζ n) v

/-- The law of one period's outcome under the rates `v`: `P(res n m) = x_{n,m}`,
`P(unres n m) = δ_{n,m} y_n` (SSRN 4112672, 2023-08-22, p. 12), and nothing happens with the
remaining probability. -/
noncomputable def outcomeProb (v : Rates M N) : Outcome M N → ℝ
  | .none => 1 - ∑ n, (∑ m, (v n).1 m + (v n).2)
  | .res n m => (v n).1 m
  | .unres n m => I.δ n m * (v n).2

/-- A full path: one outcome per period. Period `t ∈ {1, …, T}` of the paper is the index
`t - 1 : Fin T`. -/
abbrev FullPath := Fin I.T → Outcome M N

/-- An observed path: one observed outcome per period. -/
abbrev ObsPath := Fin I.T → ObsOutcome M N

/-- The observed path of a full path. -/
def observe (ω : I.FullPath) : I.ObsPath := fun t => (ω t).obs

/-- `X̄_{ℓ,m}[1,t]`: the number of reserved tickets sold in periods `1, …, t` that use leg `ℓ` of
train `m` (SSRN 4112672, 2023-08-22, §2.2, p. 12). Period `s + 1` of the paper is the index `s`, so
the periods `1, …, t` are the indices `s < t`. -/
def resCount (o : I.ObsPath) (ℓ : Fin L) (m : Fin M) (t : ℕ) : ℕ :=
  (univ.filter fun s : Fin I.T => s.val < t ∧ ∃ n, ℓ ∈ I.legs n ∧ o s = .res n m).card

/-- `Ȳ_{ℓ,m}[1,T]`: the number of unreserved tickets sold that use leg `ℓ` and whose buyer travels
on train `m` (SSRN 4112672, 2023-08-22, §2.2, pp. 12–13). It is a function of the full path. -/
def unresCount (ω : I.FullPath) (ℓ : Fin L) (m : Fin M) : ℕ :=
  (univ.filter fun s : Fin I.T => ∃ n, ℓ ∈ I.legs n ∧ ω s = .unres n m).card

/-- `b_{r,m} = ⌈max_ℓ X̄_{ℓ,m}[1,T] / k⌉`: the number of reserved coaches needed on train `m`
(SSRN 4112672, 2023-08-22, p. 12).

**Formalization Note.** `⌈·⌉` is the usual ceiling. Footnote 2, p. 12, writes `⌈x⌉ = ⌊x⌋ + 1`, which
differs at integers and contradicts the equivalence of (1) and (3), p. 14, and "the minimum number of
reserved coaches sufficient", p. 16. -/
noncomputable def reservedCoaches [NeZero L] (o : I.ObsPath) (m : Fin M) : ℕ :=
  ⌈((univ.sup' univ_nonempty fun ℓ : Fin L => I.resCount o ℓ m I.T : ℕ) : ℝ) / (I.k : ℝ)⌉₊

/-- Rate decisions: the rate vector of period `t` as a function of the observed path. -/
abbrev RatePolicy := Fin I.T → I.ObsPath → Rates M N

/-- A policy: rate decisions and the final number of unreserved coaches `b_{u,m}`, a function of the
whole observed path (SSRN 4112672, 2023-08-22, §2.3, p. 13).

**Formalization Note.** Prices are recovered by `ζ`, so a price policy and a rate policy are the same
object (condition 2, p. 11). -/
structure Policy where
  rate : I.RatePolicy
  coaches : I.ObsPath → Fin M → ℕ

variable {I}

/-- Non-anticipation (p. 13): the rates of period `t` depend only on what was observed before `t`. -/
def NonAnticipating (ρ : I.RatePolicy) : Prop :=
  ∀ (t : Fin I.T) (o o' : I.ObsPath), (∀ s, s < t → o s = o' s) → ρ t o = ρ t o'

variable (I)

/-- The probability of a full path under rate decisions `ρ`. -/
noncomputable def pathProb (ρ : I.RatePolicy) (ω : I.FullPath) : ℝ :=
  ∏ t, I.outcomeProb (ρ t (I.observe ω)) (ω t)

/-- The expectation of a function of the full path under rate decisions `ρ`, a finite sum. -/
noncomputable def expect (ρ : I.RatePolicy) (f : I.FullPath → ℝ) : ℝ :=
  ∑ ω, I.pathProb ρ ω * f ω

/-- The expected revenue `E[∑_t ∑_n r_n(x⃗^π_n(t), y^π_n(t))]`, the first term of (P_S), p. 13. The
revenue is that of the rates, as printed, including zero rates. -/
noncomputable def revenue (ρ : I.RatePolicy) : ℝ :=
  I.expect ρ fun ω => ∑ t, ∑ n, I.rev n (ρ t (I.observe ω) n)

/-- The expected cost of a policy, the last three terms of (P_S), p. 13:
`E[∑_m c_o ⌈max_ℓ X̄_{ℓ,m}[1,T]/k⌉ + ∑_m c_o b_{u,m} + ∑_m ∑_ℓ c_s [Ȳ_{ℓ,m}[1,T] - b_{u,m} k]⁺]`. -/
noncomputable def cost [NeZero L] (π : I.Policy) : ℝ :=
  I.expect π.rate fun ω =>
    ∑ m, I.co * (I.reservedCoaches (I.observe ω) m : ℝ) +
      ∑ m, I.co * (π.coaches (I.observe ω) m : ℝ) +
      ∑ m, ∑ ℓ : Fin L, I.cs *
        max ((I.unresCount ω ℓ m : ℝ) - (π.coaches (I.observe ω) m : ℝ) * (I.k : ℝ)) 0

/-- The expected profit of a policy, the objective of (P_S), p. 13. -/
noncomputable def profit [NeZero L] (π : I.Policy) : ℝ := I.revenue π.rate - I.cost π

/-- Feasibility for (P_S), pp. 13–14: `π` is non-anticipatory, its rates lie in `Λ^C_n`, and on every
path of positive probability `X̄_{ℓ,m}[1,T] + b_{u,m} k ≤ b̄_m k` (1) and `b_{u,m} ≥ b̲_m` (2).
`b_{u,m} ∈ ℕ` is the type of `coaches`.

**Formalization Note.** (2) is printed without "(a.s.)". A policy can be changed on null paths
without changing its law or its profit, so the two readings have the same set of profits. -/
def IsFeasible (π : I.Policy) : Prop :=
  NonAnticipating π.rate ∧
  (∀ t o n, π.rate t o n ∈ I.Λ n) ∧
  ∀ ω, 0 < I.pathProb π.rate ω →
    (∀ ℓ m, I.resCount (I.observe ω) ℓ m I.T + π.coaches (I.observe ω) m * I.k ≤ I.bMax m * I.k) ∧
    ∀ m, I.bMin m ≤ π.coaches (I.observe ω) m

/-- The set of expected profits of the feasible policies of (P_S). -/
def profits [NeZero L] : Set ℝ := {J | ∃ π : I.Policy, I.IsFeasible π ∧ I.profit π = J}

/-- `J_S`, the optimal value of (P_S), p. 13. The paper's "max" over `Π` is a supremum, since
attainment is not claimed anywhere. Every statement about it also carries the bound against each
feasible policy, so that a junk value of `sSup` cannot satisfy it. -/
noncomputable def JS [NeZero L] : ℝ := sSup I.profits

/-- `x̄_{ℓ,m} = ∑_{n ∈ S_ℓ} x_{n,m}` (SSRN 4112672, 2023-08-22, (4), p. 15). -/
noncomputable def xbar (v : Rates M N) (ℓ : Fin L) (m : Fin M) : ℝ :=
  ∑ n ∈ univ.filter (fun n => ℓ ∈ I.legs n), (v n).1 m

/-- `ȳ_{ℓ,m} = ∑_{n ∈ S_ℓ} δ_{n,m} y_n` (SSRN 4112672, 2023-08-22, (4), p. 15). -/
noncomputable def ybar (v : Rates M N) (ℓ : Fin L) (m : Fin M) : ℝ :=
  ∑ n ∈ univ.filter (fun n => ℓ ∈ I.legs n), I.δ n m * (v n).2

/-- `max {x̄_{ℓ,m} : 1 ≤ ℓ ≤ L}`. -/
noncomputable def xbarMax [NeZero L] (v : Rates M N) (m : Fin M) : ℝ :=
  univ.sup' univ_nonempty fun ℓ : Fin L => I.xbar v ℓ m

/-- `r̄ = ∑_n r_n(x⃗_n, y_n)`, the revenue per period at the rates `v` (App. p. 3 for the optimum). -/
noncomputable def rbar (v : Rates M N) : ℝ := ∑ n, I.rev n (v n)

/-- The revenue term `R_D` of (P_D), p. 15: `∑_n r_n(x⃗_n, y_n) T`. -/
noncomputable def detRevenue (v : Rates M N) : ℝ := I.rbar v * (I.T : ℝ)

/-- The cost terms `C_D` of (P_D), p. 15, as written in (10), App. p. 3:
`∑_m c_o b_{u,m} + ∑_m (c_o T / k) max_ℓ x̄_{ℓ,m} + ∑_m ∑_ℓ c_s (ȳ_{ℓ,m} T - b_{u,m} k)⁺`. -/
noncomputable def detCost [NeZero L] (v : Rates M N) (b : Fin M → ℝ) : ℝ :=
  ∑ m, I.co * b m + ∑ m, I.co * (I.T : ℝ) / (I.k : ℝ) * I.xbarMax v m +
    ∑ m, ∑ ℓ : Fin L, I.cs * max (I.ybar v ℓ m * (I.T : ℝ) - b m * (I.k : ℝ)) 0

/-- The objective of (P_D), p. 15. -/
noncomputable def detProfit [NeZero L] (v : Rates M N) (b : Fin M → ℝ) : ℝ :=
  I.detRevenue v - I.detCost v b

/-- The constraints (4) of (P_D), p. 15: `(x⃗_n, y_n) ∈ Λ^C_n`, `b_{u,m} ≥ b̲_m`, `b_{u,m} ∈ ℝ₊`, and
`x̄_{ℓ,m} T + b_{u,m} k ≤ b̄_m k`. -/
def IsFeasibleD (v : Rates M N) (b : Fin M → ℝ) : Prop :=
  (∀ n, v n ∈ I.Λ n) ∧ (∀ m, 0 ≤ b m ∧ (I.bMin m : ℝ) ≤ b m) ∧
  ∀ ℓ m, I.xbar v ℓ m * (I.T : ℝ) + b m * (I.k : ℝ) ≤ (I.bMax m : ℝ) * (I.k : ℝ)

/-- `(v, b)` is an optimal solution of (P_D), p. 15. Its objective value is `J_D`. -/
def IsOptimalD [NeZero L] (v : Rates M N) (b : Fin M → ℝ) : Prop :=
  I.IsFeasibleD v b ∧ ∀ v' b', I.IsFeasibleD v' b' → I.detProfit v' b' ≤ I.detProfit v b

/-- The `κ`-scaled instance (SSRN 4112672, 2023-08-22, p. 17): `T ↦ κ T`, `b̄_m ↦ κ b̄_m`,
`b̲_m ↦ κ b̲_m`, and all other data unchanged.

**Formalization Note.** "The capacities are all scaled by κ" is read as including `b̲_m`. App. p. 6
says the solution of `P_{D,κ}` is `(x⃗*, y⃗*, κ b⃗*_u)`, which fails if `b̲_m` is not scaled and
binds. -/
def scale (κ : ℕ+) : Instance L M N :=
  { I with
    T := (κ : ℕ) * I.T
    T_pos := Nat.mul_pos κ.pos I.T_pos
    bMax := fun m => (κ : ℕ) * I.bMax m
    bMin := fun m => (κ : ℕ) * I.bMin m
    bMin_le := fun m => Nat.mul_le_mul_left _ (I.bMin_le m) }

end Instance

/-- The scaled coach vector `κ b`. -/
noncomputable def scaleCoaches {M : ℕ} (κ : ℕ+) (b : Fin M → ℝ) : Fin M → ℝ :=
  fun m => ((κ : ℕ) : ℝ) * b m

end RailwayRM


