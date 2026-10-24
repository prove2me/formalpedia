-- Prove2me | Definitions.Def_GenCostSched_GFCS_Model
-- name    : GenCostSched_GFCS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:57.725613+00:00
-- url     : https://prove2.me/theorems/abf534f5-f1fc-4d34-b214-b8d251ac3d2f
-- title:
--   §II–IV, pp. 5–22 — online single-machine instance with general costs, LP (1)/(21) value, GFCS(s) (7), its dual (2), Algorithm 2, Definition 5, β̂ (20), K
-- statement:
--   This file sets up the model of Etesami's online scheduling problem with general cost functions (GFCS) and every object the analysis of Algorithm 2 uses.
--
--   **Online instance** (§II, p. 5). There are $n$ jobs. Job $j$ has length $v_j>0$, release time $r_j\ge 0$, and a cost function $g_j$, which is the *scaled* function of p. 6 (the original cost divided by $v_j$). The standing assumptions are that on $[r_j,\infty)$ each $g_j$ is nonnegative, nondecreasing, differentiable with derivative $g'_j$, and $g_j(r_j)=0$, and that jobs are indexed in release order $r_1\le r_2\le\cdots$. Where the curvature constant is used, $g'_j$ is differentiable on $[r_j,\infty)$ with derivative $g''_j$. The curvature condition for a real $K$ is
--   $$K\ge 1,\qquad (t-r_\ell)\,g''_\ell(t)\le (K-1)\,g'_\ell(t)\quad\text{for all }\ell,\ t\ge r_\ell .$$
--
--   **Schedules and the benchmark.** A fractional schedule with machine capacity $c$ is a family of measurable rates $x_j(t)\ge 0$, zero before $r_j$, with $\sum_j x_j(t)\le c$ for all $t$ and $\int x_j\ge v_j$ for every $j$. Its cost is $\sum_j\int g_j(t)x_j(t)\,dt$, and $\mathrm{OPT}_c$ is the infimum of the cost over all such schedules: the value of LP (1) for $c=1$ and of LP (21) for $c=1/(1+\epsilon)$. The dual (2) is written per unit length, $a_j=\alpha_j/v_j$: $a_j\ge 0$, $\beta$ is integrable and nonnegative on $[0,\infty)$, and $a_j\le\beta_t+g_j(t)$ for almost every $t\ge r_j$. Its objective with capacity $c$ is $\sum_j a_jv_j-c\int_0^\infty\beta_t\,dt$.
--
--   **The offline problem GFCS(s)** ((7), p. 11; Definition 3, p. 15). The jobs of a finite set $A$ all start at time $s$, with lengths $\rho_j$ (the residual lengths). Fractional schedules have total rate at most $1$, and $\mathrm{RNF}$ is the infimum of the cost over them. An integral schedule has rates in $\{0,1\}$, processes each job of $A$ exactly $\rho_j$ and finishes in finite time. An *optimal integral* schedule is an integral schedule whose cost is at most that of every fractional schedule. Its dual is the restriction of (2) to $[s,\infty)$, with objective $\sum_{j\in A}a_j\rho_j-\int_s^\infty\beta$. An *optimal* dual maximizes this objective, and a *maximal* optimal dual (proof of Lemma 4, p. 17) has the largest $\int_s^\infty\beta$ among optimal duals.
--
--   **Postponement and Definition 5** (p. 20). A schedule $x'$ *postpones* $x$ on the jobs $A$ if for every $\ell\in A$ and $u\ge s$ the amount of $\ell$ processed by $x'$ during $[s,u]$ is at most that processed by $x$. A class $H$ of cost functions is *monotone substitute* if, for every identical-release instance with cost functions in $H$ and every optimal integral schedule $x$, adding a new job leaves an optimal integral schedule that postpones $x$ on the existing jobs.
--
--   **Algorithm 2** (p. 15). A run is a sequence of schedules $X_0=0,X_1,\dots,X_n$. At the arrival of job $k$, $X_{k+1}$ agrees with $X_k$ before $r_k$. From $r_k$ on it is an optimal integral schedule of GFCS($r_k$) for the alive old jobs (earlier jobs with positive residual length $v_j-\int_{t<r_k}X_k$) together with job $k$, with their residual lengths. It postpones the continuing schedule on the old jobs. $\mathrm{Cost(Alg)}$ is the cost of $X_n$. The dual update replaces the tail of $\beta$ from $r_k$ on, so the generated $\beta$ equals the tail chosen at arrival $k$ on $[r_k,r_{k'})$, where $k'$ is the next job, and is $0$ before the first release.
--
--   **β̂** ((20), p. 20). For a schedule $x$, $\hat\beta_t=\sum_\ell\int_{(t,\infty)}g'_\ell(\tau)x_\ell(\tau)\,d\tau$: the total increase of the cost functions over the processing that remains after $t$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Costs and processed amounts are `lintegral`s in $\mathbb R_{\ge 0}\cup\{\infty\}$, so a non-integrable schedule cannot have the junk cost $0$. Dual feasibility holds almost everywhere, because $\beta$ is a density. Both feasible sets are nonempty: run the jobs one after another. So no infimum is the value of an empty `sInf`. Runs are a relation on sequences of schedules indexed by $\mathbb N$; only $X_0,\dots,X_n$ matter.
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, pp. 5–7 (§II, (1), (2), Definition 1), p. 11 ((7)), p. 15 (Algorithm 2, Definition 3), p. 18 (Definition 4), p. 20 (Definition 5, Theorem 3, (20)), p. 21 ((21))

import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-!
# Online single-machine scheduling with general cost functions (Etesami, arXiv:1906.02644v3)

Model of §II (pp. 5–7), the offline identical-release problem GFCS(s) of §III, (7), p. 11 and
Definition 3, p. 15, its dual (2), Algorithm 2 (p. 15), Definition 5 (p. 20), β̂ (20) (p. 20),
the slower benchmark LP (21) (p. 21) and the curvature constant K of Theorem 3 (p. 20).

Conventions.
* Jobs are `Fin n` (or `Fin m` for an offline instance); times are real numbers.
* A schedule is a family of processing rates `x j t`; the machine has capacity `∑ j x j t ≤ c`.
* Costs and processed amounts are `lintegral`s in `ℝ≥0∞` of `ENNReal.ofReal (…)`, so no
  integrability side condition can turn a cost into a junk `0`. On every schedule considered
  here the integrand is nonnegative (rates are `≥ 0` and vanish before the job's release, where
  the cost function is `≥ 0`), so `ofReal` changes nothing.
* The dual variable `β` is a density on the time axis: dual feasibility is required for
  almost every `t`, and `β` must be integrable on the horizon.
* `g j` is the **scaled** cost function of p. 6 (the paper's `g_j / v_j`).
-/

/-! ### The offline problem GFCS(s) for a bare family of cost functions -/

/-- The tail `t ↦ 1_{t ≥ s} x j t` of a schedule from time `s` on. -/
noncomputable def tailFrom {m : ℕ} (s : ℝ) (x : Fin m → ℝ → ℝ) : Fin m → ℝ → ℝ :=
  fun j => (Ici s).indicator (x j)

/-- Feasible (fractional) schedule of the identical-release instance GFCS(s)
(Definition 3, p. 15; (7), p. 11): jobs `A` with lengths `ρ j` (the residual lengths),
all released at time `s`; measurable rates `x j t ≥ 0`, zero before `s` and for jobs outside
`A`, total rate at most `1` at every time, and every job of `A` processed at least `ρ j`
(`∫_s^∞ x_j(t)/ρ_j dt ≥ 1`). -/
def IsOffFracSched {m : ℕ} (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ)
    (x : Fin m → ℝ → ℝ) : Prop :=
  (∀ j, Measurable (x j)) ∧ (∀ j t, 0 ≤ x j t) ∧ (∀ j t, t < s → x j t = 0) ∧
  (∀ j, j ∉ A → ∀ t, x j t = 0) ∧ (∀ t, ∑ j, x j t ≤ 1) ∧
  (∀ j ∈ A, ENNReal.ofReal (ρ j) ≤ ∫⁻ t, ENNReal.ofReal (x j t))

/-- The LP objective `∑_j ∫ g_j(t) x_j(t) dt` of (1) / Definition 3, valued in `ℝ≥0∞`. -/
noncomputable def offCost {m : ℕ} (G : Fin m → ℝ → ℝ) (x : Fin m → ℝ → ℝ) : ℝ≥0∞ :=
  ∑ j, ∫⁻ t, ENNReal.ofReal (G j t * x j t)

/-- `RNF` of Definition 3 (p. 15): the optimal value of GFCS(s) with jobs `A`, lengths `ρ` and
cost functions `G`, i.e. the infimum of the LP objective over **all** feasible fractional
schedules. The feasible set is nonempty (process the jobs of `A` one after another at rate 1
from time `s`), so this infimum is never the junk value of an empty `sInf`. -/
noncomputable def rnf {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m))
    (ρ : Fin m → ℝ) : ℝ≥0∞ :=
  sInf (offCost G '' {x | IsOffFracSched s A ρ x})

/-- An integral schedule of GFCS(s): rates in `{0, 1}` (one job at a time at unit speed), zero
before `s` and outside `A`, every job of `A` processed exactly its length `ρ j`, and all
processing finished by some finite time (the paper's `x^o`, (9), p. 12). -/
def IsOffIntSched {m : ℕ} (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ)
    (x : Fin m → ℝ → ℝ) : Prop :=
  (∀ j, Measurable (x j)) ∧ (∀ j t, x j t = 0 ∨ x j t = 1) ∧ (∀ j t, t < s → x j t = 0) ∧
  (∀ j, j ∉ A → ∀ t, x j t = 0) ∧ (∀ t, ∑ j, x j t ≤ 1) ∧
  (∀ j ∈ A, ∫⁻ t, ENNReal.ofReal (x j t) = ENNReal.ofReal (ρ j)) ∧
  (∃ T : ℝ, ∀ j t, T < t → x j t = 0)

/-- An optimal integral schedule of GFCS(s): an integral schedule whose cost is at most the cost
of **every fractional** feasible schedule of the same instance (optimal for the LP (7)). -/
def IsOptIntegral {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ)
    (x : Fin m → ℝ → ℝ) : Prop :=
  IsOffIntSched s A ρ x ∧ ∀ y, IsOffFracSched s A ρ y → offCost G x ≤ offCost G y

/-- Feasibility for the dual (2) of GFCS(s), in per-unit form: `a j` stands for the paper's
`α_j / ρ_j` (so `α_j ≥ 0 ↔ a j ≥ 0` as `ρ j > 0`). The density `β` is integrable on `[s, ∞)`,
nonnegative a.e. there, and `a j ≤ β t + G j t` for a.e. `t ≥ s` and every `j ∈ A`. -/
def IsOffDualFeas {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m))
    (a : Fin m → ℝ) (β : ℝ → ℝ) : Prop :=
  IntegrableOn β (Ici s) ∧ (∀ j ∈ A, 0 ≤ a j) ∧ (∀ᵐ t, s ≤ t → 0 ≤ β t) ∧
  ∀ j ∈ A, ∀ᵐ t, s ≤ t → a j ≤ β t + G j t

/-- Dual objective `∑_{j ∈ A} α_j − ∫_s^∞ β_t dt` with `α_j = a j * ρ j`. -/
noncomputable def offDualObj {m : ℕ} (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ)
    (a : Fin m → ℝ) (β : ℝ → ℝ) : ℝ :=
  ∑ j ∈ A, a j * ρ j - ∫ t in Ici s, β t

/-- An optimal dual solution of GFCS(s): feasible, and its objective is at least that of every
feasible dual solution. -/
def IsOffOptDual {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ)
    (a : Fin m → ℝ) (β : ℝ → ℝ) : Prop :=
  IsOffDualFeas G s A a β ∧
    ∀ a' β', IsOffDualFeas G s A a' β' → offDualObj s A ρ a' β' ≤ offDualObj s A ρ a β

/-- The *maximal* optimal dual of the proof of Lemma 4 (p. 17): an optimal dual solution whose
`∫_s^∞ β` is the largest among all optimal dual solutions. -/
def IsOffMaxOptDual {m : ℕ} (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ)
    (a : Fin m → ℝ) (β : ℝ → ℝ) : Prop :=
  IsOffOptDual G s A ρ a β ∧
    ∀ a' β', IsOffOptDual G s A ρ a' β' → ∫ t in Ici s, β' t ≤ ∫ t in Ici s, β t

/-- `x'` **postpones** `x` on the jobs `A` (reading of Definition 5, p. 20): for every job
`ℓ ∈ A` and every time `u ≥ s`, the amount of `ℓ` processed by `x'` during `[s, u]` is at most
the amount processed by `x` during `[s, u]`. -/
def postpones {m : ℕ} (s : ℝ) (A : Finset (Fin m)) (x x' : Fin m → ℝ → ℝ) : Prop :=
  ∀ ℓ ∈ A, ∀ u, s ≤ u →
    ∫⁻ t in Icc s u, ENNReal.ofReal (x' ℓ t) ≤ ∫⁻ t in Icc s u, ENNReal.ofReal (x ℓ t)

/-- **Definition 5** (p. 20), as read in this mission: a class `H` of cost functions is
*monotone substitute* if, for every identical-release instance GFCS(s) whose jobs `A ∪ {k}`
have cost functions in `H` (nonnegative and nondecreasing on `[s, ∞)`) and positive lengths,
and every optimal integral schedule `x` of the instance with jobs `A`, there is an optimal
integral schedule `x'` of the instance with the new job `k` added that postpones `x` on the
existing jobs. -/
def IsMonotoneSubstitute (H : Set (ℝ → ℝ)) : Prop :=
  ∀ (m : ℕ) (G : Fin m → ℝ → ℝ) (s : ℝ) (A : Finset (Fin m)) (ρ : Fin m → ℝ) (k : Fin m),
    (∀ i ∈ insert k A, G i ∈ H) → (∀ i ∈ insert k A, ∀ t, s ≤ t → 0 ≤ G i t) →
    (∀ i ∈ insert k A, MonotoneOn (G i) (Ici s)) →
    (∀ j ∈ A, 0 < ρ j) → k ∉ A → 0 < ρ k →
    ∀ x, IsOptIntegral G s A ρ x →
      ∃ x', IsOptIntegral G s (insert k A) ρ x' ∧ postpones s A x x'

/-- `β̂_t` of (20) (p. 20) for a schedule `x` with cost derivatives `gp`:
`∑_ℓ ∫_{(t,∞)} g'_ℓ(τ) x_ℓ(τ) dτ`, the total increase of `g_ℓ` over the part of job `ℓ`'s
processing after time `t` (for an integral schedule this is `∑_ℓ ∑_d [g_ℓ(C^{2d}) − g_ℓ(C^{2d−1})]`
over the remaining processing intervals, by the fundamental theorem of calculus). -/
noncomputable def betaHat {m : ℕ} (gp : Fin m → ℝ → ℝ) (x : Fin m → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ ℓ, ∫ τ in Ioi t, gp ℓ τ * x ℓ τ

/-! ### The online instance -/

/-- An instance of the online GFCS problem (§II, p. 5) with `n` jobs: lengths `v j`, release
times `r j`, **scaled** cost functions `g j` (the paper's `g_j / v_j`, p. 6) and given first and
second derivatives `g' j`, `g'' j`. -/
structure Instance (n : ℕ) where
  v : Fin n → ℝ
  r : Fin n → ℝ
  g : Fin n → ℝ → ℝ
  g' : Fin n → ℝ → ℝ
  g'' : Fin n → ℝ → ℝ

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- Standing assumptions of §II (p. 5) for job `j`: `v_j > 0`, `r_j ≥ 0`, and on `[r_j, ∞)` the
cost function `g_j` is nonnegative, nondecreasing, differentiable with derivative `g'_j`, and
`g_j(r_j) = 0`. -/
def JobStanding (j : Fin n) : Prop :=
  0 < I.v j ∧ 0 ≤ I.r j ∧ (∀ t, I.r j ≤ t → 0 ≤ I.g j t) ∧ MonotoneOn (I.g j) (Ici (I.r j)) ∧
    I.g j (I.r j) = 0 ∧ ∀ t, I.r j ≤ t → HasDerivWithinAt (I.g j) (I.g' j t) (Ici (I.r j)) t

/-- Standing assumptions for all jobs, and jobs indexed in release order `r_1 ≤ r_2 ≤ …`
(p. 18). -/
def Standing : Prop :=
  (∀ j, I.JobStanding j) ∧ Monotone I.r

/-- Twice differentiability on `[r_j, ∞)`: `g''_j` is the derivative of `g'_j` there. -/
def TwiceDiff : Prop :=
  ∀ j, ∀ t, I.r j ≤ t → HasDerivWithinAt (I.g' j) (I.g'' j t) (Ici (I.r j)) t

/-- `K` bounds the curvature as in Theorem 3 (p. 20): `K ≥ 1` and
`(t − r_ℓ) g''_ℓ(t) ≤ (K − 1) g'_ℓ(t)` for every job `ℓ` and `t ≥ r_ℓ`. The paper's
`K = 1 + sup_{ℓ, t ≥ r_ℓ} (t − r_ℓ) g''_ℓ(t) / g'_ℓ(t)` is the least such `K` when `g' > 0` and
the supremum is finite. -/
def CurvBound (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ ℓ, ∀ t, I.r ℓ ≤ t → (t - I.r ℓ) * I.g'' ℓ t ≤ (K - 1) * I.g' ℓ t

/-- A feasible schedule of LP (1) on a machine of capacity `c` (LP (21) for `c = 1/(1+ε)`,
p. 21): measurable rates `x j t ≥ 0`, zero before `r_j`, total rate at most `c`, and every job
processed at least `v_j`. -/
def IsFracSched (c : ℝ) (x : Fin n → ℝ → ℝ) : Prop :=
  (∀ j, Measurable (x j)) ∧ (∀ j t, 0 ≤ x j t) ∧ (∀ j t, t < I.r j → x j t = 0) ∧
    (∀ t, ∑ j, x j t ≤ c) ∧ ∀ j, ENNReal.ofReal (I.v j) ≤ ∫⁻ t, ENNReal.ofReal (x j t)

/-- Cost `∑_j ∫_{r_j}^∞ g_j(t) x_j(t) dt` of a schedule (the objective of (1)). -/
noncomputable def cost (x : Fin n → ℝ → ℝ) : ℝ≥0∞ :=
  offCost I.g x

/-- `OPT_c`: the optimal value of LP (1) with machine capacity `c` (LP (21) for
`c = 1/(1+ε)`), the infimum of the cost over all feasible fractional schedules. For `c > 0` the
feasible set is nonempty (run the jobs one after another in release order at rate `c`), and
costs are `≥ 0`, so this is a genuine infimum. -/
noncomputable def optLP (c : ℝ) : ℝ≥0∞ :=
  sInf (I.cost '' {x | I.IsFracSched c x})

/-- Feasibility for the dual (2) of LP (1) (p. 7), per-unit form `a j = α_j / v_j`: `β` is
integrable on `[0, ∞)` and a.e. nonnegative there, `a j ≥ 0`, and `a j ≤ β t + g_j(t)` for
a.e. `t ≥ r_j`. The dual of (21) has the same constraints (p. 21). -/
def IsDualFeas (a : Fin n → ℝ) (β : ℝ → ℝ) : Prop :=
  IntegrableOn β (Ici 0) ∧ (∀ j, 0 ≤ a j) ∧ (∀ᵐ t, 0 ≤ t → 0 ≤ β t) ∧
    ∀ j, ∀ᵐ t, I.r j ≤ t → a j ≤ β t + I.g j t

/-- Objective `∑_j α_j − c ∫_0^∞ β_t dt` of the dual of LP (1) with capacity `c`
(`c = 1`: (2); `c = 1/(1+ε)`: (21)), with `α_j = a j * v_j`. -/
noncomputable def dualObj (c : ℝ) (a : Fin n → ℝ) (β : ℝ → ℝ) : ℝ :=
  ∑ j, a j * I.v j - c * ∫ t in Ici 0, β t

/-- Residual length `v_j(r_k) = v_j − ∫_{t < r_k} y_j(t) dt` of job `j` at the release time of
job `k` under the schedule `y`. -/
noncomputable def residual (y : Fin n → ℝ → ℝ) (k j : Fin n) : ℝ :=
  I.v j - ∫ t in Iio (I.r k), y j t

/-- The alive old jobs `A(r_k)` at the arrival of job `k` (p. 7): earlier jobs with positive
residual length. -/
noncomputable def aliveOld (y : Fin n → ℝ → ℝ) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j < k ∧ 0 < I.residual y k j)

/-- A run of **Algorithm 2** (p. 15). `X k` is the schedule in force after the first `k`
arrivals (`X 0 = 0`). Upon the arrival of job `k` at `r_k`, the schedule is kept before `r_k`
and replaced from `r_k` on by an optimal integral schedule of GFCS(r_k) whose jobs are the alive
old jobs and job `k`, with their residual lengths (later jobs are not seen). The re-solve picks
an optimal schedule that postpones the continuing one on the old alive jobs (tie-break; such a
choice exists for a monotone substitute class). Jobs released at the same time are handled one
after another in index order. -/
def IsAlg2Run (X : ℕ → Fin n → ℝ → ℝ) : Prop :=
  X 0 = 0 ∧ ∀ k : Fin n,
    (∀ j t, t < I.r k → X (k.val + 1) j t = X k.val j t) ∧
    IsOptIntegral I.g (I.r k) (insert k (I.aliveOld (X k.val) k)) (I.residual (X k.val) k)
      (tailFrom (I.r k) (X (k.val + 1))) ∧
    postpones (I.r k) (I.aliveOld (X k.val) k) (tailFrom (I.r k) (X k.val))
      (tailFrom (I.r k) (X (k.val + 1)))

/-- `Cost(Alg)`: the cost of the final schedule of a run, after all `n` arrivals. -/
noncomputable def algCost (X : ℕ → Fin n → ℝ → ℝ) : ℝ≥0∞ :=
  I.cost (X n)

/-- The time segment `[r_k, r_{k'})` (with `k'` the next job, `r_{n} := ∞`) during which the dual
tail set at the arrival of job `k` stays in force (p. 15: the tail `{β_t}_{t ≥ r_k}` is
replaced at each arrival). Empty when a later job has the same release time. -/
def segment (k : Fin n) : Set ℝ :=
  {t | I.r k ≤ t ∧ ∀ k' : Fin n, k < k' → t < I.r k'}

/-- The β-variable generated by the dual update of Algorithm 2 (p. 15) from the tails `B k`
chosen at the arrivals: `B k` on the segment of job `k`, and `0` before the first release. -/
noncomputable def concatDual (B : Fin n → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ k, (I.segment k).indicator (B k) t

end Instance

end GenCostSched.GFCS


