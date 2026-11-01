-- Prove2me | Definitions.Def_LPResolvingRM_regret
-- name    : LPResolvingRM_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:41:13.993836+00:00
-- url     : https://prove2.me/theorems/9674362a-709b-4249-a12f-87649e40407b
-- title:
--   Algorithm 1 with an LP solution rule, the law of its run, the stopping time $\tau$ and the regret $\mathrm{Reg}_T$
-- statement:
--   At each period $t\ge2$ Algorithm 1 solves the sampled LP
--   $$\max\ \sum_{j=1}^n\frac{n_{t-1}(j)}{t-1}\mu_jy_j\quad\text{s.t.}\quad\sum_{j=1}^n\frac{n_{t-1}(j)}{t-1}c_jy_j\le b_t,\quad0\le y_j\le1, \tag{5}$$
--   takes an optimal solution $y^*_t$, observes the type $j$ and accepts with probability $y^*_{j,t}$ when the constraint permits (otherwise rejects); at $t=1$ it accepts. A **solution rule** `sel` maps the frequencies and the right-hand side to an optimal solution of (5); every such rule defines a law on the sample paths (types i.i.d. with law $p$, coins as above), and $\mathbb E$ is the expectation under it.
--
--   The **stopping time** is $\tau:=\min\{t: B_{i,t}\le1\text{ for some }i\}-1$, with $t$ ranging over $1,\dots,T+1$ and $\tau=T$ if no resource falls to $1$. The **regret** is
--   $$\mathrm{Reg}^\pi_T:=\mathbb E\Big[T\cdot\mathrm{OPT}_D-\sum_{t=1}^{\tau}r_tx_t\Big],$$
--   with $r_t=\mu_{j_t}$; rewards after $\tau$ are not counted.
--
--   **Formalization Note** All randomness is finite, so $\mathbb E$ is a finite sum over type sequences and coin sequences weighted by the path probability.
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, §2.1, p.6; §2.2, p.7; Algorithm 1, p.8

import Definitions.Def_LPResolvingRM_Assumption2
import Definitions.Def_LPResolvingRM_cap

open scoped Classical

namespace LPResolvingRM

/-- A **solution rule for the sampled LP (5)**: it maps the empirical frequencies `q` and the
right-hand side `r` to a vector `y ∈ ℝⁿ` (arXiv:2101.11092v3, Algorithm 1, lines 7–8, p.8). -/
abbrev Selector (n m : ℕ) := (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ)

/-- `sel` **returns an optimal solution of the sampled LP (5)**
`max ∑_j q_jμ_j y_j s.t. ∑_j q_j c_j y_j ≤ r, 0 ≤ y_j ≤ 1` for every frequency vector `q` and
every right-hand side `r ≥ 0` (arXiv:2101.11092v3, Algorithm 1, lines 7–8: "Denote the optimal
solution as y∗ₜ", p.8). Optimality is the published `LPAllocRM.IsLPOptimal` with upper bound
`1`.

**Formalization Note.** LP (5) can have several optimal solutions and the paper does not say
which one is used; quantifying over every such `sel` covers every tie-breaking rule that is a
function of the LP's data. For `r ≥ 0` the point `y = 0` is feasible and the feasible set is
compact, so optimal solutions exist; the algorithm only calls `sel` with `r = b_t ≥ 0`. -/
def IsSelector {n m : ℕ} (I : Instance n m) (sel : Selector n m) : Prop :=
  ∀ (q : Fin n → ℝ) (r : Fin m → ℝ), (∀ i, 0 ≤ r i) →
    LPAllocRM.IsLPOptimal (Matrix.of fun i j => q j * I.c j i) r 1 (fun j => q j * I.μ j)
      (sel q r)

/-- The **acceptance probabilities** used by Algorithm 1 at the paper's period `t = k + 1` when
the remaining average capacity is `r` (arXiv:2101.11092v3, Algorithm 1, p.8): `1` for every type
at `t = 1` (line 3, `x₁ = 1`), and `y*_t = sel(n_{t−1}/(t−1), r)` for `t ≥ 2` (lines 7–10). -/
noncomputable def yRule {n m T : ℕ} (sel : Selector n m) (ω : Fin T → Fin n) (k : ℕ)
    (r : Fin m → ℝ) : Fin n → ℝ :=
  if k = 0 then fun _ => 1 else sel (freq ω k) r

/-- The **conditional probability of the coin** of Lean period `k` given the past
(arXiv:2101.11092v3, Algorithm 1, line 10, p.8). With `y = y*_{j,t}` for the arriving type
`j = ω k` (computed from the history and `b_t`): if the constraint permits, the coin is `true`
with probability `y` and `false` with probability `1 − y`; otherwise `x_t = 0` and the coin is
`false` with probability `1`. -/
noncomputable def bitWeight {n m : ℕ} (I : Instance n m) (sel : Selector n m) (T : ℕ)
    (ω : Fin T → Fin n) (β : Fin T → Bool) (k : Fin T) : ℝ :=
  let y := yRule sel ω k.val (avgCap I T ω β k.val) (ω k)
  if permitted I T ω β k then (if β k = true then y else 1 - y)
  else (if β k = true then 0 else 1)

/-- The **probability of a sample path** `(ω, β)` of Algorithm 1 over the horizon `T`
(arXiv:2101.11092v3, Assumption 1 (a) and Algorithm 1): the types are i.i.d. with law `p`, and
each coin follows `LPResolvingRM.bitWeight` given the past. -/
noncomputable def pathWeight {n m : ℕ} (I : Instance n m) (sel : Selector n m) (T : ℕ)
    (ω : Fin T → Fin n) (β : Fin T → Bool) : ℝ :=
  (∏ k, I.p (ω k)) * ∏ k, bitWeight I sel T ω β k

/-- **Expectation over the run of Algorithm 1**: the finite sum of `X(ω, β)` weighted by the path
probability `LPResolvingRM.pathWeight`.

**Formalization Note.** Every quantity of the paper is a function of the type sequence and the
acceptance decisions, both finite, so `E[·]` is this finite sum (no measure space). -/
noncomputable def expect {n m : ℕ} (I : Instance n m) (sel : Selector n m) (T : ℕ)
    (X : (Fin T → Fin n) → (Fin T → Bool) → ℝ) : ℝ :=
  ∑ ω : Fin T → Fin n, ∑ β : Fin T → Bool, pathWeight I sel T ω β * X ω β

/-- **Probability of an event** of the run of Algorithm 1: the expectation of its indicator. -/
noncomputable def prob {n m : ℕ} (I : Instance n m) (sel : Selector n m) (T : ℕ)
    (S : (Fin T → Fin n) → (Fin T → Bool) → Prop) : ℝ :=
  expect I sel T fun ω β => if S ω β then 1 else 0

/-- **The stopping time** `τ := min{t : B_{i,t} ≤ 1 for some i = 1, …, m} − 1`
(arXiv:2101.11092v3, p.7).

**Formalization Note.** Reading R4: `t` ranges over `1, …, T + 1`, and `τ := T` when no such `t`
exists. With `B_t = cap (t − 1)` this is the least `k ≤ T` with `cap k i ≤ 1` for some `i`, or
`T`. -/
noncomputable def tau {n m : ℕ} (I : Instance n m) (T : ℕ) (ω : Fin T → Fin n)
    (β : Fin T → Bool) : ℕ :=
  if h : ∃ k, k ≤ T ∧ ∃ i, cap I T ω β k i ≤ 1 then Nat.find h else T

/-- **Collected reward up to period `t`**: `∑_{s=1}^{t} r_s x_s` with `r_s = μ_{j_s}`
(arXiv:2101.11092v3, p.6), i.e. the rewards of the accepted orders of the Lean periods `k < t`. -/
noncomputable def reward {n m : ℕ} (I : Instance n m) (T : ℕ) (ω : Fin T → Fin n)
    (β : Fin T → Bool) (t : ℕ) : ℝ :=
  ∑ k : Fin T, if k.val < t ∧ accepted I T ω β k then I.μ (ω k) else 0

/-- **The regret of Algorithm 1** (arXiv:2101.11092v3, §2.1, p.6):
`Reg^π_T := E[T · OPT_D − ∑_{t=1}^{τ} r_t x_t]`, where the decisions follow Algorithm 1 with the
LP solution rule `sel`, and rewards after the stopping time `τ` are not counted. -/
noncomputable def regret {n m : ℕ} (I : Instance n m) (sel : Selector n m) (T : ℕ) : ℝ :=
  expect I sel T fun ω β => (T : ℝ) * optD I - reward I T ω β (tau I T ω β)

end LPResolvingRM


