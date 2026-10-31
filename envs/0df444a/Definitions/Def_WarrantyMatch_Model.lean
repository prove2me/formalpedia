-- Prove2me | Definitions.Def_WarrantyMatch_Model
-- name    : WarrantyMatch_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:32.463854+00:00
-- url     : https://prove2.me/theorems/60bfcb7e-c8d8-4b44-840a-e9abff0265b1
-- title:
--   Warranty matching model — uncovered time, cost (1), KS drift (6), geometric inventory time, $a_r$, $b_r$
-- statement:
--   The objects of the random-assignment analysis of Calmon, Graves and Lemmens. Periods and warranty termination dates are integers; $T_w\in\mathbb N$ is the warranty length and $l\in\mathbb N$ the repair lead time.
--
--   1. **Uncovered time and cost (1).** Assigning, in period $t$, a device whose OEM warranty ends at date $i$ to a customer whose customer warranty ends at date $j$ leaves the customer uncovered for $(j-\max(i,t))^+$ periods, and costs
--   $$
--   c_t(i,j)=\beta\cdot\bigl(j-\max(i,t)\bigr)^+ ,
--   $$
--   for a cost rate $\beta$ (the theorems assume $\beta\ge 0$).
--   2. **Kolmogorov–Smirnov drift (6).** A family $(D_u)_{u\in\mathbb Z}$ of integer random variables on a probability space $(\Omega,P)$ satisfies the drift condition with parameter $\varepsilon$ up to period $t$ if
--   $$
--   \bigl|P(D_{u+1}\le k)-P(D_u\le k)\bigr|\le\varepsilon\qquad\text{for all } u\text{ with } u+1\le t \text{ and all } k\in\mathbb Z .
--   $$
--   3. **Admissible family.** $(D_u)$ is admissible up to $t$ (with parameters $\varepsilon$, $T_w$) if every $D_u$ with $u\le t$ is measurable, these $D_u$ are mutually independent, the drift condition holds up to $t$, and $D_u\le t+T_w$ almost surely for every $u\le t$. Here $D_u$ is the customer-warranty termination date of a randomly chosen customer filing a claim in period $u$.
--   4. **Geometric inventory time.** An $\mathbb N$-valued random variable $Z$ is a geometric number of trials with parameter $q$ if it is measurable and $P(Z=k+1)=(1-q)^k q$ for every $k\ge 0$. The time a device spends in inventory is such a $Z$ with $q=d/(y+d)$, where $d$ is the demand and $y$ the inventory per period.
--   5. **Constants.** $a_r=l+\dfrac{y+d}{d}$ and $b_r=\dfrac{y(y+d)}{d^2}$.
--
--   These are the inputs of Proposition 1 and of its proof: the drift condition is the paper's only distributional assumption on the termination dates, and $a_r$, $b_r$ are the mean shift and the variance of the time $l+Z$ between a device's return and its reassignment.
--
--   **Formalization Note** The positive part is `max (·) 0` on $\mathbb Z$, cast to $\mathbb R$. In (6) the paper takes the maximum over $k=1,\dots,m$, the range of dates; here $k$ ranges over all integers. The family is indexed by all integers $u\le t$, because the date $D_{t-l-Z}$ of the reassigned device reaches arbitrarily far back. No lower bound $D_u\ge u$ and no identical distribution is assumed. $Z$ takes values in $\{1,2,\dots\}$ (the "number of trials" convention with mean $1/q$), which is the convention fixed by the paper's $E[Z]=(y+d)/d$; Mathlib's `geometricMeasure` counts failures instead. All objects are bundled in one module because they are used together by every statement.
-- source:
--   Calmon–Graves–Lemmens, Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain, INSEAD WP 2020/03/TOM (SSRN 3357683), eq. (1), p.9; eq. (6) and §4 independence assumption, p.12; §4.1, random assignment and the geometric law of Z, p.13; Proposition 1 (a_r, b_r), p.13; §EC.2, proof of Proposition 1 (support of the dates, E[Z]), pp.ec4–ec5

import Mathlib

open MeasureTheory ProbabilityTheory

namespace WarrantyMatch

/-- The **uncovered warranty time** `(j − max(i, t))⁺` of assigning, in period `t`, a device whose
OEM warranty terminates at date `i` to a customer whose customer warranty terminates at date `j`.
Calmon–Graves–Lemmens, *Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain*,
INSEAD WP 2020/03/TOM (SSRN 3357683), §3, "Matching costs", p.9.

**Formalization Note** Dates are integers; the positive part is `max (·) 0` on `ℤ`, cast to `ℝ`. -/
noncomputable def uncovered (t i j : ℤ) : ℝ := ((max (j - max i t) 0 : ℤ) : ℝ)

/-- The **matching cost** (1): `c_t(i, j) = β · (j − max(i, t))⁺`, for a cost rate `β ≥ 0` per
uncovered period.
Calmon–Graves–Lemmens, INSEAD WP 2020/03/TOM (SSRN 3357683), eq. (1), p.9.

**Formalization Note** The sign condition `β ≥ 0` is not part of the definition; theorems that
need it assume it. -/
noncomputable def cost (β : ℝ) (t i j : ℤ) : ℝ := β * uncovered t i j

/-- The **Kolmogorov–Smirnov drift condition** (6) up to period `t`: for every period `u` with
`u + 1 ≤ t` and every date `k`, `|Pr(D_{u+1} ≤ k) − Pr(D_u ≤ k)| ≤ ε`.
Calmon–Graves–Lemmens, INSEAD WP 2020/03/TOM (SSRN 3357683), eq. (6), p.12.

**Formalization Note** The paper takes the maximum over `k = 1, …, m`, the range of dates; here
`k` ranges over all integers, which is the same condition when the dates lie in `[1, m]`. The
family is indexed by all integers `u ≤ t`, because the replacement device's date `D_{t−l−Z}`
reaches arbitrarily far back. -/
def KSDrift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℤ → Ω → ℤ) (ε : ℝ) (t : ℤ) :
    Prop :=
  ∀ u : ℤ, u + 1 ≤ t → ∀ k : ℤ,
    |(P {ω | D (u + 1) ω ≤ k}).toReal - (P {ω | D u ω ≤ k}).toReal| ≤ ε

/-- The standing model of §4 for the customer-warranty termination dates up to period `t`:
`D u` is the termination date of a randomly chosen customer filing a claim in period `u`, and
1. every `D u`, `u ≤ t`, is a random variable (measurable);
2. the dates `D u`, `u ≤ t`, are mutually independent (p.12: "we assume that D1, …, DT are
   independent random variables, but not necessarily identically distributed");
3. the drift condition (6) holds for all `u + 1 ≤ t` (`KSDrift`);
4. every `D u`, `u ≤ t`, is at most `t + T_w` almost surely, since warranties have length `T_w`
   (p.ec4: "at time t, customers and devices will have latest warranty termination date of
   t + Tw").
Calmon–Graves–Lemmens, INSEAD WP 2020/03/TOM (SSRN 3357683), §4, p.12, eq. (6); §EC.2, proof
of Proposition 1, p.ec4.

**Formalization Note** No lower bound `D u ≥ u` and no identical distribution is assumed.
Independence is required only among the indices `u ≤ t` (the subtype `Set.Iic t`). The support
clause is the page's bound at the current period `t`, for customers and for the returned devices
alike. It is implied by the sharper `D u ≤ u + T_w`, and unlike that one it admits stationary
laws (`ε = 0`), which a condition on every `u ≤ t` with `u + T_w` would exclude. -/
structure Admissible {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℤ → Ω → ℤ) (ε : ℝ)
    (Tw : ℕ) (t : ℤ) : Prop where
  measurable : ∀ u ≤ t, Measurable (D u)
  indep : iIndepFun (fun u : Set.Iic t => D u) P
  drift : KSDrift P D ε t
  support : ∀ u ≤ t, ∀ᵐ ω ∂P, D u ω ≤ t + Tw

/-- `Z` is a **geometric number of trials** with success probability `q`: a measurable `ℕ`-valued
random variable with `Pr(Z = k + 1) = (1 − q)^k q` for every `k ∈ ℕ`. This is the time a device
spends in inventory, with `q = d/(y + d)`.
Calmon–Graves–Lemmens, INSEAD WP 2020/03/TOM (SSRN 3357683), §4.1, p.13 ("Z becomes a geometric
random variable with parameter d/(y + d)"); §EC.2, p.ec5 (`E[Z] = (y + d)/d`).

**Formalization Note** The support is `{1, 2, …}` (the "number of trials" convention, mean
`1/q`), which is the convention fixed by the paper's `E[Z] = (y+d)/d`. Mathlib's
`geometricMeasure` counts failures and starts at `0`. For `0 < q ≤ 1` the listed masses sum to
`1`, so under a probability measure `Pr(Z = 0) = 0` follows. -/
def IsGeomTrials {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℕ) (q : ℝ) : Prop :=
  Measurable Z ∧ ∀ k : ℕ, (P {ω | Z ω = k + 1}).toReal = (1 - q) ^ k * q

/-- The constant `a_r = l + (y + d)/d` of Proposition 1.
Calmon–Graves–Lemmens, INSEAD WP 2020/03/TOM (SSRN 3357683), Proposition 1, p.13. -/
noncomputable def aR (l : ℕ) (y d : ℝ) : ℝ := (l : ℝ) + (y + d) / d

/-- The constant `b_r = y(y + d)/d²` of Proposition 1.
Calmon–Graves–Lemmens, INSEAD WP 2020/03/TOM (SSRN 3357683), Proposition 1, p.13. -/
noncomputable def bR (y d : ℝ) : ℝ := y * (y + d) / d ^ 2

end WarrantyMatch


