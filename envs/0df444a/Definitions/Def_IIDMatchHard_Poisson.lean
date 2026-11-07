-- Prove2me | Definitions.Def_IIDMatchHard_Poisson
-- name    : IIDMatchHard_Poisson
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:21.450898+00:00
-- url     : https://prove2.me/theorems/e28efdc3-9f68-4fa1-8124-940e6b571d1c
-- title:
--   The Poisson arrival process with i.i.d. types
-- statement:
--   Let $R>0$ and let $p$ be a distribution on a finite type set $Y$. Take i.i.d. pairs $(g_k,y_k)_{k\ge1}$: $g_k$ is exponential of rate $R$, and $y_k$ is independent of $g_k$ with law $p$. Then $\tau_k=g_1+\dots+g_k$ are the points $\tau_1<\tau_2<\cdots$ of a **Poisson process of rate $R$**, $y_k$ is the type of the $k$-th arrival, and
--   $$K(t)=|\{k\ge1:\tau_k\le t\}|$$
--   is the number of points in $[0,t]$. The online arrivals of the Poisson model are the $K(1)$ points in $[0,1]$. The arrivals of a type $y$ form a Poisson process of rate $\lambda_y=R\,p(y)$.
--
--   This is the arrival model in which the paper computes the values of policies (§3.2).
--
--   **Formalization Note** The sample space is $(\mathbb R\times Y)^{\mathbb N}$ with Mathlib's infinite product measure (`Measure.infinitePi`), which is the zero measure unless $R>0$ and $p$ is a probability vector. Arrivals are indexed from $0$: arrival $k$ is the paper's arrival $k+1$. $K(t)$ is a `Set.ncard`, which is $0$ on an infinite set; that happens only on a null event.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), §3.2, p.6 (PDF p.7); App. B.1, p.14

import Mathlib

set_option autoImplicit false

namespace IIDMatchHard

open MeasureTheory ProbabilityTheory

/-- A sample of the **marked Poisson arrival process**: `ω k = (g_k, y_k)` holds the `k`-th
interarrival gap and the type of the `k`-th arrival (0-based `k`). -/
abbrev Sample (Y : Type*) : Type _ := ℕ → ℝ × Y

variable {Y : Type*}

/-- The arrival time of the arrival with 0-based index `k`, the paper's `τ_{k+1}`: the sum of the
first `k + 1` gaps. -/
def arrTime (ω : Sample Y) (k : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (k + 1), (ω q).1

/-- The type of the arrival with 0-based index `k`, the paper's `y_{k+1}`. -/
def arrType (ω : Sample Y) (k : ℕ) : Y :=
  (ω k).2

/-- `K(t)`, the number of points of the process in `[0, t]`.

**Formalization Note.** The points are counted with `Set.ncard`, which is `0` on an infinite set;
the set is finite almost surely (the gaps are i.i.d. exponential), so this changes `K(t)` only on
a null event. The gaps are nonnegative almost surely, so `τ_k ≥ 0` and the count over `(−∞, t]`
is the count over `[0, t]` almost surely. -/
noncomputable def count (ω : Sample Y) (t : ℝ) : ℕ :=
  {k : ℕ | arrTime ω k ≤ t}.ncard

/-- The types `y_1, …, y_ℓ` of the first `ℓ` arrivals, oldest first. -/
def firstTypes (ω : Sample Y) (ℓ : ℕ) : List Y :=
  List.ofFn fun k : Fin ℓ => arrType ω k

variable [Fintype Y] [MeasurableSpace Y]

/-- The type distribution `p` as a measure on the finite type set. -/
noncomputable def typeMeasure (p : Y → ℝ) : Measure Y :=
  ∑ y, ENNReal.ofReal (p y) • Measure.dirac y

/-- The law of the **Poisson arrival process of rate `R` with i.i.d. types drawn from `p`**
(§3.2, p.6 (PDF p.7)): the pairs `(g_k, y_k)` are i.i.d., with `g_k` exponential of rate `R`
and `y_k` independent of `g_k` with law `p`. Then `τ_k` are the points of a Poisson process of
rate `R`, and each arrival's type is independently generated from `p`. Teng, Yang,
*Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026, sha256
f0193d92…), §3.2, p.6.

**Formalization Note.** Mathlib's `Measure.infinitePi` is the zero measure unless every factor is
a probability measure; the factor is a probability measure exactly when `R > 0` and `p` is a
probability vector. -/
noncomputable def poissonLaw (R : ℝ) (p : Y → ℝ) : Measure (Sample Y) :=
  Measure.infinitePi fun _ : ℕ => (expMeasure R).prod (typeMeasure p)

end IIDMatchHard


