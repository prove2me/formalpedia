-- Prove2me | Definitions.Def_OMSRArbitrary_Releases
-- name    : OMSRArbitrary_Releases
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:15.423197+00:00
-- url     : https://prove2.me/theorems/e41c9710-b741-4704-a3c9-6ea5ae19d17b
-- title:
--   Releases, release arrivals (Definition F.2) and the auxiliary dual $\hat a_\tau$
-- statement:
--   Fix $i$ and seeds $u$ with $u:=u_i$.
--
--   1. A run of PG **releases at $\tau$** if it probes $i$ at $\tau$, its best alternative $J=J_\tau$ exists, and $p_{i\tau}<z_\tau\le p_{J\tau}$.
--   2. Let $z^{(\tau)}=(z_{<\tau},0,z_{>\tau})$; the run of PG$(u)$ on $z^{(\tau)}$ is the run in which $(i,\tau)$ succeeds. An arrival $\tau$ is a **release arrival** (Definition F.2) if (i) PG$(u)$ probes $i$ at $\tau$, a best alternative $J_\tau$ exists and $p_{i\tau}<p_{J\tau}$, and (ii) in the run on $z^{(\tau)}$, at every arrival $t>\tau$ with $(i,t)\in E$ and $z_t\le p_{it}$, PG$(u)$ probes a resource whose reduced price is at least $r_ip_{it}(1-g(u))$.
--   3. $a_\tau$ is the indicator that PG$(u)$ probes $i$ at $\tau$ and $z_\tau\le p_{i\tau}$, and
--   $$\hat a_\tau=\begin{cases}p_{i\tau}/p_{J\tau}&\tau\text{ a release arrival and }z_\tau\le p_{J\tau},\\0&\tau\text{ a release arrival and }z_\tau>p_{J\tau},\\a_\tau&\text{otherwise.}\end{cases}$$
--
--   The auxiliary dual spreads the mass of a probe of $i$ over a larger set of thresholds; Lemma F.3 shows it keeps the expectation.
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Definition 12, p.18 (restated p.40); §4.2 (Release Arrivals), p.19; Definition F.2, pp.40–41; App. F.2 (The Auxiliary Dual), p.41

import Mathlib
import Definitions.Def_OMSRArbitrary_PerturbedGreedy

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds)
noncomputable section

namespace OMSRArbitrary

variable {n m : ℕ}

/-- **A release** (arXiv:2611.03598, Definition 12, p.18, restated p.40), for the run of PG with
seeds `u` from `(S, s)` on thresholds `z`: the run releases at `τ` if it probes `i` at `τ`, its
best alternative `J = J_τ` exists, and `p_{iτ} < z_τ ≤ p_{Jτ}` (it unsuccessfully probes `i`
although a probe of `J` would have succeeded). PG(u) is the run with `S = univ`, `s = 0`;
Lemma 13 uses general runs. -/
def releasesAt (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (S : Finset (Fin n)) (s : ℕ)
    (z : Seeds m) (i : Fin n) (τ : Fin m) : Prop :=
  pgProbe D g u S s (corrOutcome D z) τ = some i ∧
    ∃ J, bestAlt D g u S s (corrOutcome D z) i τ = some J ∧
      D.probability (i, τ) < z τ ∧ z τ ≤ D.probability (J, τ)

/-- **Condition (i) of Definition F.2** (arXiv:2611.03598, p.40): PG(u) probes `i` at `τ`, a best
alternative `J = J_τ` exists, and `p_{iτ} < p_{Jτ}`. -/
def relCond1 (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m)
    (τ : Fin m) : Prop :=
  pgProbe D g u Finset.univ 0 (corrOutcome D z) τ = some i ∧
    ∃ J, bestAlt D g u Finset.univ 0 (corrOutcome D z) i τ = some J ∧
      D.probability (i, τ) < D.probability (J, τ)

/-- **Condition (ii) of Definition F.2** (arXiv:2611.03598, p.41): in the run of PG(u) in which
`(i, τ)` succeeds, i.e. the run on `z^{(τ)} := (z_{<τ}, 0, z_{>τ})` (p.19), at every arrival
`t > τ` with `(i, t) ∈ E` and `z_t ≤ p_{it}`, PG(u) probes a resource whose reduced price is at
least `r_i p_{it}(1 − g(u))`. -/
def relCond2 (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m)
    (τ : Fin m) : Prop :=
  ∀ t : Fin m, τ < t → (i, t) ∈ D.edges → z t ≤ D.probability (i, t) →
    ∃ k, pgProbe D g u Finset.univ 0 (corrOutcome D (Function.update z τ 0)) t = some k ∧
      D.reward i * D.probability (i, t) * (1 - g (u i)) ≤ reducedPrice D g u k t

/-- **Release arrival with weights** (arXiv:2611.03598, Definition F.2, pp.40–41): conditions (i)
and (ii). -/
def IsReleaseArrival (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m)
    (τ : Fin m) : Prop :=
  relCond1 D g u i z τ ∧ relCond2 D g u i z τ

open Classical in
/-- `a_τ`: the indicator that PG(u) probes `i` at `τ` and `z_τ ≤ p_{iτ}`
(arXiv:2611.03598, App. F.2, p.41). -/
def aInd (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) (τ : Fin m) : ℝ :=
  if pgProbe D g u Finset.univ 0 (corrOutcome D z) τ = some i ∧ z τ ≤ D.probability (i, τ)
  then 1 else 0

open Classical in
/-- **The normalized auxiliary dual** `â_τ` (arXiv:2611.03598, App. F.2, p.41): `p_{iτ}/p_{Jτ}` if
`τ` is a release arrival and `z_τ ≤ p_{Jτ}`; `0` if `τ` is a release arrival and
`z_τ > p_{Jτ}`; `a_τ` otherwise. -/
def aHat (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) (τ : Fin m) : ℝ :=
  if IsReleaseArrival D g u i z τ then
    (match bestAlt D g u Finset.univ 0 (corrOutcome D z) i τ with
      | some J => if z τ ≤ D.probability (J, τ) then D.probability (i, τ) / D.probability (J, τ)
          else 0
      | none => 0)
  else aInd D g u i z τ

end OMSRArbitrary


