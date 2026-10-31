-- Prove2me | Definitions.Def_CrowdLastMile_Model
-- name    : CrowdLastMile_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:53.319324+00:00
-- url     : https://prove2.me/theorems/84e8d3c6-a752-4019-80bc-971f432613eb
-- title:
--   Problem (14): parameters, constraint families, feasibility and objective
-- statement:
--   The data of the robust crowdsourcing problem: the set size $q\ge1$, the number of drivers $N\ge1$, the integer $\tau^m\ge1$ with $m=\tau^m N$ customer sets and $mq$ crowd customers, and the driver population $\mathbb N\ge N$; the means and standard deviations $\mu^a_\ell,\sigma^a_\ell$ of interarrival times and $\mu^s_\ell,\sigma^s_\ell$ of on-site service times ($\ell=1,\dots,mq$); tour speeds $v_j$ ($j=1,\dots,m$); the tour constant $\beta$; conservatism levels $\gamma^a,\gamma^s,\gamma^k$; the delivery window $\alpha$; the stability slack $\epsilon$; the 3PL fee $c_T$; and the opportunity-cost means $\mu^k_i$ with common standard deviation $\sigma^k$. `Valid` collects the standing sign conditions.
--
--   Write
--
--   $$
--   C_1=\frac{\sum_{i=1}^{mq}\mu^s_i}{m}+\frac{\sum_{i=1}^{m}\beta\sqrt{q+1}/v_i}{m},\qquad C_2=\frac{\sum_{i=1}^{mq}\mu^a_i}{m},\qquad R=\sum_{i=1}^{N}\mu^k_{(i)}+\gamma^k\sqrt N\sigma^k,
--   $$
--
--   and let $C$ be the bracket of the objective,
--
--   $$
--   C=\frac{\sum_{j=1}^m\beta\sqrt{q+1}/v_j+\sum_{j=1}^N\Big(\sum_{i=1}^{\tau^m}\sum_{k=(j_i-1)q+1}^{j_iq}\mu^s_k+\gamma^s\sqrt{\sum_{i=1}^{\tau^m}\sum_{k=(j_i-1)q+1}^{j_iq}(\sigma^s_k)^2}\Big)}{mq},
--   $$
--
--   with $j_i=(i-1)N+j$. A pair $(P,w)$ is feasible for Problem (14) if $0<P\le1$, $w>0$, and:
--
--   1. for $j=N+1,\dots,m$ and $i=1,\dots,a^j$, where $a^j=\lceil j/N\rceil-1$,
--   $$
--   -\sum_{\ell=(j-iN)q+1}^{(j-1)q+1}\frac{\mu^a_\ell}{P}+\gamma^a\sqrt{\sum_{\ell=(j-iN)q+1}^{(j-1)q+1}\Big(\frac{\sigma^a_\ell}{P}\Big)^2}+\sum_{\ell=0}^{i}\sum_{p=(j-\ell N-1)q+1}^{(j-\ell N)q}\mu^s_p+\gamma^s\sqrt{\sum_{\ell=0}^{i}\sum_{p=(j-\ell N-1)q+1}^{(j-\ell N)q}(\sigma^s_p)^2}+\sum_{\ell=0}^{i}\frac{\beta\sqrt{q+1}}{v_{j-\ell N}}\le\alpha;
--   $$
--   2. for $j=1,\dots,m$,
--   $$
--   \sum_{\ell=(j-1)q+2}^{jq}\frac{\mu^a_\ell}{P}+\gamma^a\sqrt{\sum_{\ell=(j-1)q+2}^{jq}\Big(\frac{\sigma^a_\ell}{P}\Big)^2}+\sum_{\ell=(j-1)q+1}^{jq}\mu^s_\ell+\gamma^s\sqrt{\sum_{\ell=(j-1)q+1}^{jq}(\sigma^s_\ell)^2}+\frac{\beta\sqrt{q+1}}{v_j}\le\alpha;
--   $$
--   3. $PC_1/(NC_2)\le1-\epsilon$;
--   4. $wPC_1/(NC_2)\ge R/N$.
--
--   The objective is $Pw\,C+(1-P)c_T$. Constraints 1 and 2 are the on-time delivery conditions, 3 is stability and 4 is participation of the crowd.
--
--   **Formalization Note** The sequences are functions on $\mathbb N$ read on the printed ranges; no out-of-range value occurs. The condition $\max_i\{\dots\}\le\alpha$ of constraint 1 is written for every $i$. Everything is transcribed as printed, with $\mu^a_\ell/P$ and $\sigma^a_\ell/P$ inside the sums and the root.
-- source:
--   Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, §2.1–§2.3, pp.5–12, and eq. (14), p.17; j_i, p.34; a^j, p.15

import Mathlib
import Definitions.Def_CrowdLastMile_sumCheapest

open Finset

namespace CrowdLastMile

/-- The data of the robust crowdsourcing problem. Fatehi–Wagner, Crowdsourcing Last-Mile
Deliveries, SSRN 3434625, §2.1–§2.3, pp.5–12.

* `q` is the set size, `N` the number of participating crowd drivers, and `τm = m/N` the
  (integer, p.9) number of tours per driver, so there are `m = τm * N` sets and `n = m * q`
  crowd customers; `pop` is the driver population size `ℕ ≥ N`.
* `μa ℓ, σa ℓ` are the mean and standard deviation of the interarrival time of customer `ℓ`,
  `μs ℓ, σs ℓ` those of the on-site service time (`ℓ = 1, …, mq`).
* `v j` is the speed on tour `j` (`j = 1, …, m`); `β` is the tour-length constant of p.10.
* `γa, γs, γk` are the levels of conservatism, `α` the delivery window, `ε` the stability slack
  and `cT` the 3PL cost per package.
* `μk i` is the mean opportunity cost of driver `i`, and `σk` the common standard deviation
  (`σ^k_i = σ^k` for all `i`, p.11).

**Formalization Note.** The sequences are functions `ℕ → ℝ` read on the printed 1-based ranges;
values outside those ranges never occur in any definition. Drivers are `Fin pop`. -/
structure Params where
  q : ℕ
  N : ℕ
  τm : ℕ
  pop : ℕ
  hq : 1 ≤ q
  hN : 1 ≤ N
  hτm : 1 ≤ τm
  hpop : N ≤ pop
  μa : ℕ → ℝ
  σa : ℕ → ℝ
  μs : ℕ → ℝ
  σs : ℕ → ℝ
  v : ℕ → ℝ
  β : ℝ
  γa : ℝ
  γs : ℝ
  γk : ℝ
  α : ℝ
  ε : ℝ
  cT : ℝ
  μk : Fin pop → ℝ
  σk : ℝ

namespace Params

variable (p : Params)

/-- The number of customer sets `m = τm * N`. Fatehi–Wagner, SSRN 3434625, p.9. -/
def m : ℕ := p.τm * p.N

/-- The standing assumptions on the data: means of interarrival times are positive, standard
deviations are positive, means of service times and of opportunity costs are nonnegative, `β` and
the speeds are positive, the conservatism levels are nonnegative, `0 < ε < 1` and `cT > 0`.
Fatehi–Wagner, SSRN 3434625, pp.6–12.

**Formalization Note.** `ε` is "smaller than any other number" on p.10; here it is any number in
`(0,1)`. No sign is imposed on `α`. -/
structure Valid : Prop where
  μa_pos : ∀ ℓ ∈ Icc 1 (p.m * p.q), 0 < p.μa ℓ
  σa_pos : ∀ ℓ ∈ Icc 1 (p.m * p.q), 0 < p.σa ℓ
  μs_nonneg : ∀ ℓ ∈ Icc 1 (p.m * p.q), 0 ≤ p.μs ℓ
  σs_pos : ∀ ℓ ∈ Icc 1 (p.m * p.q), 0 < p.σs ℓ
  v_pos : ∀ j ∈ Icc 1 p.m, 0 < p.v j
  β_pos : 0 < p.β
  γa_nonneg : 0 ≤ p.γa
  γs_nonneg : 0 ≤ p.γs
  γk_nonneg : 0 ≤ p.γk
  ε_pos : 0 < p.ε
  ε_lt_one : p.ε < 1
  cT_pos : 0 < p.cT
  μk_nonneg : ∀ i, 0 ≤ p.μk i
  σk_pos : 0 < p.σk

/-- `a^j = ⌈j/N⌉ - 1`, the number of sets formed before set `j` that the same driver serves.
Fatehi–Wagner, SSRN 3434625, p.15.

**Formalization Note.** The ceiling is computed in `ℕ` as `(j + N - 1) / N`. -/
def a (j : ℕ) : ℕ := (j + p.N - 1) / p.N - 1

/-- `j_i = (i - 1) * N + j`, "the `j`th element of the set `J_i`", where
`J_i = {(i-1)N + 1, …, iN}`. Fatehi–Wagner, SSRN 3434625, pp.9, 34. -/
def jIdx (j i : ℕ) : ℕ := (i - 1) * p.N + j

/-- `∑_{i=1}^{mq} μ^s_i / m + ∑_{i=1}^m β√(q+1)/v_i / m`, the mean busy time per set.
Fatehi–Wagner, SSRN 3434625, eq. (14), p.17. -/
noncomputable def C1 : ℝ :=
  (∑ i ∈ Icc 1 (p.m * p.q), p.μs i) / (p.m : ℝ)
    + (∑ i ∈ Icc 1 p.m, p.β * Real.sqrt ((p.q : ℝ) + 1) / p.v i) / (p.m : ℝ)

/-- `∑_{i=1}^{mq} μ^a_i / m`, the mean time for a set to form.
Fatehi–Wagner, SSRN 3434625, eq. (14), p.17. -/
noncomputable def C2 : ℝ := (∑ i ∈ Icc 1 (p.m * p.q), p.μa i) / (p.m : ℝ)

/-- The bound on the value-adding time per package in the objective of Problem (14):
`[∑_{j=1}^m β√(q+1)/v_j + ∑_{j=1}^N (∑_{i=1}^{τm} ∑_{k=(j_i-1)q+1}^{j_i q} μ^s_k
+ γ^s √(∑_{i=1}^{τm} ∑_{k=(j_i-1)q+1}^{j_i q} (σ^s_k)²))] / (mq)`.
Fatehi–Wagner, SSRN 3434625, eq. (14), p.17. -/
noncomputable def C : ℝ :=
  ((∑ j ∈ Icc 1 p.m, p.β * Real.sqrt ((p.q : ℝ) + 1) / p.v j)
    + ∑ j ∈ Icc 1 p.N,
        ((∑ i ∈ Icc 1 p.τm, ∑ k ∈ Icc ((p.jIdx j i - 1) * p.q + 1) (p.jIdx j i * p.q), p.μs k)
          + p.γs * Real.sqrt
              (∑ i ∈ Icc 1 p.τm,
                ∑ k ∈ Icc ((p.jIdx j i - 1) * p.q + 1) (p.jIdx j i * p.q), (p.σs k) ^ 2)))
    / ((p.m : ℝ) * (p.q : ℝ))

/-- `R = ∑_{i=1}^N μ^k_(i) + γ^k √N σ^k`, the numerator of the right-hand side of the participation
constraint. Fatehi–Wagner, SSRN 3434625, Lemma 1, p.12, and eq. (14), p.17. -/
noncomputable def R : ℝ := sumCheapest p.μk p.N + p.γk * Real.sqrt (p.N : ℝ) * p.σk

/-- The expression inside the `max` of the first constraint family of Problem (14), for set `j`
and index `i`, transcribed as printed with `μ^a_ℓ/P` and `σ^a_ℓ/P` inside the sums and the root.
Fatehi–Wagner, SSRN 3434625, eq. (14), p.17. -/
noncomputable def firstTerm (P : ℝ) (j i : ℕ) : ℝ :=
  -(∑ ℓ ∈ Icc ((j - i * p.N) * p.q + 1) ((j - 1) * p.q + 1), p.μa ℓ / P)
    + p.γa * Real.sqrt (∑ ℓ ∈ Icc ((j - i * p.N) * p.q + 1) ((j - 1) * p.q + 1), (p.σa ℓ / P) ^ 2)
    + (∑ ℓ ∈ range (i + 1), ∑ r ∈ Icc ((j - ℓ * p.N - 1) * p.q + 1) ((j - ℓ * p.N) * p.q), p.μs r)
    + p.γs * Real.sqrt
        (∑ ℓ ∈ range (i + 1),
          ∑ r ∈ Icc ((j - ℓ * p.N - 1) * p.q + 1) ((j - ℓ * p.N) * p.q), (p.σs r) ^ 2)
    + ∑ ℓ ∈ range (i + 1), p.β * Real.sqrt ((p.q : ℝ) + 1) / p.v (j - ℓ * p.N)

/-- The first constraint family of Problem (14): for `j = N+1, …, m`, the `max` over
`i = 1, …, a^j` of `firstTerm` is at most `α`.

**Formalization Note.** `max_i {…} ≤ α` is written as `∀ i ∈ {1, …, a^j}, … ≤ α`. -/
def FirstFamily (P : ℝ) : Prop :=
  ∀ j ∈ Icc (p.N + 1) p.m, ∀ i ∈ Icc 1 (p.a j), p.firstTerm P j i ≤ p.α

/-- The left-hand side of the second constraint family of Problem (14), for set `j`.
Fatehi–Wagner, SSRN 3434625, eq. (14), p.17. -/
noncomputable def secondTerm (P : ℝ) (j : ℕ) : ℝ :=
  (∑ ℓ ∈ Icc ((j - 1) * p.q + 2) (j * p.q), p.μa ℓ / P)
    + p.γa * Real.sqrt (∑ ℓ ∈ Icc ((j - 1) * p.q + 2) (j * p.q), (p.σa ℓ / P) ^ 2)
    + (∑ ℓ ∈ Icc ((j - 1) * p.q + 1) (j * p.q), p.μs ℓ)
    + p.γs * Real.sqrt (∑ ℓ ∈ Icc ((j - 1) * p.q + 1) (j * p.q), (p.σs ℓ) ^ 2)
    + p.β * Real.sqrt ((p.q : ℝ) + 1) / p.v j

/-- The second constraint family of Problem (14), for `j = 1, …, m`. -/
def SecondFamily (P : ℝ) : Prop :=
  ∀ j ∈ Icc 1 p.m, p.secondTerm P j ≤ p.α

/-- The third constraint of Problem (14): the utilization `ρ = P C1 / (N C2)` is at most `1 - ε`. -/
def Stability (P : ℝ) : Prop :=
  P * p.C1 / ((p.N : ℝ) * p.C2) ≤ 1 - p.ε

/-- The fourth constraint of Problem (14), the participation constraint:
`w P C1 / (N C2) ≥ (∑_{i=1}^N μ^k_(i) + γ^k √N σ^k) / N`. -/
def Participation (P w : ℝ) : Prop :=
  w * P * p.C1 / ((p.N : ℝ) * p.C2) ≥ p.R / (p.N : ℝ)

/-- Feasibility of `(P, w)` for Problem (14): `P ∈ (0,1]`, `w > 0` and the four constraint families.
Fatehi–Wagner, SSRN 3434625, eq. (14), p.17. -/
structure Feasible (P w : ℝ) : Prop where
  P_pos : 0 < P
  P_le_one : P ≤ 1
  w_pos : 0 < w
  first : p.FirstFamily P
  second : p.SecondFamily P
  stability : p.Stability P
  participation : p.Participation P w

/-- The objective of Problem (14), the worst-case delivery cost rate per package:
`P w C + (1 - P) c_T`. Fatehi–Wagner, SSRN 3434625, eq. (14), p.17. -/
noncomputable def obj (P w : ℝ) : ℝ := P * w * p.C + (1 - P) * p.cT

end Params

end CrowdLastMile


