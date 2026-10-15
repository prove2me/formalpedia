-- Prove2me | Definitions.Def_VehicleSharePricing_Static_Availability
-- name    : VehicleSharePricing_Static_Availability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:31.005526+00:00
-- url     : https://prove2.me/theorems/0a3c441e-0525-4bef-959f-8de72df83c61
-- title:
--   p. 6, (3) — availability $\alpha_i$ under a static policy (BCMP product form) and the reward rate $R(q)$
-- statement:
--   Under a static policy $q$, the system with $K$ vehicles is a closed queueing network (p. 5) with two kinds of stations:
--
--   1. a **pick-up queue** at each location $i$: a single-server station with service rate $\lambda_i=\sum_j\Lambda_{ij}q_{ij}$, which sends a departing vehicle to the transit queue $(i,j)$ with probability $\lambda_{ij}/\lambda_i$;
--   2. a **transit queue** for each ordered pair $(i,j)$: an infinite-server station with mean time $1/\mu_{ij}$, which sends a vehicle on to location $j$.
--
--   Given a positive solution $r$ of the traffic equations (9), the relative loads are $r_i/\lambda_i$ at pick-up queue $i$ and $r_i\lambda_{ij}/(\lambda_i\mu_{ij})$ at transit queue $(i,j)$, so the product-form weight of a state $x$ (vehicle counts at every location and in every transit queue, total $K$) is
--   $$w(x)=\prod_{i}\Bigl(\frac{r_i}{\lambda_i}\Bigr)^{x_i}\prod_{(i,j)}\frac{1}{x_{ij}!}\Bigl(\frac{r_i\lambda_{ij}}{\lambda_i\mu_{ij}}\Bigr)^{x_{ij}}.$$
--   The **availability** at location $i$ with $K$ vehicles is the probability that at least one vehicle is waiting there:
--   $$\alpha_i(K)=\frac{\sum_{x:\,x_i\ge 1}w(x)}{\sum_x w(x)}.$$
--   The expected reward rate of the static policy, equation (3), is
--   $$R(q)=\sum_{(i,j)\in\mathcal A}\alpha_i\,\Lambda_{ij}q_{ij}I_{ij}(q_{ij}).$$
--
--   The paper states that the network "belongs to the class of BCMP networks" (p. 6) and does not write the stationary law; this file makes it explicit as the BCMP product form (Baskett et al. 1975). It is a **definition**, not a theorem of the mission. The availabilities are not assumed to be equal: that is the first milestone.
--
--   **Formalization Note** Every ordered pair $(i,j)$ has a transit queue; a pair with $\lambda_{ij}=0$ has load $0$ and never holds a vehicle. $R$ takes the throughput vector $r$ and the number of vehicles $K$ as arguments; the product form does not depend on the scale of $r$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 5 (closed queueing network of pick-up and transit queues), p. 6 (equation (3), α_i = Σ_{x: x_i>0} π(x), BCMP networks), p. 23 (Appendix, equations (9))

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_ClosedNetwork
import Definitions.Def_VehicleSharePricing_Static_Model

namespace VehicleSharePricing.Static

open Finset

variable {L : Type*} [Fintype L]

/-- Stations of the closed queueing network induced by a static policy (p. 5): one pick-up
queue per location (`Sum.inl i`) and one transit queue per ordered pair (`Sum.inr (i, j)`). -/
abbrev Station (L : Type*) := L ⊕ (L × L)

/-- Relative loads of the stations, given throughputs `r` solving (9): `r_i / λ_i` at the
single-server pick-up queue `i` (service rate `λ_i`), and `r_i λ_ij / (λ_i μ_ij)` at the
infinite-server transit queue `(i,j)` (visit ratio `r_i λ_ij / λ_i`, mean time `1/μ_ij`).
Pairs with `λ_ij = 0` get load `0`, so their transit queue stays empty. -/
noncomputable def stationLoad (P : Instance L) (q : L → L → ℝ) (r : L → ℝ) :
    Station L → ℝ
  | Sum.inl i => r i / outRate P q i
  | Sum.inr (i, j) => r i * effRate P q i j / (outRate P q i * P.rate i j)

/-- Pick-up queues are single-server stations, transit queues are infinite-server stations. -/
def stationIsIS : Station L → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

/-- Availability `α_i` at location `i` with `K` vehicles under the static policy `q` (p. 6):
the BCMP product-form probability that the pick-up queue at `i` holds at least one vehicle. -/
noncomputable def availability [DecidableEq L] (P : Instance L) (q : L → L → ℝ) (r : L → ℝ)
    (K : ℕ) (i : L) : ℝ :=
  pfBusyProb (stationLoad P q r) stationIsIS K (Sum.inl i)

/-- Expected reward rate (3), p. 6, of the static policy `q` with `K` vehicles:
`R(q) = ∑_{(i,j)∈𝒜} α_i Λ_ij q_ij I_ij(q_ij)`. -/
noncomputable def R [DecidableEq L] (P : Instance L) (q : L → L → ℝ) (r : L → ℝ) (K : ℕ) : ℝ :=
  ∑ i, ∑ j, availability P q r K i * P.demand i j * q i j * P.reward i j (q i j)

end VehicleSharePricing.Static


