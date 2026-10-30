-- Prove2me | Definitions.Def_VehShare_SeqBounds_gen
-- name    : VehShare_SeqBounds_gen
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:37:12.05824+00:00
-- url     : https://prove2.me/theorems/d9b54fdf-44be-4a06-be92-b01d6d661541
-- title:
--   Generator of the closed queueing network
-- statement:
--   Under the accepted fractions $q$, the system is a closed queueing network with single-server pick-up queues at the locations and infinite-server transit queues for the pairs (p. 5). Its generator $Q$ acts on $f:S\to\mathbb R$ by
--
--   $$
--   (Qf)(x)=\sum_{i,j}\Lambda_{ij}q_{ij}(x)\Big[\big(1-\textstyle\sum_s\beta_{ij}(s)\big)\big(f(x^{i\to j})-f(x)\big)+\sum_s\beta_{ij}(s)\big(f(x^{i\to(ij,s)})-f(x)\big)\Big]
--   +\sum_{i,j}\sum_{s\neq s'}x_{ij,s}\,r_{ij}(s,s')\big(f(x^{(ij,s)\to(ij,s')})-f(x)\big)
--   +\sum_{i,j}\sum_s x_{ij,s}\,e_{ij}(s)\big(f(x^{(ij,s)\to j})-f(x)\big),
--   $$
--
--   where $x^{a\to b}$ moves one vehicle from slot $a$ to slot $b$:
--
--   1. **pick-up**: a customer for $i\to j$ arrives at rate $\Lambda_{ij}$, accepts with probability $q_{ij}(x)$ and takes a vehicle at $i$, which enters stage $s$ with probability $\beta_{ij}(s)$ (or arrives at $j$ at once);
--   2. **stage move**: each of the $x_{ij,s}$ vehicles in stage $s$ moves to stage $s'$ at rate $r_{ij}(s,s')$;
--   3. **drop-off**: each of them completes its trip at rate $e_{ij}(s)$ and joins location $j$.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §2, pp. 4–5 (unnumbered)

import Mathlib
import Definitions.Def_VehShare_SeqBounds_move

namespace VehShare.SeqBounds

/-- **Generator of the closed queueing network under the prices `q`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §2, pp. 4–5 (unnumbered): "the system ... can be modeled as a closed queueing network with two
types of queues: single server queues associated with each location (modeling the vehicle pickup
process) and infinite server queues associated with each pair of locations (modeling the vehicle
travel process)".

`gen q f z` is `(Q f)(z)` for the rate matrix `Q` with these transitions out of `z`:
1. pick-up: at rate `Λ_ij q_ij(z)` a customer for `i → j` takes a vehicle at `i`; the vehicle enters
   stage `s` of the transit queue `(i, j)` with probability `β_ij(s)`, or arrives at `j` at once with
   probability `1 − ∑_s β_ij(s)` (single server: the rate does not depend on the number of vehicles);
2. stage move: each of the `z(i,j,s)` vehicles in stage `s` moves to stage `s' ≠ s` at rate
   `r_ij(s, s')` (infinite server);
3. drop-off: each of them completes the trip at rate `e_ij(s)` and joins location `j`.

**Formalization Note.** A pick-up out of an empty location never has positive rate for a policy
(`q = 0` there), and the other two rates carry the factor `z(i,j,s)`; so `move`'s convention on an
empty source slot is never used. -/
noncomputable def gen {P : Instance} {K : ℕ} (q : State P K → P.L → P.L → ℝ)
    (f : State P K → ℝ) (z : State P K) : ℝ :=
  (∑ i, ∑ j, P.Λ i j * q z i j *
      ((1 - ∑ s, P.β i j s) * (f (move z (Sum.inl i) (Sum.inl j)) - f z)
        + ∑ s, P.β i j s * (f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)) - f z)))
  + (∑ i, ∑ j, ∑ s, ∑ s', if s = s' then 0 else
        (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
          (f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩)) - f z))
  + ∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
        (f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j)) - f z)

end VehShare.SeqBounds


