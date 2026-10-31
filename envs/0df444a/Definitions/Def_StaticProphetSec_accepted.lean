-- Prove2me | Definitions.Def_StaticProphetSec_accepted
-- name    : StaticProphetSec_accepted
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:55.37211+00:00
-- url     : https://prove2.me/theorems/7eacd7cc-c2c8-453f-8031-e95ceb6e8e24
-- title:
--   The static threshold policy $(t,p)$: eligible applicants, demand and the accepted set
-- statement:
--   Consider $n$ applicants with values $V=(V_1,\dots,V_n)$, a threshold $t$, and coins $B=(B_1,\dots,B_n)$. Applicant $i$ is **eligible** when $V_i>t$, or when $V_i=t$ and $B_i$ shows heads. **Demand** $D$ is the number of eligible applicants; with no ties it is $D^t(V)=\sum_i\mathbb 1(V_i>t)$.
--
--   Given an arrival order $\sigma$, the policy processes the applicants $\sigma(0),\sigma(1),\dots$ in turn. It accepts the arriving applicant exactly when that applicant is eligible and fewer than $k$ applicants have been accepted so far. The **accepted set** is the outcome of this procedure, so the policy accepts the first $k$ eligible arrivals.
--
--   **Formalization Note** The paper flips the coin of a tied applicant when items remain and the applicant is considered. Here every coin is drawn in advance. The two have the same law, because each coin is read at most once and is independent of all other randomness.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, p.2 (policy), (3) p.15 (demand), Remark 1 p.5 (tie-breaking)

import Mathlib

namespace StaticProphetSec

/-- The eligible applicants of the static threshold policy `(t, p)` (Arnosti & Ma,
arXiv:2108.12893v2, p.2 and Remark 1, p.5): applicant `i` is eligible when `V i > t`, or when
`V i = t` and its tie-break coin `B i` shows heads.

**Formalization Note.** The paper flips the coin of a tied applicant when items remain and that
applicant is considered. Here each applicant's coin is drawn in advance and independently of all
other randomness (`B : Fin n → Bool`), which has the same law, because a coin is read at most
once and is independent of everything else. -/
noncomputable def eligibleSet {n : ℕ} (t : ℝ) (V : Fin n → ℝ) (B : Fin n → Bool) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => t < V i ∨ (V i = t ∧ B i = true)

/-- Demand at threshold `t`, equation (3) (Arnosti & Ma, arXiv:2108.12893v2, (3), p.15): the
number of eligible applicants. When no coin shows heads, or no value equals `t`, this is
`∑ i, 𝟙(V i > t)`. -/
noncomputable def demand {n : ℕ} (t : ℝ) (V : Fin n → ℝ) (B : Fin n → Bool) : ℕ :=
  (eligibleSet t V B).card

/-- The sequential procedure behind a static threshold policy, for a given set `E` of eligible
applicants: applicants arrive in the order `σ 0, σ 1, …`, and the arriving applicant is accepted
exactly when it is in `E` and fewer than `k` applicants have been accepted so far. The result is
the set of accepted applicants. -/
def acceptedFrom {n : ℕ} (k : ℕ) (E : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n) :=
  (List.finRange n).foldl
    (fun S m => if σ m ∈ E ∧ S.card < k then insert (σ m) S else S) ∅

/-- The set of applicants accepted by the static threshold policy `(t, p)` with `k` items on
values `V`, coins `B` and arrival order `σ` (Arnosti & Ma, arXiv:2108.12893v2: "accept the first
k applicants whose value exceeds t", p.2; tie-breaking, Remark 1, p.5). `σ m` is the applicant
arriving in position `m`. -/
noncomputable def accepted {n : ℕ} (k : ℕ) (t : ℝ) (V : Fin n → ℝ) (B : Fin n → Bool)
    (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  acceptedFrom k (eligibleSet t V B) σ

end StaticProphetSec


