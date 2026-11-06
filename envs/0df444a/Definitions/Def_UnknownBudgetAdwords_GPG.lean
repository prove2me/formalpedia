-- Prove2me | Definitions.Def_UnknownBudgetAdwords_GPG
-- name    : UnknownBudgetAdwords_GPG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:45.595341+00:00
-- url     : https://prove2.me/theorems/6a9245d0-6fa8-4a9b-ac14-f0badd2bf554
-- title:
--   Generalized Perturbed Greedy (GPG), Algorithm 1
-- statement:
--   **Generalized Perturbed Greedy** is a randomized online algorithm for Adwords that never reads a budget. Fix $\beta>0$ and let $g(x)=e^{\beta(x-1)}$. Each resource $i$ draws a seed $y_i$, i.i.d. uniform on $[0,1]$. When arrival $t$ appears, with bids $(b_{i,t})_i$, the algorithm matches it to
--
--   $$
--   i^*=\arg\max_{i\in I} b_{i,t}\,(1-g(y_i)),
--   $$
--
--   where $I$ is the set of resources not yet known to be out of budget, and removes $i^*$ from $I$ if $i^*$ has just run out of budget. The quantity $b_{i,t}(1-g(y_i))$ is the **randomized bid price**. The reward of a resource is what it paid, capped at its budget.
--
--   This is the algorithm of the mission's goal theorem. Its budget obliviousness is what separates it from the MSVV algorithm: the bid prices depend on bids and seeds alone, and budgets are learned only when one is used up.
--
--   **Formalization Note** The selection rule `gpgChoice` takes the bids of the arrival, the seeds and the available set, so a budget cannot enter it. The only test that reads a budget is the removal in `gpgStep`, which is the revelation of p.7. Ties, of probability 0, are broken by least index. Arrivals are `Fin M`, so arrival $t$ of the paper is index $t-1$. The reward `gpgReward` is `revenue` of the resulting allocation, with $r_i=1$ without loss of generality (p.7).
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Algorithm 1, p.9; OBA model, p.7

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_Spend
import Definitions.Def_StochasticRewardMatching_Decomposable_Seeds
import Definitions.Def_StochasticRewardMatching_Decomposable_FiniteChoice
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds bestOf)
noncomputable section

namespace UnknownBudgetAdwords

/-- The function `g(x) = e^{β(x−1)}` of Algorithm 1 (Udwani, arXiv:2110.00504v5, Algorithm 1, p.9).

**Formalization Note** This is the paper's one-parameter family; the `g` of
`StochasticRewardMatching.Decomposable` is the case `β = 1` and is not used. -/
def g (β x : ℝ) : ℝ := Real.exp (β * (x - 1))

/-- The randomized bid price `b_j (1 − g(y_j))` of resource `j` for the bid vector `b` of one
arrival and the seed vector `Y` (Udwani, arXiv:2110.00504v5, Algorithm 1, p.9). -/
def price {N : ℕ} (β : ℝ) (b : Fin N → ℝ) (Y : Seeds N) (j : Fin N) : ℝ :=
  b j * (1 - g β (Y j))

/-- The selection rule `i* = argmax_{i ∈ S} b_{i,t} (1 − g(y_i))` of Algorithm 1
(Udwani, arXiv:2110.00504v5, Algorithm 1, p.9): `none` on an empty available set `S`.

**Formalization Note** The rule receives the bids of the arrival, the seeds and the available set
and nothing else, so no budget can enter it. The paper fixes no tie rule, because ties have
probability 0 (p.9); here the least index among the maximizers is taken. -/
def gpgChoice {N : ℕ} (β : ℝ) (b : Fin N → ℝ) (Y : Seeds N) (S : Finset (Fin N)) :
    Option (Fin N) :=
  bestOf (price β b Y) (S.sort (· ≤ ·))

/-- The state of GPG: the set of resources not yet revealed to be out of budget, and the
allocation so far. -/
abbrev GPGState (N M : ℕ) := Finset (Fin N) × Allocation N M

/-- One iteration of the loop of Algorithm 1 at arrival `t` (Udwani, arXiv:2110.00504v5,
Algorithm 1, p.9): match `t` to `j = gpgChoice …`, and remove `j` from the available set exactly
when its capped spend has reached its budget.

**Formalization Note** That test is the only place a budget is read, and it is the revelation of
p.7: "capacity of a resource is revealed right after it is used up". -/
def gpgStep {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (st : GPGState N M) (t : Fin M) :
    GPGState N M :=
  match gpgChoice β (fun j => I.bid j t) Y st.1 with
  | none => st
  | some j =>
    let σ := Function.update st.2 t (some j)
    (if I.budget j ≤ assignedBefore I σ j (t.val + 1) then st.1.erase j else st.1, σ)

/-- The state of GPG just before arrival `t` (arrivals are `0, …, M − 1`; `t = M` is the end of
the run), starting from all resources available and nothing matched. -/
def gpgState {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) : ℕ → GPGState N M
  | 0 => (Finset.univ, fun _ => none)
  | t + 1 =>
    if h : t < M then gpgStep I β Y (gpgState I β Y t) ⟨t, h⟩ else gpgState I β Y t

/-- The matching `GPG(Y)` output by Algorithm 1 on seed `Y` (Udwani, arXiv:2110.00504v5,
Algorithm 1, p.9). -/
def gpgAlloc {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) : Allocation N M :=
  (gpgState I β Y M).2

/-- The total reward `GPG(Y)` of Algorithm 1 on seed `Y` (Udwani, arXiv:2110.00504v5, p.12).

**Formalization Note** Per-unit rewards are `1` without loss of generality (p.7). The reward is
`revenue`, the capped reward of p.7, because an available resource has spend below its budget, so
that paying up to the remaining budget adds exactly what `spend` adds. -/
def gpgReward {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) : ℝ :=
  revenue I (gpgAlloc I β Y)

end UnknownBudgetAdwords


