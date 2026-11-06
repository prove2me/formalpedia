-- Prove2me | Definitions.Def_UnknownBudgetAdwords_FGPG
-- name    : UnknownBudgetAdwords_FGPG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:06.101702+00:00
-- url     : https://prove2.me/theorems/b703fc76-c3a8-41bf-a04a-e525cd7e50f9
-- title:
--   Fractional GPG (f-GPG), Algorithm 2, its moments, and $\lambda_t$, $\theta_i$
-- statement:
--   **Fractional GPG** is the analysis tool of the paper. It uses the same seeds as GPG but knows the budgets, and matches an arrival fractionally. With $\delta=0$ and $B_j(t-1)$ the remaining budgets, while $\delta<1$ and some resource has positive remaining budget and a positive bid on $t$, it takes such a resource $i^*$ of highest bid price and matches it the fraction
--
--   $$
--   d=\min\Big\{1-\delta,\ \frac{B_{i^*}(t-1)}{b_{i^*,t}}\Big\}.
--   $$
--
--   This defines the fractions $\delta_{j,t}(Y)$, the budget used $\text{f-GPG}_i(Y)=\sum_t b_{i,t}\delta_{i,t}(Y)$ and the reward $\text{f-GPG}(Y)=\sum_i \text{f-GPG}_i(Y)$.
--
--   The paper also views f-GPG in continuous time: arrival $t$ occupies $[t,t+1)$, the resources being served in the order of the passes. At a moment $\tau=t+s$, $I(\tau,Y)$ is the set of resources with positive remaining budget, and
--
--   $$
--   \lambda_\tau(Y)=\max_{j\in I(\tau,Y)}b_{j,t}(1-g(y_j)).
--   $$
--
--   The candidate dual variables are
--
--   $$
--   \lambda_t(Y)=\sum_j b_{j,t}\,\delta_{j,t}(Y)\,(1-g(y_j)),\qquad \theta_i(Y)=\text{f-GPG}_i(Y)\,g(y_i).
--   $$
--
--   Every step of the analysis of Theorem 2 is stated in these objects.
--
--   **Formalization Note** The printed step is $\min\{1,B_{i^*}(t-1)/b_{i^*,t}\}$, which can match more than one whole arrival; the step above is the one the text of p.10 and p.16 describes. `passes` lists the passes of one arrival, with fuel $N$, which suffices because each pass exhausts its resource or completes the arrival. `fractionTo l a s j` is the fraction of the arrival given to $j$ by position $s$, and `remAt` is the remaining budget at a moment. On an empty available set $\lambda_\tau=0$.
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, Algorithm 2, p.10; (4), (5), p.12; p.16

import Definitions.Def_UnknownBudgetAdwords_GPG
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds bestOf maxWithZero)
noncomputable section

namespace UnknownBudgetAdwords

/-- The resources with positive remaining budget `R j` and positive bid `b j`: the set
`I(t) ∩ {i | b_{i,t} > 0}` of Algorithm 2 (Udwani, arXiv:2110.00504v5, Algorithm 2, p.10). -/
def eligible {N : ℕ} (b R : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => 0 < R j ∧ 0 < b j)

/-- The selection rule of Algorithm 2 (Udwani, arXiv:2110.00504v5, Algorithm 2, p.10): the
resource of highest bid price among the eligible ones, `none` if there is none.

**Formalization Note** The printed argmax runs over `I(t)`; restricting it to positive bids, as
the loop guard does, avoids dividing by a zero bid and only differs from the printed rule when
some `y_j = 1`. Ties are broken by least index (probability 0, p.10). -/
def fChoice {N : ℕ} (β : ℝ) (b : Fin N → ℝ) (Y : Seeds N) (R : Fin N → ℝ) : Option (Fin N) :=
  bestOf (price β b Y) ((eligible b R).sort (· ≤ ·))

/-- The passes of the `while` loop of Algorithm 2 for one arrival with bid vector `b`, from
remaining budgets `R` and matched fraction `δ` (Udwani, arXiv:2110.00504v5, Algorithm 2, p.10):
the list of pairs `(i*, d)`, in order, where the pass matches a fraction `d` of the arrival to
`i*`. The first argument after the seeds is fuel.

**Formalization Note** The step is `d = min {1 − δ, R_{i*} / b_{i*,t}}`, correcting the printed
`min {1, B_{i*}(t−1) / b_{i*,t}}`: with budgets `(0.5, 10)` and one arrival with bids `(1, 1)` the
printed step matches `1.5` of one arrival, against "until t is fully (fractionally) matched or no
resource is available" (p.10) and the continuous description of p.16. Each pass exhausts `i*` or
completes the arrival, so `N` passes suffice. -/
def passes {N : ℕ} (β : ℝ) (b : Fin N → ℝ) (Y : Seeds N) :
    ℕ → (Fin N → ℝ) → ℝ → List (Fin N × ℝ)
  | 0, _, _ => []
  | k + 1, R, δ =>
    if δ < 1 then
      match fChoice β b Y R with
      | none => []
      | some j =>
        let d := min (1 - δ) (R j / b j)
        (j, d) :: passes β b Y k (Function.update R j (R j - b j * d)) (δ + d)
    else []

/-- The fraction of an arrival that the passes `l`, starting at position `a` of the unit interval
of the arrival, have matched to `j` by position `s`. Pass `(k, d)` occupies `[a, a + d)`. -/
def fractionTo {N : ℕ} : List (Fin N × ℝ) → ℝ → ℝ → Fin N → ℝ
  | [], _, _, _ => 0
  | (k, d) :: l, a, s, j =>
    (if k = j then max 0 (min d (s - a)) else 0) + fractionTo l (a + d) s j

/-- The remaining budgets `B_j(t−1)` of f-GPG just before arrival `t` (arrivals are
`0, …, M − 1`; `t = M` is the end of the run), Udwani, arXiv:2110.00504v5, Algorithm 2, p.10. -/
def remBefore {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) : ℕ → Fin N → ℝ
  | 0 => I.budget
  | t + 1 =>
    if h : t < M then
      fun j => remBefore I β Y t j - I.bid j ⟨t, h⟩ *
        fractionTo (passes β (fun k => I.bid k ⟨t, h⟩) Y N (remBefore I β Y t) 0) 0 1 j
    else remBefore I β Y t

/-- The passes of Algorithm 2 at arrival `t`, run from `δ = 0` and the remaining budgets just
before `t`, with fuel `N` (Udwani, arXiv:2110.00504v5, Algorithm 2, p.10). -/
def fPasses {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (t : Fin M) : List (Fin N × ℝ) :=
  passes β (fun k => I.bid k t) Y N (remBefore I β Y t) 0

/-- `δ_{j,t}(Y)`: the fraction of arrival `t` matched to `j` by f-GPG on seed `Y`
(Udwani, arXiv:2110.00504v5, p.12). -/
def delta {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (j : Fin N) (t : Fin M) : ℝ :=
  fractionTo (fPasses I β Y t) 0 1 j

/-- The budget of `i` used by f-GPG on seed `Y` before arrival `t`. -/
def fUsedBefore {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (i : Fin N) (t : ℕ) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin M => v.val < t), I.bid i v * delta I β Y i v

/-- `f-GPG_i(Y)`: the total budget of `i` used by f-GPG on seed `Y`
(Udwani, arXiv:2110.00504v5, p.12). -/
def fUsed {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (i : Fin N) : ℝ :=
  fUsedBefore I β Y i M

/-- `f-GPG(Y)`: the total reward of f-GPG on seed `Y`, the sum over `i` and `t` of
`b_{i,t} δ_{i,t}(Y)` (Udwani, arXiv:2110.00504v5, p.15). -/
def fValue {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) : ℝ :=
  ∑ i, fUsed I β Y i

/-- The remaining budget of `j` at moment `t + s`, for `s ∈ [0, 1)`, of the continuous view of
f-GPG (Udwani, arXiv:2110.00504v5, p.16). -/
def remAt {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (t : Fin M) (s : ℝ) (j : Fin N) : ℝ :=
  remBefore I β Y t j - I.bid j t * fractionTo (fPasses I β Y t) 0 s j

/-- `I(τ, Y)`: the resources available at moment `τ = t + s` (Udwani, arXiv:2110.00504v5, p.16).

**Formalization Note** Available means positive remaining budget at the moment, so a resource
exhausted exactly at `τ` is out at `τ`. -/
def availAt {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (t : Fin M) (s : ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter (fun j => 0 < remAt I β Y t s j)

/-- `λ_τ(Y) = max_{j ∈ I(τ, Y)} b_{j,t} (1 − g(y_j))` for `τ = t + s`
(Udwani, arXiv:2110.00504v5, p.16).

**Formalization Note** On an empty available set the value is `0`, the natural value: nothing is
matched and the moment contributes nothing to `λ_t`. For seeds in `[0, 1]` all prices are
nonnegative, so the `0` in `maxWithZero` changes nothing else. -/
def lamAt {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (t : Fin M) (s : ℝ) : ℝ :=
  maxWithZero (((availAt I β Y t s).sort (· ≤ ·)).map (price β (fun j => I.bid j t) Y))

/-- `λ_t(Y) = ∑_j b_{j,t} δ_{j,t}(Y) (1 − g(y_j))`, display (4) for f-GPG
(Udwani, arXiv:2110.00504v5, (4), p.12). -/
def lam {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (t : Fin M) : ℝ :=
  ∑ j, I.bid j t * delta I β Y j t * (1 - g β (Y j))

/-- `θ_i(Y) = f-GPG_i(Y) g(y_i)`, display (5) for f-GPG
(Udwani, arXiv:2110.00504v5, (5), p.12). -/
def theta {N M : ℕ} (I : Instance N M) (β : ℝ) (Y : Seeds N) (i : Fin N) : ℝ :=
  fUsed I β Y i * g β (Y i)

end UnknownBudgetAdwords


