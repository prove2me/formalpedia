-- Prove2me | Definitions.Def_BoundedParamMDP_Optimal_BMDP
-- name    : BoundedParamMDP_Optimal_BMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:31.055976+00:00
-- url     : https://prove2.me/theorems/631f7e0f-dcd8-4cfe-93f2-8a1190abc591
-- title:
--   Bounded-parameter MDP $M_\updownarrow$, its member MDPs, order-maximizing MDPs, interval values and the orders $\le_{\mathrm{opt}}$, $\le_{\mathrm{pes}}$
-- statement:
--   This file fixes the objects of Section 4 of Givan, Leach and Dean.
--
--   1. **BMDP** (pp. 7–8). A bounded-parameter MDP $M_\updownarrow=\langle Q,A,F_\updownarrow,R_\updownarrow\rangle$ over finite $Q$, $A$ gives, for every $p,q\in Q$ and $\alpha\in A$, a closed interval $F_\updownarrow{}_{pq}(\alpha)=[F_\downarrow{}_{pq}(\alpha),F_\uparrow{}_{pq}(\alpha)]$ with $0\le F_\downarrow\le F_\uparrow\le 1$, such that for every $p,\alpha$
--   $$
--   \sum_{q\in Q}F_\downarrow{}_{pq}(\alpha)\le 1\le\sum_{q\in Q}F_\uparrow{}_{pq}(\alpha).
--   $$
--   Rewards are tight (footnote 3): $R_\updownarrow(q)=[R(q),R(q)]$. The discount rate satisfies $0\le\gamma<1$.
--   2. **Members** (p. 8). An exact MDP $M$ belongs to $M_\updownarrow$ if it has the same states, actions, reward $R$ and discount rate, and $F_\downarrow{}_{pq}(\alpha)\le F^M_{pq}(\alpha)\le F_\uparrow{}_{pq}(\alpha)$ for all $p,q,\alpha$ (each row of $F^M$ being a probability distribution, as for every exact MDP).
--   3. **Order-maximizing MDPs** (Definition 1, p. 9; Definition 2, p. 11). For an ordering $O=q_1,\dots,q_k$ of $Q$ and each $p,\alpha$, let $r$ be the largest index $1\le r\le k$ with
--   $$
--   \sum_{i=1}^{r-1}F_\uparrow{}_{p,q_i}(\alpha)+\sum_{i=r}^{k}F_\downarrow{}_{p,q_i}(\alpha)\le 1. \tag{9}
--   $$
--   The order-maximizing MDP $M_O$ gives $q_j$ the probability $F_\uparrow{}_{pq_j}(\alpha)$ if $j<r$, $F_\downarrow{}_{pq_j}(\alpha)$ if $j>r$, and $q_r$ the remaining mass $1-\sum_{i\ne r}F^{M_O}_{pq_i}(\alpha)$. $X_{M_\updownarrow}$ is the finite set of the $M_O$, one per ordering.
--   4. **Interval values** (Definition 3, p. 12). For a policy $\pi$ and state $q$,
--   $$
--   V_\updownarrow{}_\pi(q)=\Big[\min_{M\in M_\updownarrow}V_{M,\pi}(q),\ \max_{M\in M_\updownarrow}V_{M,\pi}(q)\Big]=\big[V_\downarrow{}_\pi(q),V_\uparrow{}_\pi(q)\big].
--   $$
--   5. **$\pi$-maximizing and $\pi$-minimizing MDPs** (Definition 4, p. 12): $M\in M_\updownarrow$ with $V_{M,\pi}\ge_{\mathrm{dom}}V_{M',\pi}$ (resp. $\le_{\mathrm{dom}}$) for every $M'\in M_\updownarrow$.
--   6. **MDP composition** (Definition 5, p. 14). $M_1\oplus^\pi_{\max}M_2$ takes the transition row of $M_1$ at $(p,\alpha)$ if $V_{M_1,\pi}(p)\ge V_{M_2,\pi}(p)$ and $\alpha=\pi(p)$, and the row of $M_2$ otherwise; $\oplus^\pi_{\min}$ uses $\le$ instead.
--   7. **Interval orders** (eq. (17), p. 16):
--   $$
--   [l_1,u_1]\le_{\mathrm{pes}}[l_2,u_2]\iff l_1<l_2\ \text{or}\ (l_1=l_2\wedge u_1\le u_2),\qquad [l_1,u_1]\le_{\mathrm{opt}}[l_2,u_2]\iff u_1<u_2\ \text{or}\ (u_1=u_2\wedge l_1\le l_2),
--   $$
--   extended to interval value functions statewise.
--   8. **Optimal policies** (Definition 6, p. 16): $\pi_{\mathrm{opt}}$ is optimistically optimal if $V_\updownarrow{}_{\pi_{\mathrm{opt}}}\ge_{\mathrm{opt}}V_\updownarrow{}_\pi$ for all $\pi\in\Pi$; pessimistically optimal likewise with $\ge_{\mathrm{pes}}$.
--   9. **Policy composition** (Definition 7, eqs. (18)–(19), p. 16): $(\pi_1\oplus_{\mathrm{opt}}\pi_2)(p)=\pi_1(p)$ if $V_\updownarrow{}_{\pi_1}(p)\ge_{\mathrm{opt}}V_\updownarrow{}_{\pi_2}(p)$ and $\pi_2(p)$ otherwise; $\oplus_{\mathrm{pes}}$ likewise with $\ge_{\mathrm{pes}}$.
--
--   These are the objects of the paper's optimality theory: the interval value of a policy, the two orders that rank intervals, and the composition operators from which the existence of optimal policies is built.
--
--   **Formalization Note** Rewards are tight, as the paper assumes from footnote 3 on; reward intervals are not formalized. A member of $M_\updownarrow$ is an element of the subtype `Member B` of exact MDPs with the BMDP's $R$ and $\gamma$ and transition probabilities inside the boxes; it is nonempty for every BMDP, which is a theorem, not a field. The minimum and maximum of Definition 3 are written as the real infimum `⨅` and supremum `⨆` over `Member B`; the values are bounded by $\max_q|R(q)|/(1-\gamma)$, and that they are attained is Corollary 1. Intervals are pairs (lower bound, upper bound). An ordering $O$ is a bijection `Fin k ≃ Q`, $k=|Q|$, with 0-based positions ($q_{i+1}=O(i)$); the index $r$ of (9) is the **largest** index for which (9) does not exceed 1 (several indices can tie when $F_\downarrow=F_\uparrow$ for some state, and only the largest one keeps the remaining mass of $q_r$ within $[F_\downarrow,F_\uparrow]$). Where the page writes $F_\uparrow{}_{pq_i}$, $F_\downarrow{}_{pq_i}$ in the cases of Definition 1 it means $q_j$. Order-maximizing MDPs and compositions are given by their transition functions (`orderMaxF`, `XM`, `composeMaxF`, `composeMinF`); "$M\in X_{M_\updownarrow}$" is formalized as a member whose transition function lies in `XM`. "$V_\updownarrow{}_{\pi_1}\ge_{\mathrm{opt}}V_\updownarrow{}_{\pi_2}$" is `optLE` with the arguments swapped.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, pp. 7–16, Section 4, footnote 3, Definitions 1–7, eqs. (9), (12), (17)–(19)

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP

open Classical

namespace BoundedParamMDP.Optimal

/-- A bounded-parameter MDP `M↕ = ⟨Q, A, F↕, R↕⟩` (Section 4, pp. 7–8) over finite `Q`, `A`,
with tight rewards (footnote 3, p. 8: `R↕(q) = [R(q), R(q)]`) and discount rate `0 ≤ γ < 1`.
`lo p α q` and `hi p α q` are the bounds `F↓_{pq}(α) ≤ F↑_{pq}(α)` of the closed interval
`F↕_{pq}(α) ⊆ [0, 1]`; for every `p, α` the lower bounds sum to at most `1` and the upper
bounds to at least `1`. -/
structure BMDP (Q A : Type*) [Fintype Q] where
  /-- the lower bound `F↓_{pq}(α)` -/
  lo : Q → A → Q → ℝ
  /-- the upper bound `F↑_{pq}(α)` -/
  hi : Q → A → Q → ℝ
  /-- the (tight) reward `R(q)` -/
  R : Q → ℝ
  /-- the discount rate `γ` -/
  γ : ℝ
  lo_nonneg : ∀ p α q, 0 ≤ lo p α q
  lo_le_hi : ∀ p α q, lo p α q ≤ hi p α q
  hi_le_one : ∀ p α q, hi p α q ≤ 1
  sum_lo_le_one : ∀ p α, ∑ q, lo p α q ≤ 1
  one_le_sum_hi : ∀ p α, 1 ≤ ∑ q, hi p α q
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

/-- The exact MDPs `M ∈ M↕` (p. 8): exact MDPs over `Q, A` with the BMDP's reward and
discount rate whose transition probabilities lie in the intervals,
`F↓_{pq}(α) ≤ F^M_{pq}(α) ≤ F↑_{pq}(α)`. -/
abbrev Member {Q A : Type*} [Fintype Q] (B : BMDP Q A) : Type _ :=
  {M : MDP Q A // M.R = B.R ∧ M.γ = B.γ ∧
    ∀ p α q, B.lo p α q ≤ M.F p α q ∧ M.F p α q ≤ B.hi p α q}

/-- Expression (9) of Definition 1 (p. 9) for the ordering `O` (positions `0, …, k-1`,
i.e. `q_{i+1} = O i` on the page) and a 0-based index `r`: the upper bounds at the positions
before `r` plus the lower bounds at the positions from `r` on. -/
noncomputable def orderSum {Q A : Type*} [Fintype Q] (B : BMDP Q A)
    (O : Fin (Fintype.card Q) ≃ Q) (p : Q) (α : A) (r : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card Q), if (i : ℕ) < r then B.hi p α (O i) else B.lo p α (O i)

/-- The index `r` of Definition 1 (p. 9), 0-based: the largest position `r ≤ k - 1` at which
expression (9) does not exceed `1` (it holds at `r = 0`, since the lower bounds sum to at
most `1`). -/
noncomputable def orderIndex {Q A : Type*} [Fintype Q] (B : BMDP Q A)
    (O : Fin (Fintype.card Q) ≃ Q) (p : Q) (α : A) : ℕ :=
  Nat.findGreatest (fun r => orderSum B O p α r ≤ 1) (Fintype.card Q - 1)

/-- The transition function of the order-maximizing MDP `M_O` (Definition 1, p. 9): the
state at position `j` of `O` gets `F↑` if `j < r`, `F↓` if `j > r`, and the state at
position `r` gets the remaining mass `1 - ∑_{i ≠ r} F^{M_O}_{p q_i}(α)`. -/
noncomputable def orderMaxF {Q A : Type*} [Fintype Q] (B : BMDP Q A)
    (O : Fin (Fintype.card Q) ≃ Q) : Q → A → Q → ℝ :=
  fun p α q =>
    let r := orderIndex B O p α
    let j : ℕ := O.symm q
    if j < r then B.hi p α q
    else if r < j then B.lo p α q
    else 1 - ∑ i : Fin (Fintype.card Q),
      (if (i : ℕ) < r then B.hi p α (O i) else if r < (i : ℕ) then B.lo p α (O i) else 0)

/-- `X_{M↕}` (Definition 2, p. 11): the transition functions of the order-maximizing MDPs,
one for each ordering `O` of `Q`. An MDP `M` lies in `X_{M↕}` when `M.F ∈ XM B`. -/
def XM {Q A : Type*} [Fintype Q] (B : BMDP Q A) : Set (Q → A → Q → ℝ) :=
  Set.range (orderMaxF B)

/-- The lower bound `V↓π(q) = min_{M ∈ M↕} V_{M,π}(q)` of the interval value (Definition 3,
eq. (12), p. 12), as an infimum over the members of `M↕`. -/
noncomputable def lowerV {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A)
    (π : Policy Q A) : Q → ℝ :=
  fun q => ⨅ M : Member B, value M.1 π q

/-- The upper bound `V↑π(q) = max_{M ∈ M↕} V_{M,π}(q)` of the interval value (Definition 3,
eq. (12), p. 12), as a supremum over the members of `M↕`. -/
noncomputable def upperV {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A)
    (π : Policy Q A) : Q → ℝ :=
  fun q => ⨆ M : Member B, value M.1 π q

/-- The interval value `V↕π(q) = [V↓π(q), V↑π(q)]` (Definition 3), as the pair
(lower bound, upper bound). -/
noncomputable def intervalV {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A)
    (π : Policy Q A) : Q → ℝ × ℝ :=
  fun q => (lowerV B π q, upperV B π q)

/-- `M ∈ M↕` is `π`-maximizing (Definition 4, p. 12): `V_{M,π} ≥_dom V_{M',π}` for all
`M' ∈ M↕`. -/
def IsPiMax {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A) (π : Policy Q A)
    (M : Member B) : Prop :=
  ∀ M' : Member B, value M'.1 π ≤ value M.1 π

/-- `M ∈ M↕` is `π`-minimizing (Definition 4, p. 12): `V_{M,π} ≤_dom V_{M',π}` for all
`M' ∈ M↕`. -/
def IsPiMin {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A) (π : Policy Q A)
    (M : Member B) : Prop :=
  ∀ M' : Member B, value M.1 π ≤ value M'.1 π

/-- The transition function of `M₁ ⊕^π_max M₂` (Definition 5, p. 14): the row of `M₁` at
`(p, α)` if `V_{M₁,π}(p) ≥ V_{M₂,π}(p)` and `α = π(p)`, the row of `M₂` otherwise. -/
noncomputable def composeMaxF {Q A : Type*} [Fintype Q] [DecidableEq Q] (π : Policy Q A)
    (M₁ M₂ : MDP Q A) : Q → A → Q → ℝ :=
  fun p α q =>
    if value M₂ π p ≤ value M₁ π p ∧ α = π p then M₁.F p α q else M₂.F p α q

/-- The transition function of `M₁ ⊕^π_min M₂` (Definition 5, p. 14): the row of `M₁` at
`(p, α)` if `V_{M₁,π}(p) ≤ V_{M₂,π}(p)` and `α = π(p)`, the row of `M₂` otherwise. -/
noncomputable def composeMinF {Q A : Type*} [Fintype Q] [DecidableEq Q] (π : Policy Q A)
    (M₁ M₂ : MDP Q A) : Q → A → Q → ℝ :=
  fun p α q =>
    if value M₁ π p ≤ value M₂ π p ∧ α = π p then M₁.F p α q else M₂.F p α q

/-- The pessimistic order on closed intervals `[l, u]`, written as pairs `(l, u)` (eq. (17),
p. 16): `[l₁, u₁] ≤_pes [l₂, u₂] ⇔ l₁ < l₂ ∨ (l₁ = l₂ ∧ u₁ ≤ u₂)`. -/
def pesLE (I J : ℝ × ℝ) : Prop :=
  I.1 < J.1 ∨ (I.1 = J.1 ∧ I.2 ≤ J.2)

/-- The optimistic order on closed intervals `[l, u]`, written as pairs `(l, u)` (eq. (17),
p. 16): `[l₁, u₁] ≤_opt [l₂, u₂] ⇔ u₁ < u₂ ∨ (u₁ = u₂ ∧ l₁ ≤ l₂)`. -/
def optLE (I J : ℝ × ℝ) : Prop :=
  I.2 < J.2 ∨ (I.2 = J.2 ∧ I.1 ≤ J.1)

/-- An optimistically optimal policy (Definition 6, p. 16): `V↕π_opt ≥_opt V↕π` for every
policy `π`, the order being extended to interval value functions statewise. -/
def IsOptOptimal {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A)
    (πo : Policy Q A) : Prop :=
  ∀ (π : Policy Q A) (q : Q), optLE (intervalV B π q) (intervalV B πo q)

/-- A pessimistically optimal policy (Definition 6, p. 16): `V↕π_pes ≥_pes V↕π` for every
policy `π`, statewise. -/
def IsPesOptimal {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A)
    (πp : Policy Q A) : Prop :=
  ∀ (π : Policy Q A) (q : Q), pesLE (intervalV B π q) (intervalV B πp q)

/-- The policy composition `π₁ ⊕_opt π₂` (Definition 7, eq. (18), p. 16):
`π₁(p)` if `V↕π₁(p) ≥_opt V↕π₂(p)`, `π₂(p)` otherwise. -/
noncomputable def composeOpt {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A)
    (π₁ π₂ : Policy Q A) : Policy Q A :=
  fun p => if optLE (intervalV B π₂ p) (intervalV B π₁ p) then π₁ p else π₂ p

/-- The policy composition `π₁ ⊕_pes π₂` (Definition 7, eq. (19), p. 16):
`π₁(p)` if `V↕π₁(p) ≥_pes V↕π₂(p)`, `π₂(p)` otherwise. -/
noncomputable def composePes {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A)
    (π₁ π₂ : Policy Q A) : Policy Q A :=
  fun p => if pesLE (intervalV B π₂ p) (intervalV B π₁ p) then π₁ p else π₂ p

end BoundedParamMDP.Optimal


