-- Prove2me | Definitions.Def_SurgeAppt_FirstAvail_Model
-- name    : SurgeAppt_FirstAvail_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:56.426251+00:00
-- url     : https://prove2.me/theorems/37e539b8-73f5-43e8-8b96-abb633a9f645
-- title:
--   §3 and (5), pp. 6–12 — appointment-scheduling MDP: book, admissible actions (1), binomial transition (4), cost (7), FA policy, value (9), condition (13)
-- statement:
--   This file sets up the infinite-horizon discounted dynamic program of Grant, Gurvich, Mutharasan and Van Mieghem for booking preventative appointments into base and surge capacity (§3, pp. 6–11, with the surge cost structure (5) of §4), together with the quantities (12), (15), (16) and (13) of Proposition 1.
--
--   **Parameters and standing assumptions.** A scheduling horizon $D \ge 1$; base capacity $K_b$ and surge capacity $K_s$ per period, with total capacity $K = K_b + K_s$; a surge cost $c_s \ge 0$ per surge appointment and a failure cost $c_F > 0$; a per-period failure probability $p_F \in (0,1)$, with $p_{\bar F} = 1-p_F$; a show probability $p_S\in[0,1]$, with $p_{\bar S} = 1-p_S$; post-appointment failure probabilities $p_{F|S}, p_{F|\bar S}\in[0,1]$ with $p_{F|S} < p_{F|\bar S}$; a discount factor $\beta\in(0,1)$; and i.i.d. arrivals $A$ with law $\mathbb P(A=a) = p_A(a)$ supported on $\{0,\dots,M\}$, $M \ge 1$.
--
--   **States.** An appointment book $\mathbf S = (S_0,\dots,S_D)$, where $S_d$ is the number of appointments booked $d$ periods ahead. A (pre-action) state is valid if $S_d \le K$ for all $d$ and $S_D = 0$.
--
--   **Actions (1).** With $a$ requests, an action $\mathbf u = (u_0,\dots,u_D)$ is admissible if $u_0 = 0$, $u_d + S_d \le K$ for $1\le d\le D$ and $\sum_{d=1}^D u_d = a$. When no such action exists ($a > \sum_{d=1}^D (K - S_d)$) the action is forced: $u_d + S_d = K$ for every $1 \le d\le D$, and the $n_O = \max\{a - \sum_d u_d, 0\}$ overflow requests leave the system.
--
--   **Transitions (2)–(4).** The post-action book is $\tilde{\mathbf S} = \mathbf S + \mathbf u$, and the next book $\mathbf S'$ has probability
--
--   $$
--   \mathbb P(\mathbf S'\mid\tilde{\mathbf S}) = \prod_{d=0}^{D-1}\binom{\tilde S_{d+1}}{S'_d}\,p_{\bar F}^{S'_d}\,(1-p_{\bar F})^{\tilde S_{d+1}-S'_d}\quad\text{if } S'_D = 0,\qquad 0 \text{ otherwise}.
--   $$
--
--   **Cost (5), (7).** With $h(x) = c_s\max\{x - K_b, 0\}$ and the failure count $F_{\mathbf S,\mathbf S'} = \sum_{d=0}^{D-1}(S_{d+1} - S'_d)$ when $\mathbb P(\mathbf S'\mid\mathbf S)>0$ (and $0$ otherwise), the expected one-period cost is
--
--   $$
--   g(\mathbf S, a, \mathbf u) = h(S_0) + \beta c_F\sum_{\mathbf S'}\mathbb P(\mathbf S'\mid\tilde{\mathbf S})\,F_{\tilde{\mathbf S},\mathbf S'} + S_0\, c_F\,(p_Sp_{F|S} + p_{\bar S}p_{F|\bar S}) + c_F\, n_O .
--   $$
--
--   **Policies and value (9)–(10).** A policy is a sequence of decision rules $U^t(\mathbf S, a)$; it is admissible if every decision at a valid state with $a\le M$ lies in (1). Its value from $\mathbf S^0$ is $V_\pi(\mathbf S^0) = \sum_{t\ge0}\beta^t\,\mathbb E[g(\mathbf S^t, A^t, U^t(\mathbf S^t, A^t))]$, and $V^*$ is the infimum over admissible policies. The **First-Available (FA)** rule books the $a$ requests into periods $1, 2, \dots, D$ in order, filling every free slot of a period before using the next.
--
--   **Proposition 1's quantities.** The discounted failure probability (bracket of (12)) $\varphi(d) = \sum_{l=0}^{d-1}\beta^{l+1}p_Fp_{\bar F}^l + \beta^dp_{\bar F}^d(p_Sp_{F|S} + p_{\bar S}p_{F|\bar S})$, the bounds (15) $c_sp_{\bar F}^d\beta^d + c_F\varphi(d)$ and (16) $c_F\varphi(d)$, and condition (13):
--
--   $$
--   \frac{c_s}{c_F}\le \big(p_{\bar F}^{d'-d}\beta^{d'-d}-1\big)\big(p_Sp_{F|S}+p_{\bar S}p_{F|\bar S}\big) + \frac{\sum_{i=d}^{d'-1}\beta^{i+1}p_Fp_{\bar F}^i}{p_{\bar F}^d\beta^d}\qquad\text{for all } 1\le d<d'\le D .
--   $$
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Books are functions $\{0,\dots,D\}\to\mathbb N$ indexed as on the page. Policies are Markov deterministic and possibly non-stationary ($U^t$ depends on $t$, the current book and the current arrivals); history-dependent and randomized policies are not modelled. The value is a `tsum` (see `MarkovCost`). The binomial coefficient vanishes when $S'_d > \tilde S_{d+1}$, so the truncated natural-number exponent there is harmless, and $n_O$ uses truncated subtraction, which is $\max\{\cdot,0\}$. The hypotheses $D\ge1$, $c_s\ge0$, $c_F>0$, $0<p_F<1$ and the ranges of the probabilities are added (they are implicit on the page: (13) divides by $c_F$ and by $p_{\bar F}^d\beta^d$). Condition (13)'s minimum over pairs is written as "for every pair", which is vacuous when $D = 1$. $V^*$ is an infimum of real numbers; it is meaningful because values are nonnegative and FA is admissible.
-- source:
--   Grant, Gurvich, Mutharasan & Van Mieghem, Optimal dynamic appointment scheduling of base and surge capacity, SSRN 3092667 (revised July 1, 2020), pp. 6–12, §3 (1)–(4), (7), (9), (10), (5), (12), (13), (15), (16)

import Mathlib
import Definitions.Def_SurgeAppt_FirstAvail_MarkovCost

namespace SurgeAppt.FirstAvail

/-- The data of the appointment-scheduling model of §3 (pp. 6–11): scheduling horizon `D`, base
capacity `Kb`, surge capacity `Ks`, arrival bound `M`, surge cost `cs`, failure cost `cF`,
per-period failure probability `pF`, show probability `pS`, post-appointment failure probabilities
`pFS` (= p_{F|S}) and `pFSbar` (= p_{F|S̄}), discount factor `β`, and the arrival law
`pA a = P(A = a)`. -/
structure Params where
  D : ℕ
  Kb : ℕ
  Ks : ℕ
  M : ℕ
  cs : ℝ
  cF : ℝ
  pF : ℝ
  pS : ℝ
  pFS : ℝ
  pFSbar : ℝ
  β : ℝ
  pA : ℕ → ℝ

/-- Total capacity per period, `K = Kb + Ks` (p. 11). -/
def Params.K (P : Params) : ℕ := P.Kb + P.Ks

/-- `p_F̄ = 1 − p_F` (p. 7). -/
def Params.pFbar (P : Params) : ℝ := 1 - P.pF

/-- `p_S̄ = 1 − p_S` (p. 8). -/
def Params.pSbar (P : Params) : ℝ := 1 - P.pS

/-- `p_S p_{F|S} + p_S̄ p_{F|S̄}`, the probability of a failure after the appointment period. -/
def Params.cpost (P : Params) : ℝ := P.pS * P.pFS + P.pSbar * P.pFSbar

/-- The standing assumptions of §3–§4: `D ≥ 1`; `M` a positive integer with `P(A ≤ M) = 1`;
`cs ≥ 0`, `cF > 0`; `0 < pF < 1`; `pS, pFS, pFSbar ∈ [0,1]` with `pFS < pFSbar` (p. 8);
`β ∈ (0,1)` (p. 9); `pA` a probability law on `{0, …, M}`. -/
def Params.Standing (P : Params) : Prop :=
  1 ≤ P.D ∧ 0 < P.M ∧ 0 ≤ P.cs ∧ 0 < P.cF ∧ 0 < P.pF ∧ P.pF < 1 ∧
  0 ≤ P.pS ∧ P.pS ≤ 1 ∧ 0 ≤ P.pFS ∧ P.pFS ≤ 1 ∧ 0 ≤ P.pFSbar ∧ P.pFSbar ≤ 1 ∧
  P.pFS < P.pFSbar ∧ 0 < P.β ∧ P.β < 1 ∧
  (∀ a, 0 ≤ P.pA a) ∧ (∀ a, P.M < a → P.pA a = 0) ∧
  ∑ a ∈ Finset.range (P.M + 1), P.pA a = 1

/-- An appointment book `S = (S_0, …, S_D)`: `S d` appointments booked for `d` periods ahead. -/
abbrev Book (P : Params) := Fin (P.D + 1) → ℕ

/-- A (pre-action) state: every period holds at most `K` appointments and `S_D = 0`. -/
def Valid (P : Params) (s : Book P) : Prop :=
  (∀ d, s d ≤ P.K) ∧ s (Fin.last P.D) = 0

/-- The finite set of valid states. -/
def validStates (P : Params) : Finset (Book P) :=
  (Fintype.piFinset fun _ => Finset.range (P.K + 1)).filter (fun s => s (Fin.last P.D) = 0)

/-- Free slots in period `d` of the book `s` (none in period `0`: same-period booking is not
allowed). -/
def free (P : Params) (s : Book P) (d : Fin (P.D + 1)) : ℕ :=
  if d = 0 then 0 else P.K - s d

/-- The set (1) is nonempty: the `a` requests fit in the free slots of periods `1, …, D`. -/
def Feasible (P : Params) (s : Book P) (a : ℕ) : Prop :=
  a ≤ ∑ d, free P s d

/-- Admissible actions (1), p. 7: `u_0 = 0`, `u_d + S_d ≤ K` for `1 ≤ d ≤ D`, and `∑_d u_d = a`;
when (1) is empty the action is forced: `u_d + S_d = K` for every `1 ≤ d ≤ D`. -/
def Admissible (P : Params) (s : Book P) (a : ℕ) (u : Book P) : Prop :=
  u 0 = 0 ∧ (∀ d, d ≠ 0 → u d + s d ≤ P.K) ∧
  ((Feasible P s a → ∑ d, u d = a) ∧ (¬ Feasible P s a → ∀ d, d ≠ 0 → u d + s d = P.K))

/-- The number of overflow appointments `n_O = max{a − ∑_d u_d, 0}` (p. 7). -/
def overflow {P : Params} (a : ℕ) (u : Book P) : ℕ := a - ∑ d, u d

/-- The transition probability (4), p. 7, from the post-action book `St = S̃` to the next pre-action
book `s'`: `∏_{d=0}^{D-1} C(S̃_{d+1}, s'_d) p_F̄^{s'_d} (1 − p_F̄)^{S̃_{d+1} − s'_d}` if `s'_D = 0`,
and `0` otherwise. -/
def trans (P : Params) (St s' : Book P) : ℝ :=
  if s' (Fin.last P.D) = 0 then
    ∏ d : Fin P.D, ((St d.succ).choose (s' d.castSucc) : ℝ) * P.pFbar ^ (s' d.castSucc)
      * (1 - P.pFbar) ^ (St d.succ - s' d.castSucc)
  else 0

/-- The failure count `F_{S,S'} = ∑_{d=0}^{D-1} (S_{d+1} − S'_d)` if `P(S'|S) > 0`, else `0` (p. 9). -/
noncomputable def failCount (P : Params) (St s' : Book P) : ℝ :=
  if 0 < trans P St s' then ∑ d : Fin P.D, ((St d.succ : ℝ) - s' d.castSucc) else 0

/-- The appointment cost function (5), p. 8: `h(x) = c_s max{x − K_b, 0}`. -/
def hcost (P : Params) (x : ℕ) : ℝ := P.cs * max ((x : ℝ) - P.Kb) 0

/-- The expected one-period cost (7), p. 9, in state `s` with `a` requests and action `u`:
`h(S_0) + β c_F ∑_{S'} P(S'|S̃) F_{S̃,S'} + S_0 c_F (p_S p_{F|S} + p_S̄ p_{F|S̄}) + c_F n_O`,
with `S̃ = s + u` (2). -/
noncomputable def cost (P : Params) (s : Book P) (a : ℕ) (u : Book P) : ℝ :=
  hcost P (s 0)
  + P.β * P.cF * ∑ s' ∈ validStates P, trans P (s + u) s' * failCount P (s + u) s'
  + (s 0 : ℝ) * P.cF * P.cpost
  + P.cF * overflow a u

/-- The First-Available action: the `a` requests fill the free slots of periods `1, 2, …, D` in
order, a period being filled completely before the next is used. -/
def faAction (P : Params) (s : Book P) (a : ℕ) : Book P := fun d =>
  min (free P s d) (a - ∑ d' ∈ Finset.univ.filter (fun d' => d' < d), free P s d')

/-- A Markov deterministic (possibly non-stationary) policy `π = {U^0, U^1, …}`: at time `t` the
action is `U^t(S^t, A^t) = π t S^t A^t`. -/
def Policy (P : Params) : Type := ℕ → Book P → ℕ → Book P

/-- A policy is admissible if every decision it takes at a valid state, for `a ≤ M` requests,
lies in (1) (p. 10). -/
def IsAdmissible (P : Params) (π : Policy P) : Prop :=
  ∀ t s a, Valid P s → a ≤ P.M → Admissible P s a (π t s a)

/-- The First-Available policy. -/
def faPolicy (P : Params) : Policy P := fun _ => faAction P

/-- One-step transition probability from `s` to `s'` under the decision rule `r`, averaging over
the arrivals `A ∼ pA`. -/
def stepKernel (P : Params) (r : Book P → ℕ → Book P) (s s' : Book P) : ℝ :=
  ∑ a ∈ Finset.range (P.M + 1), P.pA a * trans P (s + r s a) s'

/-- Expected one-period cost in state `s` under the decision rule `r`, averaging over `A ∼ pA`. -/
noncomputable def stageCost (P : Params) (r : Book P → ℕ → Book P) (s : Book P) : ℝ :=
  ∑ a ∈ Finset.range (P.M + 1), P.pA a * cost P s a (r s a)

/-- The value (9), p. 10: `V_π(S^0) = ∑_{t ≥ 0} β^t E[g_t(S^t, U^t(S^t, A^t))]` for `S^0 = s₀`. -/
noncomputable def value (P : Params) (π : Policy P) (s₀ : Book P) : ℝ :=
  discountedCost (validStates P) (fun t => stepKernel P (π t)) (fun t => stageCost P (π t)) P.β s₀

/-- The optimal value function (10), p. 10: the infimum of `V_π(s)` over admissible policies. -/
noncomputable def optValue (P : Params) (s : Book P) : ℝ :=
  ⨅ π : {π : Policy P // IsAdmissible P π}, value P π.1 s

/-- The right-hand side of the Bellman equation for a given `V`, at state `s`, with `a` requests and
action `u`: `g(s, u) + β ∑_{s'} P(s'|s + u) V(s')`. -/
noncomputable def qValue (P : Params) (V : Book P → ℝ) (s : Book P) (a : ℕ) (u : Book P) : ℝ :=
  cost P s a u + P.β * ∑ s' ∈ validStates P, trans P (s + u) s' * V s'

/-- The bracket of (12), p. 11: `∑_{l=0}^{d-1} β^{l+1} p_F p_F̄^l + β^d p_F̄^d (p_S p_{F|S} + p_S̄ p_{F|S̄})`. -/
def phi (P : Params) (d : ℕ) : ℝ :=
  ∑ l ∈ Finset.range d, P.β ^ (l + 1) * P.pF * P.pFbar ^ l + P.β ^ d * P.pFbar ^ d * P.cpost

/-- The upper bound (15), p. 12: `c_s p_F̄^d β^d + c_F (p_F̄^d β^d (…) + ∑_{l<d} β^{l+1} p_F p_F̄^l)`. -/
def upper (P : Params) (d : ℕ) : ℝ := P.cs * P.pFbar ^ d * P.β ^ d + P.cF * phi P d

/-- The lower bound (16), p. 12: `c_F (p_F̄^d β^d (…) + ∑_{l<d} β^{l+1} p_F p_F̄^l)`. -/
def lower (P : Params) (d : ℕ) : ℝ := P.cF * phi P d

/-- The `(d, d')` term of the right-hand side of (13), p. 12:
`(p_F̄^{d'-d} β^{d'-d} − 1)(p_S p_{F|S} + p_S̄ p_{F|S̄}) + (∑_{i=d}^{d'-1} β^{i+1} p_F p_F̄^i) / (p_F̄^d β^d)`. -/
noncomputable def rhs13 (P : Params) (d d' : ℕ) : ℝ :=
  (P.pFbar ^ (d' - d) * P.β ^ (d' - d) - 1) * P.cpost
  + (∑ i ∈ Finset.Ico d d', P.β ^ (i + 1) * P.pF * P.pFbar ^ i) / (P.pFbar ^ d * P.β ^ d)

/-- Condition (13), p. 12: `c_s / c_F ≤ rhs13 d d'` for every pair `1 ≤ d < d' ≤ D`. -/
def Condition13 (P : Params) : Prop :=
  ∀ d d' : ℕ, 1 ≤ d → d < d' → d' ≤ P.D → P.cs / P.cF ≤ rhs13 P d d'

end SurgeAppt.FirstAvail


