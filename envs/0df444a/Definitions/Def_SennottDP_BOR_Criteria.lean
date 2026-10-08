-- Prove2me | Definitions.Def_SennottDP_BOR_Criteria
-- name    : SennottDP_BOR_Criteria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T10:48:58.066891+00:00
-- url     : https://prove2.me/theorems/c9ae1db2-c5bf-40c0-9635-3ec6fc91297b
-- title:
--   Discounted and average costs, relative values $h_\alpha$, the (SEN) assumptions, limit functions and the ACOI/ACOE
-- statement:
--   Fix an MDC $\Delta$ and a policy $\theta$. Starting from $X_0=i$, $\theta$ determines the law of the states and actions $(X_t,A_t)$. For $\alpha\in(0,1)$ the **expected discounted cost**, the **discount value function**, the **average cost** and the **minimum average cost** are
--   $$
--   V_{\theta,\alpha}(i)=\sum_{t\ge0}\alpha^tE_\theta[C(X_t,A_t)\mid X_0=i],\quad V_\alpha(i)=\inf_\theta V_{\theta,\alpha}(i),\quad J_\theta(i)=\limsup_{n\to\infty}\frac1n\sum_{t=0}^{n-1}E_\theta[C(X_t,A_t)\mid X_0=i],\quad J(i)=\inf_\theta J_\theta(i),
--   $$
--   all in $[0,\infty]$, infima over all policies. A policy is **average cost optimal** if $J_\theta=J$.
--
--   For a distinguished state $z$ the **relative value** is $h_\alpha(i)=V_\alpha(i)-V_\alpha(z)$. The **(SEN) assumptions** (p. 132) are:
--
--   1. (SEN1) $(1-\alpha)V_\alpha(z)$ is bounded for $\alpha\in(0,1)$;
--   2. (SEN2) there is a nonnegative finite function $M$ with $h_\alpha(i)\le M(i)$ for all $i$ and $\alpha\in(0,1)$;
--   3. (SEN3) there is a nonnegative finite constant $L$ with $-L\le h_\alpha(i)$ for all $i$ and $\alpha\in(0,1)$.
--
--   A function $h:S\to\mathbb R$ is a **limit function** (Definition 7.2.2(i)) if $V_\alpha(z)<\infty$ for $\alpha\in(0,1)$ and $h(i)=\lim_n h_{\beta_n}(i)$ for all $i$ along some sequence $\beta_n\to1^-$. For a constant $J$ and a function $h$, the **average cost optimality inequality** (ACOI) and **equation** (ACOE) are
--   $$
--   J+h(i)\ \ge\ \min_{a\in A_i}\Big\{C(i,a)+\sum_jP_{ij}(a)h(j)\Big\}\quad\text{resp.}\quad J+h(i)=\min_{a\in A_i}\Big\{C(i,a)+\sum_jP_{ij}(a)h(j)\Big\},\qquad i\in S.
--   $$
--   A stationary policy $e$ **realizes the minimum** if $e(i)$ attains the minimum at every $i$, and its **discrepancy function** $\Phi$ is defined by $J+h(i)=C(i,e)+\Phi(i)+\sum_jP_{ij}(e)h(j)$ (7.28).
--
--   **Formalization Note** Costs and values live in `ℝ≥0∞`; $h_\alpha$ is taken in `EReal` (it is only used when $V_\alpha(z)<\infty$). The discount factor is a real $\alpha$ entering through `ENNReal.ofReal`. $\sum_jP_{ij}(a)h(j)$ is the `EReal` difference of the $[0,\infty]$-valued sums of the positive and negative parts of $h$; for $h$ bounded below (every limit function under (SEN)) the negative part is finite, so the value lies in $(-\infty,+\infty]$ as in the book. The (SEN) predicate is stated with the function $M$ and the constant $L$ explicit (`SENWith`) and existentially (`SEN`).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 26–27, (2.13)–(2.16); p. 132, (SEN1)–(SEN3); p. 134, Definition 7.2.2(i); p. 135, (7.9); p. 139, ACOE; p. 142, (7.28)

import Mathlib
import Definitions.Def_SennottDP_BOR_MDC

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

variable {S : Type} [Countable S] {Act : Type}

open Classical in
/-- Sennott (1999), §2.3, pp. 22–23: the probability, under policy `θ` and initial state `i`,
of the history `h_n = (s 0, as 0, s 1, …, as (n-1), s n)`:
`P_θ(X_0 = s 0, A_0 = as 0, …, X_n = s n | X_0 = i)`. It is `1_{s 0 = i}` for `n = 0`; each
further step multiplies by the action probability `θ(a_n | h_n)` and the transition probability
`P_{i_n i_{n+1}}(a_n)`. -/
noncomputable def histProb {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) :
    (n : ℕ) → (Fin (n + 1) → S) → (Fin n → Act) → ℝ≥0∞
  | 0, s, _ => if s 0 = i then 1 else 0
  | n + 1, s, as =>
      histProb θ i n (Fin.init s) (Fin.init as) *
        θ.dist n (Fin.init s) (Fin.init as) (as (Fin.last n)) *
        M.P (s (Fin.castSucc (Fin.last n))) (as (Fin.last n)) (s (Fin.last (n + 1)))

/-- The expected cost at time `t` of history `h_t`, averaged over the action chosen at time `t`:
`∑_{a ∈ A_{i_t}} θ(a | h_t) C(i_t, a)`. -/
noncomputable def stepCost {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (t : ℕ) (s : Fin (t + 1) → S)
    (as : Fin t → Act) : ℝ≥0∞ :=
  ∑ a ∈ M.A (s (Fin.last t)), θ.dist t s as a * (M.C (s (Fin.last t)) a : ℝ≥0∞)

/-- Sennott (1999), (2.6), p. 23: the expected cost at time `t`,
`E_θ[C(X_t, A_t) | X_0 = i]`, a value in `[0, ∞]`. -/
noncomputable def expCost {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (t : ℕ) : ℝ≥0∞ :=
  ∑' s : Fin (t + 1) → S, ∑' as : Fin t → Act, histProb θ i t s as * stepCost θ t s as

/-- Sennott (1999), (2.13), p. 26: the expected discounted cost
`V_{θ,α}(i) = ∑_{t ≥ 0} α^t E_θ[C(X_t,A_t) | X_0 = i]` in `[0, ∞]`; the discount factor
`α ∈ (0,1)` is a real number, entering through `ENNReal.ofReal`. -/
noncomputable def discCost {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ENNReal.ofReal α ^ t * expCost θ i t

/-- Sennott (1999), (2.14), p. 26: the discount value function `V_α(i) = inf_θ V_{θ,α}(i)`,
the infimum over all general policies. -/
noncomputable def valueFn (M : SennottDP.Discounted.MDC S Act) (α : ℝ) (i : S) : ℝ≥0∞ :=
  ⨅ θ : SennottDP.Discounted.Policy M, discCost θ α i

/-- The `n`-horizon expected cost with terminal cost `0` (p. 128),
`v_{θ,n}(i) = ∑_{t=0}^{n-1} E_θ[C(X_t,A_t) | X_0 = i]`. -/
noncomputable def horizonCost {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (n : ℕ) (i : S) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, expCost θ i t

/-- Sennott (1999), (2.15), p. 27: the average cost `J_θ(i) = limsup_{n→∞} v_{θ,n}(i)/n`,
in `[0, ∞]`. -/
noncomputable def avgCost {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) : ℝ≥0∞ :=
  limsup (fun n : ℕ => horizonCost θ n i / (n : ℝ≥0∞)) atTop

/-- Sennott (1999), (2.16), p. 27: the minimum average cost `J(i) = inf_θ J_θ(i)` over all
general policies. -/
noncomputable def avgValue (M : SennottDP.Discounted.MDC S Act) (i : S) : ℝ≥0∞ :=
  ⨅ θ : SennottDP.Discounted.Policy M, avgCost θ i

/-- Sennott (1999), Definition 2.4.5: `θ` is average cost optimal if `J_θ(i) = J(i)` for all
`i`. -/
def IsAvgOptimal {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) : Prop :=
  ∀ i, avgCost θ i = avgValue M i

/-- Sennott (1999), p. 132: the relative value function `h_α(i) = V_α(i) − V_α(z)`, taken in the
extended reals. It is used only when `V_α(z) < ∞` (then it lies in `(−∞, +∞]`). -/
noncomputable def relValue (M : SennottDP.Discounted.MDC S Act) (z : S) (α : ℝ) (i : S) : EReal :=
  (valueFn M α i : EReal) - (valueFn M α z : EReal)

/-- Sennott (1999), (SEN1), p. 132: `(1 − α) V_α(z)` is bounded for `α ∈ (0,1)`. -/
def SEN1 (M : SennottDP.Discounted.MDC S Act) (z : S) : Prop :=
  ∃ B : ℝ≥0, ∀ α : ℝ, 0 < α → α < 1 → ENNReal.ofReal (1 - α) * valueFn M α z ≤ B

/-- Sennott (1999), (SEN2), p. 132, for a given function `Mf`: `Mf ≥ 0` is finite and
`h_α(i) ≤ Mf(i)` for all `i ∈ S` and `α ∈ (0,1)`. -/
def SEN2 (M : SennottDP.Discounted.MDC S Act) (z : S) (Mf : S → ℝ) : Prop :=
  (∀ i, 0 ≤ Mf i) ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ i, relValue M z α i ≤ (Mf i : EReal)

/-- Sennott (1999), (SEN3), p. 132, for a given constant `L`: `L ≥ 0` is finite and
`−L ≤ h_α(i)` for all `i ∈ S` and `α ∈ (0,1)`. -/
def SEN3 (M : SennottDP.Discounted.MDC S Act) (z : S) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ i, ((-L : ℝ) : EReal) ≤ relValue M z α i

/-- Sennott (1999), p. 132: the (SEN) assumptions for the distinguished state `z`, with the
function `Mf` of (SEN2) and the constant `L` of (SEN3) made explicit. -/
def SENWith (M : SennottDP.Discounted.MDC S Act) (z : S) (Mf : S → ℝ) (L : ℝ) : Prop :=
  SEN1 M z ∧ SEN2 M z Mf ∧ SEN3 M z L

/-- Sennott (1999), p. 132: the (SEN) assumptions hold for the distinguished state `z`. -/
def SEN (M : SennottDP.Discounted.MDC S Act) (z : S) : Prop :=
  ∃ Mf : S → ℝ, ∃ L : ℝ, SENWith M z Mf L

/-- Sennott (1999), Definition 7.2.2(i), p. 134: `h : S → ℝ` is a limit function (for the
distinguished state `z`): `V_α(z) < ∞` for all `α ∈ (0,1)`, and there is a sequence
`β_n ∈ (0,1)` with `β_n → 1⁻` (a subsequence of some `α_n → 1⁻`) such that
`lim_n h_{β_n}(i) = h(i)` for every `i ∈ S`. -/
def IsLimitFunction (M : SennottDP.Discounted.MDC S Act) (z : S) (h : S → ℝ) : Prop :=
  (∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤) ∧
  ∃ β : ℕ → ℝ, (∀ n, 0 < β n ∧ β n < 1) ∧ Tendsto β atTop (𝓝 1) ∧
    ∀ i, Tendsto (fun n => relValue M z (β n) i) atTop (𝓝 (h i : EReal))

/-- The expectation `∑_j P_{ij}(a) h(j)` of a real function `h` after one transition, in the
extended reals: the positive part `∑_j P_{ij}(a) h(j)^+ ∈ [0, ∞]` minus the negative part
`∑_j P_{ij}(a) h(j)^- ∈ [0, ∞]`. When `h` is bounded below (as every limit function under (SEN)
is) the negative part is finite and the value lies in `(−∞, +∞]`, the book's convention. -/
noncomputable def nextExp (M : SennottDP.Discounted.MDC S Act) (h : S → ℝ) (i : S) (a : Act) : EReal :=
  ((∑' j, M.P i a j * ENNReal.ofReal (h j) : ℝ≥0∞) : EReal) -
    ((∑' j, M.P i a j * ENNReal.ofReal (-h j) : ℝ≥0∞) : EReal)

/-- The right side of the ACOI (7.9), p. 135: `min_{a ∈ A_i} {C(i,a) + ∑_j P_{ij}(a) h(j)}`. -/
noncomputable def acoiRHS (M : SennottDP.Discounted.MDC S Act) (h : S → ℝ) (i : S) : EReal :=
  (M.A i).inf' (M.A_nonempty i) (fun a => (M.C i a : EReal) + nextExp M h i a)

/-- A stationary policy `e` realizes the minimum in (7.9) (equivalently in the ACOE) for `h`:
`C(i,e(i)) + ∑_j P_{ij}(e) h(j) = min_a {C(i,a) + ∑_j P_{ij}(a) h(j)}` for every `i ∈ S`. -/
def RealizesMin (M : SennottDP.Discounted.MDC S Act) (h : S → ℝ) (e : StationaryPolicy M) : Prop :=
  ∀ i, (M.C i (e.1 i) : EReal) + nextExp M h i (e.1 i) = acoiRHS M h i

/-- Sennott (1999), §7.4, p. 139: the average cost optimality equation (ACOE) for the constant `J`
and the function `h`: (7.9) with equality at every state,
`J + h(i) = min_a {C(i,a) + ∑_j P_{ij}(a) h(j)}`, `i ∈ S`. -/
def ACOE (M : SennottDP.Discounted.MDC S Act) (J : ℝ) (h : S → ℝ) : Prop :=
  ∀ i, ((J + h i : ℝ) : EReal) = acoiRHS M h i

/-- Sennott (1999), (7.28), p. 142: the discrepancy function `Φ` of a stationary policy `e`,
defined by `J + h(i) = C(i,e) + Φ(i) + ∑_j P_{ij}(e) h(j)`, i.e.
`Φ(i) = J + h(i) − (C(i,e) + ∑_j P_{ij}(e) h(j))` (in the extended reals). -/
noncomputable def discrepancy (M : SennottDP.Discounted.MDC S Act) (J : ℝ) (h : S → ℝ) (e : StationaryPolicy M)
    (i : S) : EReal :=
  ((J + h i : ℝ) : EReal) - ((M.C i (e.1 i) : EReal) + nextExp M h i (e.1 i))

end SennottDP.BOR


