-- Prove2me | Definitions.Def_SennottDP_BOR_FirstPassage
-- name    : SennottDP_BOR_FirstPassage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T11:01:43.533246+00:00
-- url     : https://prove2.me/theorems/94dbc691-3602-4a19-a3d2-46b3a6e3f98a
-- title:
--   First passage classes $\Re(i,G)$, $\Re^*(i,G)$, recurrence, communicating classes and $z$ standard policies
-- statement:
--   Let $\theta$ be a policy, $i$ an initial state and $G$ a nonempty set of states. The **first passage time** to $G$ is $T=\min\{n\ge1: X_n\in G\}$ ($T=\infty$ if there is no such $n$); note $T\ge1$ even when $i\in G$. The **expected first passage time** $m_{iG}(\theta)=E_\theta[T\mid X_0=i]$ equals $\infty$ when $P_\theta(T<\infty\mid X_0=i)<1$, and the **expected first passage cost** is
--   $$
--   c_{iG}(\theta)=E_\theta\Big[\sum_{t=0}^{T-1}C(X_t,A_t)\,\Big|\,X_0=i\Big]\in[0,\infty].
--   $$
--   $\Re(i,G)$ is the class of policies with $P_\theta(X_n\in G\text{ for some }n\ge1\mid X_0=i)=1$ and $m_{iG}(\theta)<\infty$; $\Re^*(i,G)\subseteq\Re(i,G)$ adds $c_{iG}(\theta)<\infty$; $\Re(i,x)=\Re(i,\{x\})$.
--
--   For a (randomized) stationary policy these are the notions of the Markov chain it induces, and the file defines: $i$ **leads to** $j$ ($P(X_t=j\mid X_0=i)>0$ for some $t\ge0$); **communicating** states and the communicating class of $z$; **recurrent** states (return to $j$ with probability one) and **positive recurrent** states (in addition $m_{jj}<\infty$); the **steady state probability** $\pi_j=(m_{jj})^{-1}$ ($=0$ if $m_{jj}=\infty$); the Cesàro averages
--   $$
--   Q^{(n)}_{ij}=\frac1n\sum_{t=0}^{n-1}P(X_t=j\mid X_0=i)\qquad\text{(C.1)};
--   $$
--   and **$z$ standard** chains (Definition C.2.5): $m_{iz}<\infty$ and $c_{iz}<\infty$ for all $i\in S$. By Definition 7.5.1 a (randomized) stationary policy is a $z$ standard policy if the chain it induces is $z$ standard.
--
--   **Formalization Note** All probabilities and expectations are computed from the history probabilities of the process under $\theta$ (sums over state and action sequences), valued in `ℝ≥0∞`. The cost of the chain induced by a randomized stationary policy $d$ at $i$ is $\sum_a d(a\mid i)C(i,a)$, which is what $c_{iz}$ computed for the policy counts. The book notes $\pi_j=\lim_nQ^{(n)}_{jj}$; the definition uses the equal quantity $(m_{jj})^{-1}$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 139–140; pp. 293–295, (C.1); p. 298; p. 301, Definition C.2.5; p. 143, Definition 7.5.1

import Mathlib
import Definitions.Def_SennottDP_BOR_Criteria

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

variable {S : Type} [Countable S] {Act : Type}

/-! First passages and Markov chain notions (Sennott 1999, pp. 139–140 and App. C.1–C.2,
pp. 292–301), stated for the process driven by a general policy `θ` from `X_0 = i`. For a
(randomized) stationary policy they are the notions for the Markov chain it induces. The first
passage time to a nonempty set `G` is `T = min {n ≥ 1 : X_n ∈ G}` (`T ≥ 1`, p. 295), with
`T = ∞` if `G` is never entered at a time `n ≥ 1`. -/

open Classical in
/-- `P_θ(X_t = j | X_0 = i)`. -/
noncomputable def stateProb {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (t : ℕ) (j : S) : ℝ≥0∞ :=
  ∑' s : Fin (t + 1) → S, ∑' as : Fin t → Act,
    if s (Fin.last t) = j then histProb θ i t s as else 0

open Classical in
/-- `P_θ(T = t, X_t = j | X_0 = i)` for the first passage time `T` to `G`: `t ≥ 1`, the states
`X_1, …, X_{t-1}` lie outside `G`, and `X_t = j ∈ G`. It is `0` for `t = 0`. -/
noncomputable def firstPassHit {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (G : Set S) (t : ℕ)
    (j : S) : ℝ≥0∞ :=
  if t = 0 then 0 else
    ∑' s : Fin (t + 1) → S, ∑' as : Fin t → Act,
      if (∀ k : Fin (t + 1), 1 ≤ k.val → k.val < t → s k ∉ G) ∧ s (Fin.last t) ∈ G ∧
          s (Fin.last t) = j
        then histProb θ i t s as else 0

/-- `P_θ(T = t | X_0 = i)` for the first passage time `T` from `i` to `G`. -/
noncomputable def firstPassProb {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (G : Set S) (t : ℕ) :
    ℝ≥0∞ :=
  ∑' j, firstPassHit θ i G t j

/-- `P_θ(X_n ∈ G for some n ≥ 1 | X_0 = i) = P_θ(T < ∞ | X_0 = i)`. -/
noncomputable def hitProb {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (G : Set S) : ℝ≥0∞ :=
  ∑' t, firstPassProb θ i G t

/-- `P_θ(X_T = j | X_0 = i)`, the law of the state at which `G` is first entered (on `T < ∞`). -/
noncomputable def hitDist {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (G : Set S) (j : S) : ℝ≥0∞ :=
  ∑' t, firstPassHit θ i G t j

open Classical in
/-- Sennott (1999), p. 139 and p. 295: the expected first passage time `m_{iG}(θ) = E_θ[T]`,
which is `∞` when `P_θ(T < ∞) < 1`. -/
noncomputable def meanPassage {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (G : Set S) : ℝ≥0∞ :=
  if hitProb θ i G = 1 then ∑' t : ℕ, (t : ℝ≥0∞) * firstPassProb θ i G t else ⊤

open Classical in
/-- Sennott (1999), p. 140 and p. 298: the expected cost of a first passage from `i` to `G`,
`c_{iG}(θ) = E_θ[∑_{t=0}^{T-1} C(X_t, A_t) | X_0 = i]` (all costs are counted on `T = ∞`),
a value in `[0, ∞]`. The cost at time `t` is counted when `T > t`, i.e. when
`X_1, …, X_t ∉ G`. -/
noncomputable def passageCost {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (G : Set S) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' s : Fin (t + 1) → S, ∑' as : Fin t → Act,
    if (∀ k : Fin (t + 1), 1 ≤ k.val → s k ∉ G) then histProb θ i t s as * stepCost θ t s as
    else 0

/-- Sennott (1999), p. 139: `θ ∈ ℜ(i,G)`: starting from `i`, `G` is entered at some time
`n ≥ 1` with probability one, and the expected first passage time `m_{iG}(θ)` is finite. -/
def InR {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (G : Set S) : Prop :=
  hitProb θ i G = 1 ∧ meanPassage θ i G < ⊤

/-- Sennott (1999), p. 140: `θ ∈ ℜ*(i,G)`: `θ ∈ ℜ(i,G)` and the expected first passage cost
`c_{iG}(θ)` is finite. -/
def InRStar {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i : S) (G : Set S) : Prop :=
  InR θ i G ∧ passageCost θ i G < ⊤

/-- Sennott (1999), p. 293: `i` leads to `j` under `θ`: `P_θ(X_t = j | X_0 = i) > 0` for some
`t ≥ 0`. -/
def LeadsTo {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i j : S) : Prop :=
  ∃ t : ℕ, stateProb θ i t j ≠ 0

/-- Sennott (1999), p. 293: `i` and `j` communicate (each leads to the other). -/
def Communicate {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (i j : S) : Prop :=
  LeadsTo θ i j ∧ LeadsTo θ j i

/-- The communicating class of `z`. -/
def commClass {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (z : S) : Set S :=
  {j | Communicate θ z j}

/-- Sennott (1999), p. 293: `j` is recurrent: the return time to `j` is finite with probability
one. -/
def Recurrent {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (j : S) : Prop :=
  hitProb θ j {j} = 1

/-- Sennott (1999), p. 293: `j` is positive recurrent: it is recurrent and the expected return
time `m_{jj}` is finite. -/
def PosRecurrent {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (j : S) : Prop :=
  hitProb θ j {j} = 1 ∧ meanPassage θ j {j} < ⊤

/-- Sennott (1999), p. 294: the steady state probability `π_j = (m_{jj})^{-1}`, which is `0`
when `m_{jj} = ∞` (the book notes `π_j = lim_n Q^{(n)}_{jj}` equals this quantity). -/
noncomputable def steadyState {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (j : S) : ℝ≥0∞ :=
  (meanPassage θ j {j})⁻¹

/-- Sennott (1999), (C.1), p. 294: `Q^{(n)}_{ij} = (1/n) ∑_{t=0}^{n-1} P^{(t)}_{ij}`, the expected
number of visits to `j` per unit time in `[0, n−1]` from `i`. -/
noncomputable def Qavg {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (n : ℕ) (i j : S) : ℝ≥0∞ :=
  (∑ t ∈ Finset.range n, stateProb θ i t j) / (n : ℝ≥0∞)

/-- Sennott (1999), Definition C.2.5, p. 301, and Definition 7.5.1, p. 143: the process under
`θ` (for Def. 7.5.1, the Markov chain with costs induced by a randomized stationary policy) is
`z` standard: `m_{iz} < ∞` and `c_{iz} < ∞` for all `i ∈ S`. -/
def IsZStandard {M : SennottDP.Discounted.MDC S Act} (θ : SennottDP.Discounted.Policy M) (z : S) : Prop :=
  ∀ i, meanPassage θ i {z} < ⊤ ∧ passageCost θ i {z} < ⊤

end SennottDP.BOR


