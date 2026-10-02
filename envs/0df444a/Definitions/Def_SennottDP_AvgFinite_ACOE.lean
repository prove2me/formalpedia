-- Prove2me | Definitions.Def_SennottDP_AvgFinite_ACOE
-- name    : SennottDP_AvgFinite_ACOE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T08:12:44.83277+00:00
-- url     : https://prove2.me/theorems/c3dae66e-9ef0-4c8c-8e66-e08203cc7756
-- title:
--   The objects of §6.3: induced chain, $p_k$, $W_\alpha$, $w_\alpha$, the relative value function $w$ and its normalization $w^*$
-- statement:
--   Let $\Delta$ be an MDC with a finite state space and $f$ a stationary policy. The chain induced by $f$ has transition probabilities $P_{ij}(f) = P_{ij}(f(i))$ and costs $C(i,f) = C(i,f(i))$. Let $R_1,\ldots,R_K$ be its positive recurrent classes and choose distinguished states $z_k \in R_k$.
--
--   1. $p_k(i)$ is the probability that class $R_k$ is reached from $i$.
--   2. $W_\alpha(i) = \sum_k p_k(i)\, V_\alpha(z_k)$ and the **relative value function** $w_\alpha(i) = V_\alpha(i) - W_\alpha(i)$.
--   3. $m_{i|k}(f)$ and $c_{i|k}(f)$ are the expected time and the expected cost to reach $z_k$ from $i$, conditioned on reaching $R_k$; $J_k$ is the (constant) average cost of $f$ on $R_k$, $J_k = J_f(z_k)$.
--   4. The limit relative value function is
--   $$w(i) = \sum_k p_k(i)\,\big[c_{i|k}(f) - J_k\, m_{i|k}(f)\big].$$
--   5. Its normalized version is
--   $$w^*(i) = w(i) - \sum_k p_k(i) \Big(\sum_{s \in R_k} \pi_s(f)\, w(s)\Big),$$
--   where $\pi_s(f)$ are the steady state probabilities of the chain induced by $f$.
--
--   These are the ingredients of the multichain average cost optimality equation (Theorem 6.3.1) and of the expansion of $V_\alpha$ near $\alpha = 1$ (Proposition 6.3.3).
--
--   **Formalization Note** The products $p_k(i)\,c_{i|k}(f)$ and $p_k(i)\,m_{i|k}(f)$ are formalized directly as $E[\sum_{s < T} C(X_s,f);\ T < \infty]$ and $E[T;\ T<\infty]$ with $T$ the first passage time to $z_k$ (reaching $R_k$ and reaching $z_k$ are the same event up to probability zero, since a finite positive recurrent class is closed and every state in it is visited), so no division by $p_k(i)$ occurs. The class $R_k$ is the communicating class of $z_k$. $V_\alpha$, $W_\alpha$ are in `ℝ≥0∞`; $w_\alpha$, $w$, $w^*$ are real, with `toReal` applied to quantities that are finite for a finite state space.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 101, Section 6.3; p. 106, Proposition 6.3.3

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria
import Definitions.Def_SennottDP_AvgFinite_MarkovChain

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal

/-! The objects of Sennott §6.3, p. 101, built from a stationary policy `f` of an MDC with a finite
state space and a set `Z = {z_1, …, z_K}` of distinguished states, one in each positive recurrent
class `R_k` of the chain induced by `f`. -/

variable {S : Type*} {Act : Type*} [Fintype S]

/-- The Markov chain induced by a stationary policy `e`: `P_{ij}(e) = P_{ij}(e(i))` (p. 101). -/
noncomputable def inducedChain (M : MDC S Act) (e : StationaryPolicy M) : S → S → ℝ≥0∞ :=
  fun i j => M.P i (e.f i) j

/-- `p_k(i)`: the probability that the positive recurrent class `R_k` of `z = z_k` (its
communicating class under `f`) is reached from `i` (p. 101). -/
noncomputable def classReachProb (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : ℝ≥0∞ :=
  reachProb (inducedChain M f) (commClass (inducedChain M f) z) i

/-- `W_α(i) = ∑_k p_k(i) V_α(z_k)` (p. 101), in `[0, ∞]`. -/
noncomputable def Wdisc (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S) (α : ℝ)
    (i : S) : ℝ≥0∞ :=
  ∑ z ∈ Z, classReachProb M f z i * discValue M α z

/-- The relative value function `w_α(i) = V_α(i) − W_α(i)` (p. 101), as a real number (both terms
are finite for a finite state space; the real subtraction is taken of their real values). -/
noncomputable def wdisc (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S) (α : ℝ)
    (i : S) : ℝ :=
  (discValue M α i).toReal - (Wdisc M f Z α i).toReal

/-- `p_k(i) c_{i|k}(f)`: the expected cost incurred under `f` before reaching `z_k`, on the event
that `R_k` (equivalently `z_k`) is reached; `c_{i|k}(f)` is this cost conditioned on reaching
`R_k` (p. 101). -/
noncomputable def condPassCost (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : ℝ≥0∞ :=
  onHitSum (inducedChain M f) z (fun j => (M.C j (f.f j) : ℝ≥0∞)) i

/-- `p_k(i) m_{i|k}(f)`: the expected time to reach `z_k` under `f`, on the event that `R_k`
(equivalently `z_k`) is reached; `m_{i|k}(f)` is this time conditioned on reaching `R_k`
(p. 101). -/
noncomputable def condPassTime (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : ℝ≥0∞ :=
  onHitSum (inducedChain M f) z (fun _ => 1) i

/-- The limit relative value function of Theorem 6.3.1(ii),
`w(i) = ∑_k p_k(i) [c_{i|k}(f) − J_k m_{i|k}(f)]`, where `J_k = J_f(z_k)` is the (constant) average
cost of `f` on `R_k` (p. 101). Real valued. -/
noncomputable def relValue (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S) (i : S) : ℝ :=
  ∑ z ∈ Z, ((condPassCost M f z i).toReal -
    (avgCost f.toPolicy z).toReal * (condPassTime M f z i).toReal)

open Classical in
/-- The normalized relative value function of Proposition 6.3.3,
`w*(i) = w(i) − ∑_k p_k(i) (∑_{s ∈ R_k} π_s(f) w(s))`, with `π_s(f)` the steady state
probabilities of the chain induced by `f` (p. 106). -/
noncomputable def relValueNorm (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S) (i : S) :
    ℝ :=
  relValue M f Z i - ∑ z ∈ Z, (classReachProb M f z i).toReal *
    ∑ s ∈ Finset.univ.filter (fun s => s ∈ commClass (inducedChain M f) z),
      (steadyState (inducedChain M f) s).toReal * relValue M f Z s

end SennottDP.AvgFinite


