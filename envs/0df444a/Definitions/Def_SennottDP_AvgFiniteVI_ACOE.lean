-- Prove2me | Definitions.Def_SennottDP_AvgFiniteVI_ACOE
-- name    : SennottDP_AvgFiniteVI_ACOE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T09:16:25.332702+00:00
-- url     : https://prove2.me/theorems/6b8caba1-e57f-407d-8291-de48f99929c3
-- title:
--   Relative value functions, the ACOE operator, finite horizon relative values and Assumption OPA
-- statement:
--   Let $\Delta$ be an MDC with finite state space $S$.
--
--   1. For a stationary policy $e$, the **induced chain** has $P_{ij}(e) = P_{ij}(e(i))$.
--   2. For a stationary $f$ and distinguished states $z_k$ of its positive recurrent classes $R_k$: $p_k(i)$ is the probability of reaching $R_k$ from $i$; $c_{i|k}(f)$, $m_{i|k}(f)$ are the expected cost and time to reach $z_k$ on that event; $w(i) = \sum_k p_k(i)[c_{i|k}(f) - J_k m_{i|k}(f)]$ with $J_k$ the average cost of $f$ on $R_k$; and $w^*(i) = w(i) - \sum_k p_k(i)\sum_{s \in R_k}\pi_s(f) w(s)$.
--   3. For a real function $g$,
--   $$\min_{a \in A_i}\Big\{C(i,a) + \sum_j P_{ij}(a) g(j)\Big\},$$
--   and a stationary policy **realizes the minimum** if it attains it in every state.
--   4. $h_\alpha(i) = V_\alpha(i) - V_\alpha(z)$ for a distinguished state $z$; $h(i) = \lim_{\alpha\to1^-} h_\alpha(i)$; $d_n(i) = h(i) + nJ - v_n(i)$.
--   5. The **finite horizon relative value function** $r_n(i) = v_n(i) - v_n(x)$ for a distinguished state $x$.
--   6. **Assumption OPA**: for every average cost optimal stationary policy $e$, every positive recurrent class of the chain induced by $e$ is aperiodic.
--   7. A stationary $e$ is a **limit point** of a sequence $f_n$ if there is a subsequence $f_{n_k}$ such that for each $i$, $f_{n_k}(i) = e(i)$ for all sufficiently large $k$.
--
--   **Formalization Note** All quantities are real (finite because $S$ is finite). $h$ is defined as the limit (`limUnder` along $\alpha \to 1^-$); Theorem 6.4.2(i) asserts that the limit exists. $d_n$ takes the constant $J$ as an argument.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 101 (Section 6.3); p. 106 (Prop. 6.3.3); pp. 109–110 (Thm 6.4.2); p. 115 (r_n); p. 117 (Assumption OPA); pp. 288–289 (Definition B.1)

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_Criteria
import Definitions.Def_SennottDP_AvgFiniteVI_MarkovChain

namespace SennottDP.AvgFiniteVI

open scoped ENNReal NNReal Topology
open Filter

/-! The objects of Sennott §§6.3–6.6 (pp. 101–120) for an MDC with a finite state space. All of
them are real valued: with `S` finite the costs are bounded and every value below is finite. -/

variable {S : Type*} {Act : Type*} [Fintype S]

/-- The Markov chain induced by a stationary policy `e`: `P_{ij}(e) = P_{ij}(e(i))` (p. 101). -/
noncomputable def inducedChain (M : MDC S Act) (e : StationaryPolicy M) : S → S → ℝ≥0∞ :=
  fun i j => M.P i (e.f i) j

/-- `p_k(i)`: the probability that the positive recurrent class `R_k` of `z = z_k` (its
communicating class under `f`) is reached from `i` (p. 101). -/
noncomputable def classReachProb (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : ℝ≥0∞ :=
  SennottDP.AvgFinite.reachProb (inducedChain M f) (SennottDP.AvgFinite.commClass (inducedChain M f) z) i

/-- `p_k(i) c_{i|k}(f)`: the expected cost incurred under `f` before the first passage to `z_k`
(at time `T ≥ 1`), on the event that `z_k` is reached (p. 101). When `z_k` is reached with
probability one (e.g. `f` unichain and `z_k` positive recurrent) this is `c_{i z_k}(f)`. -/
noncomputable def condPassCost (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : ℝ≥0∞ :=
  SennottDP.AvgFinite.onHitSum (inducedChain M f) z (fun j => (M.C j (f.f j) : ℝ≥0∞)) i

/-- `p_k(i) m_{i|k}(f)`: the expected first passage time to `z_k` under `f`, on the event that
`z_k` is reached (p. 101). When `z_k` is reached with probability one this is `m_{i z_k}(f)`. -/
noncomputable def condPassTime (M : MDC S Act) (f : StationaryPolicy M) (z i : S) : ℝ≥0∞ :=
  SennottDP.AvgFinite.onHitSum (inducedChain M f) z (fun _ => 1) i

/-- The relative value function of Theorem 6.3.1(ii),
`w(i) = ∑_k p_k(i) [c_{i|k}(f) − J_k m_{i|k}(f)]`, where `J_k = J_f(z_k)` is the (constant) average
cost of `f` on `R_k` (p. 101). -/
noncomputable def relValue (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S) (i : S) : ℝ :=
  ∑ z ∈ Z, ((condPassCost M f z i).toReal -
    (avgCost f.toPolicy z).toReal * (condPassTime M f z i).toReal)

open Classical in
/-- The normalized relative value function of Proposition 6.3.3,
`w*(i) = w(i) − ∑_k p_k(i) (∑_{s ∈ R_k} π_s(f) w(s))` (p. 106). -/
noncomputable def relValueNorm (M : MDC S Act) (f : StationaryPolicy M) (Z : Finset S) (i : S) :
    ℝ :=
  relValue M f Z i - ∑ z ∈ Z, (classReachProb M f z i).toReal *
    ∑ s ∈ Finset.univ.filter (fun s => s ∈ SennottDP.AvgFinite.commClass (inducedChain M f) z),
      (SennottDP.AvgFinite.steadyState (inducedChain M f) s).toReal * relValue M f Z s

/-- The right side of the optimality equations (6.31), (6.36), (6.37), (6.49):
`min_{a ∈ A_i} { C(i,a) + ∑_j P_{ij}(a) g(j) }` for a real function `g`. -/
noncomputable def bellmanMin (M : MDC S Act) (g : S → ℝ) (i : S) : ℝ :=
  (M.A i).inf' (M.A_nonempty i) (fun a => (M.C i a : ℝ) + ∑ j, (M.P i a j).toReal * g j)

/-- The stationary policy `e` realizes the minimum in `min_a {C(i,a) + ∑_j P_{ij}(a) g(j)}` at
every state `i`. -/
def RealizesMin (M : MDC S Act) (g : S → ℝ) (e : StationaryPolicy M) : Prop :=
  ∀ i, (M.C i (e.f i) : ℝ) + ∑ j, (M.P i (e.f i) j).toReal * g j = bellmanMin M g i

/-- `E_e[g(X_n) | X_0 = i] = ∑_j P^{(n)}_{ij}(e) g(j)` for a stationary policy `e`. -/
noncomputable def expectStat (M : MDC S Act) (e : StationaryPolicy M) (g : S → ℝ) (n : ℕ)
    (i : S) : ℝ :=
  ∑ j, (SennottDP.AvgFinite.nStep (inducedChain M e) n i j).toReal * g j

/-- `h_α(i) = V_α(i) − V_α(z)` for a distinguished state `z` (Theorem 6.4.2, p. 109). -/
noncomputable def hDisc (M : MDC S Act) (z : S) (α : ℝ) (i : S) : ℝ :=
  (discValue M α i).toReal - (discValue M α z).toReal

/-- `h(i) = lim_{α→1⁻} h_α(i)` (Theorem 6.4.2(i), p. 109). Defined as the limit along
`α → 1⁻`; Theorem 6.4.2(i) asserts that the limit exists when the minimum average cost is
constant. -/
noncomputable def hLim (M : MDC S Act) (z : S) (i : S) : ℝ :=
  limUnder (𝓝[<] (1 : ℝ)) (fun α => hDisc M z α i)

/-- `d_n(i) = h(i) + nJ − v_n(i)` (Theorem 6.4.2(iv), p. 110), for the constant minimum average
cost `J`. -/
noncomputable def dSeq (M : MDC S Act) (z : S) (J : ℝ) (n : ℕ) (i : S) : ℝ :=
  hLim M z i + n * J - (horizonValue M n i).toReal

/-- The finite horizon relative value function `r_n(i) = v_n(i) − v_n(x)` (p. 115). -/
noncomputable def relHorizon (M : MDC S Act) (x : S) (n : ℕ) (i : S) : ℝ :=
  (horizonValue M n i).toReal - (horizonValue M n x).toReal

/-- **Assumption OPA** (p. 117): if `e` is an (average cost) optimal stationary policy, then every
positive recurrent class in the Markov chain induced by `e` is aperiodic. -/
def AssumptionOPA (M : MDC S Act) : Prop :=
  ∀ e : StationaryPolicy M, IsAverageOptimal e.toPolicy →
    ∀ x, SennottDP.AvgFinite.PositiveRecurrent (inducedChain M e) x →
      IsAperiodicClass (inducedChain M e) (SennottDP.AvgFinite.commClass (inducedChain M e) x)

/-- Definition B.1 (pp. 288–289): the stationary policy `e` is a limit point of the sequence
`fs n` if there is a subsequence `fs (φ k)` such that, given `i`, `fs (φ k) i = e i` for all
sufficiently large `k`. -/
def IsLimitPoint {M : MDC S Act} (fs : ℕ → StationaryPolicy M) (e : StationaryPolicy M) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∀ᶠ k in atTop, (fs (φ k)).f i = e.f i

end SennottDP.AvgFiniteVI


