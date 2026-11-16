-- Prove2me | Definitions.Def_BipartiteVRM_Competitive_Supplement_Specifications
-- name    : BipartiteVRM_Competitive_Supplement_Specifications
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:29:03.038843+00:00
-- url     : https://prove2.me/theorems/b402d996-8e72-47e5-b592-6d96ce2e4384
-- title:
--   Optimal offline matching, execution correctness and optimal paths $P^*_u(t)$
-- statement:
--   For an MPMD input, $M^*$ is **optimal** if it is a perfect matching of $R$ minimizing $D(M^*)=\sum_{e\in M^*}D(e)$. **Offline attainment** says the actual timed objective $\sum_{uv}[d(x_u,x_v)+(t_{uv}-a_u)+(t_{uv}-a_v)]$, over perfect matchings with $t_{uv}\ge\max(a_u,a_v)$, attains its minimum $\mathrm{OPT}$.
--
--   **Execution correctness** of a run says: it halts; its output is a perfect matching of $R$, each pair once, with match times no earlier than both arrivals; at every state $M^{\mathrm{OFF}}$ is a matching on arrived requests saturating exactly the requests saturated by $M^{\mathrm{VRM}}$, and every cached $P_u$ is an $M^{\mathrm{OFF}}$-augmenting path from $u$ to its partner that minimizes $\varphi$ over all $M^{\mathrm{OFF}}$-augmenting paths from $u$ to another free request, with $\varphi_u=+\infty$ exactly when $u$ is the only free request; the output is only appended to and the clock never decreases.
--
--   For a free request $u$ at time $t$, with $M_t$ the offline matching at $t$, the **optimal path** $P^*_u(t)$ is the walk from $u$ that alternately follows the $M^*$-edge and the $M_t$-edge, i.e. the component of $M_t\triangle M^*$ containing $u$; its last vertex is the **terminal request**, and $D^*=D(P^*_u(t)\cap M^*)$.
--
--   These are conclusion predicates and analysis objects, never assumptions on the data or the run.
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 13 (MPMD model, OPT), p. 14 (feasibility of output decisions), p. 17 (§5.4, M*, M_t, P*_u(t), terminal request)

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Execution

set_option autoImplicit false

namespace BipartiteVRM.Competitive.Supplement

open Classical
open MatchingDelays.Linear (Instance Edge edge endpoints allPairs IsPairing FeasibleTimes
  scheduleCost offlineOpt pairingCost requestDist)

/-! Kuo, §5, pp. 13–18. Conclusion predicates (never assumptions on the data or the run)
and the analysis objects M*, P*_u(t) and D* of §5.4. -/

/-- The TA distance D on edges. -/
noncomputable def taDist {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (e : Edge) : ℝ := requestDist I e.1 e.2

/-- M* is a minimum-cost perfect matching on R under D. -/
def IsOptimal {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) (Mstar : Matching) :
    Prop :=
  IsPairing n Mstar ∧ ∀ N, IsPairing n N → pairingCost I Mstar ≤ pairingCost I N

/-- The timed offline objective has a minimizer and OPT is its minimum value. -/
def OfflineAttained {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) : Prop :=
  ∃ M τ, IsPairing n M ∧ FeasibleTimes I M τ ∧ scheduleCost I M τ = offlineOpt I ∧
    ∀ N σ, IsPairing n N → FeasibleTimes I N σ → offlineOpt I ≤ scheduleCost I N σ

/-- A feasible output: a perfect matching on R, each pair output once, with match times
no earlier than both arrivals. -/
def FeasibleOutput {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (E : List MatchEvent) : Prop :=
  IsPairing n (eventEdges E) ∧ (E.map (fun e => edge e.initiator e.partner)).Nodup ∧
    ∀ e ∈ E, e.initiator ≠ e.partner ∧
      max (MatchingDelays.Linear.arrival I e.initiator)
        (MatchingDelays.Linear.arrival I e.partner) ≤ e.time

/-- Reachable-state invariants: M^OFF is a matching on inserted requests, M^OFF and
M^VRM saturate the same requests, and every output decision is feasible. -/
def StateValid {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) (b : View) : Prop :=
  b.inserted ⊆ b.visible ∧ b.visible ⊆ Finset.range n ∧
    IsMatching b.off ∧ covered b.off ⊆ b.inserted ∧
    IsMatching (eventEdges b.output) ∧
    (b.output.map (fun e => edge e.initiator e.partner)).Nodup ∧
    covered b.off = covered (eventEdges b.output) ∧
    ∀ e ∈ b.output, e.initiator ≠ e.partner ∧
      max (MatchingDelays.Linear.arrival I e.initiator)
        (MatchingDelays.Linear.arrival I e.partner) ≤ e.time

/-- The cached P_u is a genuine minimum augmenting path: an M^OFF-augmenting path from u
to another free request minimizing φ over all of them; φ_u = +∞ iff u is the only free
request. -/
def CacheValid (γ : ℝ) (b : View) : Prop :=
  ∀ u ∈ b.freeRequests,
    (b.cache u = none ↔ b.freeRequests = {u}) ∧
    ∀ v Q, b.cache u = some (v, Q) →
      v ∈ b.freeRequests ∧ v ≠ u ∧
      (∃ P, IsAugmenting b.inserted b.off u v P ∧ pathEdges P = Q) ∧
      ∀ w P, IsAugmenting b.inserted b.off u w P →
        netCost b.edgeTA γ b.off Q ≤ netCost b.edgeTA γ b.off (pathEdges P)

/-- Halting, a feasible perfect output, reachable-state invariants, irrevocable output
and a monotone clock: all *conclusions*. -/
def ExecutionCorrect {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) : Prop :=
  (∃ k, halted I γ (state I γ tie k)) ∧
    FeasibleOutput I (output I γ tie) ∧
    (∀ k, StateValid I (state I γ tie k) ∧ CacheValid γ (state I γ tie k)) ∧
    (∀ k, (state I γ tie k).output.IsPrefix (state I γ tie (k + 1)).output) ∧
    (∀ k, (state I γ tie k).clock ≤ (state I γ tie (k + 1)).clock)

/-- The other endpoint of the edge of M at x, if any. -/
noncomputable def mate (M : Matching) (x : ℕ) : Option ℕ :=
  ((M.filter (fun e => x ∈ endpoints e)).toList.head?).map
    (fun e => if e.1 = x then e.2 else e.1)

/-- Follow an M*-edge, then an M-edge, alternately, from u. Started at an M-free request
with M* perfect, this traverses the component of M △ M* containing u, ending at its
terminal request. The fuel is an analysis bound that never truncates the component. -/
noncomputable def optimalWalk (M Mstar : Matching) : ℕ → ℕ → List ℕ
  | 0, u => [u]
  | k + 1, u => match mate Mstar u with
    | none => [u]
    | some p => u :: p ::
        (match mate M p with | none => [] | some q => optimalWalk M Mstar k q)

/-- P*_u(t): the optimal path of u at time t, with M_t the offline matching at t. -/
noncomputable def optimalPath {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) (t : ℝ) (u : ℕ) : List ℕ :=
  optimalWalk (stateAt I γ tie t).off Mstar (n + 1) u

/-- D* = D(P*_u(t) ∩ M*). -/
noncomputable def optimalLength {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) (t : ℝ) (u : ℕ) : ℝ :=
  ∑ e ∈ pathEdges (optimalPath I γ tie Mstar t u) ∩ Mstar, taDist I e

end BipartiteVRM.Competitive.Supplement


