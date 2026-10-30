-- Prove2me | Definitions.Def_OfflineStochMatchFull_InfinitePatience_Policies
-- name    : OfflineStochMatchFull_InfinitePatience_Policies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:45:44.7329+00:00
-- url     : https://prove2.me/theorems/79c69e3e-4ba3-43a7-ab79-b795562ceb17
-- title:
--   Observable histories and randomized legal probing policies
-- statement:
--   Let $G=(V,E)$ be a finite loopless undirected graph, $p_e\in[0,1]$ the independent hidden activation probabilities, $w_e\ge0$ the edge rewards, and $t_v\in\mathbb N\cup\{\infty\}$ the patience bounds. Parallel edges are admitted by the reused graph interface.
--
--   An observable history $h$ lists distinct probed edges and their revealed active bits, in chronological order. Its committed matching consists exactly of the active probes. An unprobed edge is legal when both endpoints are unmatched and each has spent fewer than its patience bound in probes. A randomized policy $\pi$ assigns a normalized probability distribution to the next edge or stop, using only this history; it assigns probability zero to illegal probes at every legal history. Stopping is allowed at every history, including the empty one.
--
--   For any terminal reward $F$, the induced finite execution expectation satisfies
--
--   $$
--   J_0(h)=F(h),\qquad
--   J_{n+1}(h)=\pi_h(\mathrm{stop})F(h)+\sum_{e\in E}\pi_h(e)\bigl((1-p_e)J_n(h\mathbin{+}(e,0))+p_eJ_n(h\mathbin{+}(e,1))\bigr).
--   $$
--
--   The policy reward $R(\pi)$ uses $F(h)=\sum_{e\in M(h)}w_e$, $n=|E|$, and empty initial history. Each legal probe is new, so this horizon includes every possible legal run without replacing infinite patience by a finite cap. These objects represent arbitrary adaptive randomized probe-commit policies, rather than only random-order policies.
--
--   **Formalization Note** Action distributions use Mathlib's `PMF`; their finite coordinate probabilities are real. The expectation is the recursion above, with no integrability convention or supplied performance field.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3 (20 April 2026), https://arxiv.org/abs/2106.06892v3, §§1–2, pp. 1–2, 6–7 (probe-commit model, patience, adaptive probing, Lemma 1 benchmark).

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting

namespace OfflineStochMatchFull.InfinitePatience

open OfflineStochMatch.InfinitePatience

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Observable probe history, oldest probe first: edge and revealed activeness.
Brubach et al., arXiv:2106.06892v3, §§1–2, pp. 1–2, 6–7. -/
abbrev ProbeHistory (E : Type) := List (E × Bool)

/-- The actual committed edges in a history. -/
def historyMatching (h : ProbeHistory E) : Finset E :=
  ((h.filter fun z => z.2).map Prod.fst).toFinset

open Classical in
/-- Matched vertices and spent patience determined entirely by observations. -/
noncomputable def historyState (G : EdmondsMatching65.Polyhedron.Graph V E)
    (h : ProbeHistory E) : RunState V where
  matched := Finset.univ.filter fun v => ∃ e ∈ historyMatching h, v ∈ G.ends e
  probes := fun v => (h.filter fun z => decide (v ∈ G.ends z.1)).length

/-- A legal next probe is new and has two unmatched endpoints with patience left.
This uses the published probe-commit eligibility predicate, including genuine `∞`. -/
def LegalNext (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞)
    (h : ProbeHistory E) (e : E) : Prop :=
  e ∉ h.map Prod.fst ∧ CanProbe G t (historyState G h) e

/-- All finite observable histories obtainable by legal probes; either result of
a probe is allowed, including histories of probability zero for a particular `p`. -/
inductive LegalHistory (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) :
    ProbeHistory E → Prop
  | nil : LegalHistory G t []
  | snoc {h : ProbeHistory E} {e : E} {b : Bool} :
      LegalHistory G t h → LegalNext G t h e → LegalHistory G t (h ++ [(e, b)])

/-- A normalized randomized nonanticipating policy. `none` stops immediately.
The action kernel reads only the observed history, and puts no mass on illegal
probes at any legal history. No performance/optimality property is a field.
Arbitrary private randomness induces such conditional action distributions. -/
structure ProbingPolicy (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) where
  choose : ProbeHistory E → PMF (Option E)
  legal : ∀ h, LegalHistory G t h → ∀ e, ¬ LegalNext G t h e → choose h (some e) = 0

/-- Stopping is legal even at the empty history. -/
noncomputable def stopPolicy (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) :
    ProbingPolicy G t where
  choose := fun _ => PMF.pure none
  legal := by intros; simp

/-- Finite expectation under the induced probing execution. A selected edge is
revealed only after its selection, with a fresh Bernoulli(`p e`) outcome. Stop
has no continuation; a probe is immediately appended with its actual outcome.
New-edge legality makes `card E` a complete horizon, rather than a patience cap. -/
noncomputable def policyEvalFrom (G : EdmondsMatching65.Polyhedron.Graph V E)
    (t : V → ℕ∞) (p : E → ℝ) (π : ProbingPolicy G t)
    (terminal : ProbeHistory E → ℝ) : ℕ → ProbeHistory E → ℝ
  | 0, h => terminal h
  | n + 1, h => ∑ act : Option E, (π.choose h act).toReal *
      match act with
      | none => terminal h
      | some e => (1 - p e) * policyEvalFrom G t p π terminal n (h ++ [(e, false)]) +
          p e * policyEvalFrom G t p π terminal n (h ++ [(e, true)])

/-- Expected *actual* terminal matched weight of an admissible adaptive policy. -/
noncomputable def policyReward (G : EdmondsMatching65.Polyhedron.Graph V E)
    (p : E → ℝ) (t : V → ℕ∞) (w : E → ℝ) (π : ProbingPolicy G t) : ℝ :=
  policyEvalFrom G t p π (fun h => ∑ e ∈ historyMatching h, w e) (Fintype.card E) []

end OfflineStochMatchFull.InfinitePatience


