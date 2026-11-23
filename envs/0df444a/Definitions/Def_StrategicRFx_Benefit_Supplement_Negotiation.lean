-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Supplement_Negotiation
-- name    : StrategicRFx_Benefit_Supplement_Negotiation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:06:18.096092+00:00
-- url     : https://prove2.me/theorems/55b2234b-5cff-434c-8bc2-6e4c05d81ecc
-- title:
--   §3.2.2 — realized negotiation continuations and the buyer’s first two tie priorities
-- statement:
--   A negotiation response records acceptance of both offers or a leader, acceptance or rejection of the leader's quote, and an actual maximizer of the published program [RFx-i]. The follower accepts his quote if and only if it is no more than his renegotiated profit, including equality. If the leader's profit is $x$ and the buyer's exclusive payoff is $y$, the realized payoffs are
--
--   $$\pi_i=x,\qquad \pi_j=\min\{\widetilde\pi_j,\theta_j(\Pi-x-y)\},\qquad \pi_0=\Pi-\pi_i-\pi_j.$$
--
--   The Nash programs, all their constraints and both reservation-utility formulas are imported from the published definition unchanged. Buyer choices maximize realized buyer profit over the direct accept-both option and all negotiation solutions. Among tied options, accepting both has first priority and accepting the leader has second priority. Accepting both is represented canonically by one response, so accepting both immediately is meaningful for either zero-quoting supplier.
--
--   The relation deliberately leaves the remaining technical buyer tie unresolved; it does not assert existence of a deterministic selector. It is sufficient to state Lemma EC.2 without resolving those remaining ties, but is not the full selector required by Theorem 4.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), §3.2.2, pp. 16–18; Lemma EC.2, p. ec16

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

namespace StrategicRFx.Benefit.Supplement

/-- A concrete negotiation continuation, not just its maximum buyer value.
The follower accepts exactly when AcceptsFollower holds, including equality. -/
inductive Negotiation where
  | both
  | bargain (leader : Fin 2) (acceptLeader : Bool) (profit exclusiveBuyer : ℝ)

def Negotiation.payoff (P : Params) (t : Fin 2 → ℝ) : Negotiation → ℝ × (Fin 2 → ℝ)
  | .both => (P.Pi - t 0 - t 1, t)
  | .bargain i _ x y =>
    (leaderBuyer P i t x y, fun k => if k = i then x else min (t (other i)) (followerSplit P (other i) x y))

/-- The bargaining programs are imported unchanged from the live mission.
A direct accept-both option is always available; negotiation solutions are
witnesses to the actual constrained argmax, never selected via a default. -/
def Negotiation.Feasible (P : Params) (t : Fin 2 → ℝ) : Negotiation → Prop
  | .both => True
  | .bargain i a x y => IsLeaderSolution P i a t x y

/-- Priority 2 for accepting both; priority 1 for early acceptance; priority 0
otherwise. Remaining source technical ties have not been resolved by this
priority function. -/
noncomputable def Negotiation.priority (P : Params) (t : Fin 2 → ℝ) : Negotiation → ℕ := by
  classical
  exact fun r => match r with
    | .both => 2
    | .bargain i a x y => if a = true ∧ AcceptsFollower P i t x y then 2 else if a then 1 else 0

/-- Source p. 16 hierarchy of buyer preferences. This is set valued: it does
not assume all argmaxes are unique or that every bargaining program attains.
A nontrivial technical tie can remain between the two reject-first leaders. -/
def IsPriorityResponse (P : Params) (t : Fin 2 → ℝ) (r : Negotiation) : Prop :=
  r.Feasible P t ∧
  (∀ s : Negotiation, s.Feasible P t → (s.payoff P t).1 ≤ (r.payoff P t).1) ∧
  (∀ s : Negotiation, s.Feasible P t → (s.payoff P t).1 = (r.payoff P t).1 →
    s.priority P t ≤ r.priority P t) ∧
  (r.priority P t = 2 → r = .both)

/-- 'Immediately' includes the simultaneous acceptance of both quotes;
it does not demand two different suppliers each occupy the first position. -/
def AcceptedImmediately (i : Fin 2) : Negotiation → Prop
  | .both => True
  | .bargain j a _ _ => j = i ∧ a = true

end StrategicRFx.Benefit.Supplement


