-- Prove2me | Definitions.Def_PlatformPreannouncement_SHNSW_Equilibrium
-- name    : PlatformPreannouncement_SHNSW_Equilibrium
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:18:27.364226+00:00
-- url     : https://prove2.me/theorems/5d575304-67d9-49da-9d76-f81ce8b0fd11
-- title:
--   Simultaneous-announcement pure SPNE and formal outcome
-- statement:
--   A pure strategy profile specifies both firms' simultaneous announcement choices and a price/fee pair for each firm at every ordered announcement history. A fulfilled-expectation demand selection is fixed across histories and price profiles.
--
--   Subgame perfection requires a valid selection and a feasible pricing equilibrium at all nine histories, with no omitted history. Using the selected continuation profits, the two announcement choices must form a pure Nash equilibrium over all three modes for each player. The published generic Nash predicate supplies both independent unilateral announcement comparisons. The unrelated single-leader SPNE predicate in that reference is not used.
--
--   A symmetric pure strategy profile has equal initial announcements, and firm 0's tariffs at $(a,b)$ equal firm 1's tariffs at $(b,a)$ for every pair of modes. This symmetry restriction on the equilibria under study does not restrict either firm's deviations. Demand selection is an explicit part of the equilibrium system; it is not reselected separately for each incentive inequality.
--
--   The formal outcome predicate, separate from subgame perfection, states that the announcement pair is $(F,F)$ and that each firm's on-path tariffs satisfy
--   $$p_i=2(t-\alpha-\beta),\qquad l_i=2(t-\beta).$$
--   It contains no incentive claims. The theorem must establish this outcome together with an equilibrium and characterize all symmetric pure equilibrium outcomes.
-- source:
--   Chellappa and Mukherjee (2020), DOI 10.1287/mnsc.2020.3606, held source.pdf Figure 1 p. 16, §§2.3–2.5 pp. 17–25, Proposition 1 p. 26; pure/symmetric restriction pp. 21–22. Generic Nash: BundledPay_Base_GenericGame.

import Definitions.Def_PlatformPreannouncement_SHNSW_Market
import Definitions.Def_BundledPay_Base_GenericGame

namespace PlatformPreannouncement.SHNSW

/-- Two simultaneous announcements and price plans at all nine histories. -/
structure StrategyProfile where
  announcement : History
  continuation : History → Prices

noncomputable def continuationPayoff (P : Parameters) (D : DemandSelection)
    (s : StrategyProfile) (h : History) (i : Firm) : ℝ :=
  profit P h (s.continuation h) (D h (s.continuation h)) i

/-- Both players choose announcements. No history is removed even if its
symmetric interior candidate is infeasible. Demand selection existence is
part of the goal, not an assumed certificate. -/
def IsSPNE (P : Parameters) (D : DemandSelection) (s : StrategyProfile) : Prop :=
  ValidSelection P D ∧
  (∀ h, PricingEquilibrium P D h (s.continuation h)) ∧
  BundledPay.Base.IsNash Set.univ Set.univ
    (fun a b => continuationPayoff P D s (a, b) 0)
    (fun a b => continuationPayoff P D s (a, b) 1)
    s.announcement.1 s.announcement.2

/-- Symmetric pure strategies exchange the firms and the announcement history;
deviations in IsSPNE are unrestricted unilateral deviations. -/
def Symmetric (s : StrategyProfile) : Prop :=
  s.announcement.1 = s.announcement.2 ∧
  ∀ a b, s.continuation (a, b) 0 = s.continuation (b, a) 1

/-- The outcome asserted by Proposition 1; this is not an equilibrium definition. -/
def FormalOutcome (P : Parameters) (s : StrategyProfile) : Prop :=
  s.announcement = (.formal, .formal) ∧
  ∀ i, (s.continuation s.announcement i).1 = 2 * (P.t - P.alpha - P.beta) ∧
    (s.continuation s.announcement i).2 = 2 * (P.t - P.beta)

end PlatformPreannouncement.SHNSW


