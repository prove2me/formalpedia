-- Prove2me | Definitions.Def_TransparencyTeamContracts_Submodular_Game
-- name    : TransparencyTeamContracts_Submodular_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:13.198237+00:00
-- url     : https://prove2.me/theorems/a2b637cd-f647-44b1-b758-21fffe89a53b
-- title:
--   Binary effort contracts, pure equilibria, and stateless optimal utility
-- statement:
--   Let $[n]$ be a finite agent set. A success technology $f:2^{[n]}\to[0,1]$ is monotone; its baseline $f(\varnothing)$ may be positive. Each cost $c_i$ is nonnegative. A contract has arbitrary shares $\alpha_i\in[0,1]$, with no constraint on their sum. For an effort team $S$, utilities are
--   $$U_i(S,\alpha)=\alpha_i f(S)-\mathbf1_{i\in S}c_i,\qquad U_P(S,\alpha)=(1-\sum_i\alpha_i)f(S).$$
--   The binary-action game is an instance of the published general strategic-game interface. A pure equilibrium permits no strictly beneficial unilateral deviation. A principal-favorable equilibrium maximizes $U_P$ among all pure equilibria of that contract. Define
--   $$V(f,c)=\sup\{U_P(S,\alpha):\alpha\in[0,1]^n,\ S\in\operatorname{NE}(\alpha;f,c)\}.$$
--   Optimizing over contracts and equilibria jointly is equivalent to favorable selection. The nonempty payoff set is bounded above by one on source instances. Minimum-payment contracts pay zero off the team and to zero-cost members, and pay $c_i/[f(S)-f(S\setminus\{i\})]$ to positive-cost members. A positive-cost member must have strictly positive marginal, and each resulting share must be at most one. Thus division by zero cannot admit an infeasible team.
--   The state-dependent model stores one such technology per state and a common nonnegative cost vector. Submodularity and additivity are imposed only by the individual theorem clauses that need them. These definitions preserve the complete contract game, including both directions of deviation and positive baseline technologies.
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), §2, printed pp.5–7 (PDF pp.7–9); §4 minimum-payment contracts, printed p.9 (PDF p.11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1292.pdf; PDF SHA-256 0aa8b61daf25346bcfca67a178c55762d05abe3f79b2b66a6d2ad6dfed9b3321

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsAdditive
import Definitions.Def_FairTeamContracts_IsTeamContract
import Definitions.Def_FairTeamContracts_IsFeasible
import Definitions.Def_WeightedCoordGames_Model

open Finset

namespace TransparencyTeamContracts.Submodular

/-- Submission #1292, §2, printed p.5 (PDF 7), including footnote 1.
No normalization at the empty set is imposed. -/
def IsSuccess {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  Monotone f ∧ ∀ S, 0 ≤ f S ∧ f S ≤ 1

/-- Full contract cube: there is no constraint on the sum of shares. -/
def IsContract {n : ℕ} (α : Fin n → ℝ) : Prop :=
  FairTeamContracts.IsTeamContract univ α

/-- Agent's expected utility, §2, printed p.7 (PDF 9). -/
noncomputable def agentUtility {n : ℕ} (f : Finset (Fin n) → ℝ) (c α : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  α i * f S - if i ∈ S then c i else 0

/-- Principal's utility; transfers to all agents are counted, §2, p.7. -/
noncomputable def principalUtility {n : ℕ} (f : Finset (Fin n) → ℝ)
    (α : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (1 - ∑ i, α i) * f S

/-- Binary action profiles and effort teams are equivalent finite representations. -/
def effortTeam {n : ℕ} (a : Fin n → Bool) : Finset (Fin n) :=
  univ.filter (fun i => a i = true)

/-- The profile corresponding to a team; both effort and shirking are available. -/
def teamProfile {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)

/-- The source's contract game built on a published general strategic game.
Only the general StrategicGame interface is used; no coordination-game assumptions. -/
noncomputable def effortGame {n : ℕ} (f : Finset (Fin n) → ℝ) (c α : Fin n → ℝ) :
    WeightedCoordGames.StrategicGame (Fin n) Bool where
  S _ := Set.univ
  payoff i a := agentUtility f c α (effortTeam a) i

/-- Weak best responses to both binary actions, §2, printed p.7 (PDF 9). -/
def IsEquilibrium {n : ℕ} (f : Finset (Fin n) → ℝ) (c α : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop :=
  (effortGame f c α).IsNash (teamProfile S)

/-- Principal-favorable pure NE, §2, p.7: maximize over the finite equilibrium set. -/
def IsBestEquilibrium {n : ℕ} (f : Finset (Fin n) → ℝ) (c α : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop :=
  IsEquilibrium f c α S ∧ ∀ T, IsEquilibrium f c α T →
    principalUtility f α T ≤ principalUtility f α S

/-- Joint optimization over a contract and an equilibrium equals optimization with
principal-favorable selection: each contract has finitely many equilibrium teams.
The payoff set is nonempty and bounded on source instances; see verification module. -/
def statelessPayoffs {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) : Set ℝ :=
  {u | ∃ α S, IsContract α ∧ IsEquilibrium f c α S ∧ u = principalUtility f α S}

/-- The source's OPT(f,c), also denoted V(f,c) here, §§2–4, pp.7–9. -/
noncomputable def V {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) : ℝ :=
  sSup (statelessPayoffs f c)

/-- Realized marginal to an effort team, §4, p.9. -/
def teamMarginal {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n))
    (i : Fin n) : ℝ := f S - f (S.erase i)

/-- Minimum shares: the zero-cost convention is explicit. Positive cost with zero
marginal is rejected by IsMinimumTeam, rather than using real division by zero. -/
noncomputable def minimumContract {n : ℕ} (f : Finset (Fin n) → ℝ)
    (c : Fin n → ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ S ∧ c i ≠ 0 then c i / teamMarginal f S i else 0

/-- Feasible minimum-payment teams, §4, p.9. Infeasible zero-marginal positive-cost
teams are explicitly excluded; no total-share constraint is imposed. -/
def IsMinimumTeam {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, c i ≠ 0 → 0 < teamMarginal f S i) ∧
  IsContract (minimumContract f c S) ∧
  FairTeamContracts.IsFeasible f c S (minimumContract f c S)

/-- Data and precisely the standing assumptions of §2, pp.5–6 (PDF 7–8).
The prior is separate, so the same family can be used for every posterior. -/
structure Model (n m : ℕ) where
  f : Fin m → Finset (Fin n) → ℝ
  c : Fin n → ℝ
  success : ∀ ω, IsSuccess (f ω)
  cost_nonneg : ∀ i, 0 ≤ c i

end TransparencyTeamContracts.Submodular


