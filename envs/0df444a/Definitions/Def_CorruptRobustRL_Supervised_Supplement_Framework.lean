-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supplement_Framework
-- name    : CorruptRobustRL_Supervised_Supplement_Framework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:11:52.167216+00:00
-- url     : https://prove2.me/theorems/99153ec7-5a88-47f8-b717-9d1fa5580f83
-- title:
--   Admissibility, actual Q-supervision and a common visitation bound
-- statement:
--   Let $M$ be a nominal MDP, $\mathcal T$ a Q-supervisor with UCB policy $\pi^{\mathrm{ucb}}$, $\pi$ an actual randomized Markovian policy, and $\rho$ a real number. Condition C.1 requires confidence-admissibility of $\mathcal T$, Q-supervision of $\pi$ by $\mathcal T$, and a UCB visitation ratio bounded by $\rho$. In particular,
--   $$\Pr^{\pi\oplus_h\pi^{\mathrm{ucb}}}[(x_\tau,a_\tau)=(x,a)]\le\rho\Pr^\pi[(x_\tau,a_\tau)=(x,a)]\quad(h\le\tau\le H),\qquad\rho\ge1.$$
--   The predicate includes the published Q-supervisor conditions. Q-supervision uses the plausible set of Definition 4.2, rather than merely the active set. The cross-multiplied occupancy inequality includes zero-visitation pairs and avoids dividing by zero.
--
--   This packages exactly the framework premises used by Theorem C.1, retaining the published atom-wise concatenation and policy correlations.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, pp. 43–44, Condition C.1

import Definitions.Def_CorruptRobustRL_Supervised_Supervisor

namespace CorruptRobustRL.Supervised.Supplement

variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

/-- The three parts of Condition C.1, with the published plausible-set supervision
and the published cross-multiplied UCB visitation ratio. -/
def HasFramework (M : NominalMDP X A) (H : ℕ) (T : QSupervisor X A)
    (π : Mixture X A) (ρ : ℝ) : Prop :=
  T.IsQSupervisor H ∧ T.IsAdmissible M H ∧ IsQSupervised H π T ∧
    HasVisitRatio M H π T.ucb ρ

end CorruptRobustRL.Supervised.Supplement


