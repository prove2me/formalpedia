-- Prove2me | Definitions.Def_BayesGroupHard_VertexCover_Supplement_Dynamics
-- name    : BayesGroupHard_VertexCover_Supplement_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:39:00.426232+00:00
-- url     : https://prove2.me/theorems/e565050c-0bad-4fd6-9f13-e85e9e320116
-- title:
--   §2.1 and §4, pp. 7, 16 — revealed-belief dynamics: reported posteriors, information sets and log-belief ratios
-- statement:
--   **The revealed belief model.** The network of the published binary action model is reused: a finite set of agents, a neighbourhood $\mathcal N_i \ni i$ for each agent, a state $\theta\in\{0,1\}$ with uniform prior $\nu(0)=\nu(1)=\tfrac12$, and conditionally independent binary private signals with $\mathbb P_{i,\theta}(1)=p_{i,\theta}$. For a set $\mathcal I$ of signal profiles, $\mu(\theta\mid\mathcal I)$ is the posterior (4) of p. 16.
--
--   In the revealed belief model (§2.1, p. 7) every agent announces her whole posterior instead of a MAP action. With two states this is the number $r_{j,t}=\mu_{j,t}(1)$. Reports and information sets are defined jointly by recursion on time $t$. On the signal profile $s$, the information set of agent $i$ at time $t$ is
--   $$\mathcal I_{i,t}(s)=\{s' : s'_i=s_i \text{ and } r_{j,\tau}(s')=r_{j,\tau}(s)\ \text{for all } j\in\mathcal N_i,\ \tau<t\},$$
--   the profiles consistent with her history $h_{i,t}$: her own signal and the reported beliefs of her neighbours at all earlier times. Her belief is $\mu_{i,t}(\theta)=\mu(\theta\mid\mathcal I_{i,t}(s))$, her report is $r_{i,t}(s)=\mu_{i,t}(1)$, and her log-belief ratio (2) is $\phi_{i,t}=\log\bigl(\mu_{i,t}(1)/\mu_{i,t}(0)\bigr)$.
--
--   These are the dynamics of Problem 2 and Theorem 2: the time-two belief of an agent who has observed two rounds of reported posteriors.
--
--   **Formalization Note.** `rInfoUsing`, `reportsUpTo`, `rInfo`, `belief`, `report`, `rLog` are the information set given earlier reports, the reports at all times below $t$ (structural recursion on $t$; entries at times $\ge t$ are an unused $0$), $\mathcal I_{i,t}$, $\mu_{i,t}(\theta)$, $r_{i,t}$ and $\phi_{i,t}$. Reports are compared as real numbers. `BinNet`, `jointProb` and `post` come from the published `BayesGroupHard.VertexCover.Model`; its binary-action `mapAct`/`infoSet`/`act` are not used. No tie-breaking is needed: the posterior is the unique optimum of the squared-distance utility of §2.1.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 6 (§2, history (1)), p. 7 (§2.1, revealed belief model), p. 8 ((2)), p. 16 (§4, (4))

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model

namespace BayesGroupHard.VertexCover.Supplement

open Finset
variable {Ag : Type} [Fintype Ag] [DecidableEq Ag]

/-- Consistency with the own signal and all earlier real-valued reports (§2, p.6). -/
noncomputable def rInfoUsing (N : BinNet Ag) (t : ℕ)
    (past : ℕ → Ag → (Ag → Bool) → ℝ) (i : Ag) (s : Ag → Bool) :
    Finset (Ag → Bool) := by
  classical
  exact univ.filter (fun s' => s' i = s i ∧
    ∀ j ∈ N.nbr i, ∀ τ < t, past τ j s' = past τ j s)

/-- Reports below t; entries at times ≥ t are unused and set to zero. -/
noncomputable def reportsUpTo (N : BinNet Ag) : ℕ → ℕ → Ag → (Ag → Bool) → ℝ
  | 0 => fun _ _ _ => 0
  | t + 1 => fun τ j s =>
      if τ < t then reportsUpTo N t τ j s
      else if τ = t then post N true (rInfoUsing N t (reportsUpTo N t) j s)
      else 0

noncomputable def rInfo (N : BinNet Ag) (t : ℕ) (i : Ag) (s : Ag → Bool) :
    Finset (Ag → Bool) := rInfoUsing N t (reportsUpTo N t) i s

noncomputable def belief (N : BinNet Ag) (t : ℕ) (i : Ag) (s : Ag → Bool) (θ : Bool) : ℝ :=
  post N θ (rInfo N t i s)

noncomputable def report (N : BinNet Ag) (t : ℕ) (i : Ag) (s : Ag → Bool) : ℝ :=
  belief N t i s true

noncomputable def rLog (N : BinNet Ag) (t : ℕ) (i : Ag) (s : Ag → Bool) : ℝ :=
  Real.log (belief N t i s true / belief N t i s false)

end BayesGroupHard.VertexCover.Supplement


