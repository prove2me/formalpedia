-- Prove2me | Definitions.Def_BayesGroupHard_VertexCover_Supplement_Network
-- name    : BayesGroupHard_VertexCover_Supplement_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:39:56.67247+00:00
-- url     : https://prove2.me/theorems/11a6a7ac-d004-4436-a608-920dd0e1509f
-- title:
--   Appendix B, pp. 31–32 — the EXACT-COVER reduction network and the observation history (19)
-- statement:
--   **The EXACT-COVER reduction network (Appendix B, pp. 31–32).** For an RXC3 instance $\hat{\mathcal G}_n=(\hat{\mathcal E}_n,\hat{\mathcal T}_n)$ the network has $2n+2$ agents: a subset agent $\tau$ for each subset, an element agent $\varepsilon$ for each element, and two agents $\kappa$ and $i$. The neighbourhoods are
--   $$\mathcal N_\tau=\{\tau\},\quad \mathcal N_\varepsilon=\{\varepsilon,\kappa,\varepsilon^{(1)},\varepsilon^{(2)},\varepsilon^{(3)}\},\quad \mathcal N_\kappa=\{\kappa\},\quad \mathcal N_i=\{i\}\cup\hat{\mathcal E}_n .$$
--   Subset agents have $\mathbb P_{\tau,1}(1)=\bar p=\tfrac12$ and $\mathbb P_{\tau,0}(1)=\underline p=\tfrac13$. Agent $\kappa$ has $\mathbb P_{\kappa,1}(1)=\bar p^\star=\tfrac7{12}$ and $\mathbb P_{\kappa,0}(1)=\underline p^\star=\tfrac7{27}$, the values fixed by $\ell^\star_1=2\ell_1$, $\ell^\star_0=2\ell_0$ (p. 32). Element agents and $i$ have non-informative signals, $\mathbb P_{\cdot,\theta}(1)=\tfrac12$.
--
--   The observation history of agent $i$ at time two, (19), is that every element agent reports the log-belief ratio $\phi_{\varepsilon,1}=3\ell_1+2\ell_0$ at time one, i.e. $\mu_{\varepsilon,1}(1)=\tfrac{243}{371}$, together with her forced time-zero report $\mu_{\varepsilon,0}(1)=\tfrac12$.
--
--   This is the instance of GROUP-DECISION that the proof of Theorem 2 builds from an RXC3 instance.
--
--   **Formalization Note.** Agents are `Fin n ⊕ Fin n ⊕ Bool`: `tau j`, `epsilon e`, `kappa` (`inr (inr false)`) and `observer` $=i$ (`inr (inr true)`). The paper's "agent $i$ does not receive a private signal" is encoded as a fair-coin signal, which changes no posterior. `project s` is the informative part $(s_\kappa,s_\tau)$ of a full profile; `Observed X s` says that the element agents' reports on $s$ are $\tfrac12$ at time $0$ and $\tfrac{243}{371}$ at time $1$. The reports of $i$ herself, also in her history, do not depend on $s$.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, pp. 31–32 (Appendix B, network, signal structures, ℓ⋆_b = 2ℓ_b, history (19)); p. 11 (proof sketch of Theorem 2)

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Dynamics
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_RXC3

namespace BayesGroupHard.VertexCover.Supplement

open Finset
/-- Subset agents, element agents, κ and i; 2n+2 agents. -/
abbrev XAgent (n : ℕ) := Fin n ⊕ Fin n ⊕ Bool

def tau {n : ℕ} (j : Fin n) : XAgent n := .inl j

def epsilon {n : ℕ} (e : Fin n) : XAgent n := .inr (.inl e)

def kappa {n : ℕ} : XAgent n := .inr (.inr false)

def observer {n : ℕ} : XAgent n := .inr (.inr true)

/-- The network of Appendix B, with rational signal probabilities fixed by ℓ⋆_b=2ℓ_b. -/
noncomputable def xcNet {n : ℕ} (X : RXC3 n) : BinNet (XAgent n) where
  nbr
    | .inl j => {tau j}
    | .inr (.inl e) => insert (epsilon e) (insert kappa
        ((univ.filter (fun j => e ∈ X.sets j)).image tau))
    | .inr (.inr false) => {kappa}
    | .inr (.inr true) => insert observer (univ.image epsilon)
  self_mem := by
    intro a
    rcases a with j | e | b
    · simp [tau]
    · simp [epsilon]
    · cases b <;> simp [kappa, observer]
  p
    | .inl _, θ => if θ then 1 / 2 else 1 / 3
    | .inr (.inl _), _ => 1 / 2
    | .inr (.inr false), θ => if θ then 7 / 12 else 7 / 27
    | .inr (.inr true), _ => 1 / 2

def project {n : ℕ} (s : XAgent n → Bool) : CoreProfile n :=
  (s kappa, fun j => s (tau j))

/-- History (19), including the forced time-zero reports. The observer's own reports
are automatically 1/2 through time one; her private fair coin is uninformative. -/
def Observed {n : ℕ} (X : RXC3 n) (s : XAgent n → Bool) : Prop :=
  ∀ e, report (xcNet X) 0 (epsilon e) s = 1 / 2 ∧
    report (xcNet X) 1 (epsilon e) s = 243 / 371

end BayesGroupHard.VertexCover.Supplement


