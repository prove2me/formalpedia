-- Prove2me | Definitions.Def_HumanMachine_Accuracy_DecisionModel
-- name    : HumanMachine_Accuracy_DecisionModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:23:08.625679+00:00
-- url     : https://prove2.me/theorems/0d3ea1a7-fe6a-458f-bbcf-a5fdde8b9c0f
-- title:
--   §3.1, §4 — the rationally inattentive decision-maker's optimal accuracy $A^\star(\mu)$ and optimal expected value $V^\star(\mu)$
-- statement:
--   This definition builds on the binary rational-inattention decision model `HumanMachine.Alone.model`. In that model a decision-maker (DM) with prior $\mu=P(\omega=g)$ that the state is good chooses conditional probabilities $p_g=P(y\mid g)$ and $p_b=P(y\mid b)$ of announcing the good state, $(p_g,p_b)\in[0,1]^2$. A strategy has **accuracy** $A=(1-\mu)(1-p_b)+\mu p_g$ (7), **cognitive cost** $C=\lambda\big[H(p)-(1-\mu)H(p_b)-\mu H(p_g)\big]$ (8), where $p=(1-\mu)p_b+\mu p_g$ (4) and $H$ is the natural-log binary entropy, and **expected value** $V=A-C$. A strategy is **optimal** if it maximizes $V$ over $[0,1]^2$.
--
--   Fix an optimal strategy $(p_g^\star,p_b^\star)$ for information cost $\lambda$ and prior $\mu$. The **optimal accuracy** and the **optimal expected value** are
--
--   $$
--   A^\star(\mu)=A(p_g^\star,p_b^\star),\qquad V^\star(\mu)=V(p_g^\star,p_b^\star)=A^\star(\mu)-C^\star(\mu).
--   $$
--
--   These are the quantities the paper denotes $A^\star(\mu)$ and $V^\star(\mu)$ on p. 9; Corollary 2 computes them in closed form and Proposition 1 compares them with their machine-assisted counterparts.
--
--   **Formalization Note** The general information-processing problem (2) of §3.1 is not formalized; the model uses the paper's own §4 "as if" reduction (Matějka & McKay 2015, Theorem 1), in which the DM chooses $(p_g,p_b)$ directly. This is the paper's equivalence, not a restriction on strategies. The optimal strategy is `optPair lam μ`, chosen by `Classical.epsilon` among the optimal pairs of `HumanMachine.Alone.IsOptimal`. An optimum exists for $\mu\in[0,1]$ (a continuous objective on a compact square), and the optimal accuracy and value are the same at every optimum, so the choice is immaterial. $A^\star$ and $V^\star$ are **not** defined by their closed forms (13) and (15), which are theorems of the mission. $\lambda$ is written `lam`.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), pp. 6–8, §3.1, (1); p. 11, §4, (4), (7), (8) and footnote 8; p. 9 (definition of V⋆, A⋆); p. 12, §4.1

import Mathlib
import Definitions.Def_HumanMachine_Alone_model

namespace HumanMachine.Accuracy

/-- A chosen optimal pair `(p_g, p_b)`. For `μ ∈ [0, 1]` an optimum exists (a continuous
objective on the compact square), and the optimal accuracy and value do not depend on which
optimum is chosen; outside `[0, 1]` the choice is irrelevant to this development. -/
noncomputable def optPair (lam μ : ℝ) : ℝ × ℝ :=
  Classical.epsilon (fun q : ℝ × ℝ => HumanMachine.Alone.IsOptimal lam μ q.1 q.2)

/-- `A⋆(μ)`: the decision accuracy at the DM's optimal strategy, for prior `μ`. -/
noncomputable def AStar (lam μ : ℝ) : ℝ := HumanMachine.Alone.accuracy μ (optPair lam μ).1 (optPair lam μ).2

/-- `V⋆(μ)`: the DM's optimal expected value (accuracy net of cognitive cost), for prior `μ`. -/
noncomputable def VStar (lam μ : ℝ) : ℝ := HumanMachine.Alone.value lam μ (optPair lam μ).1 (optPair lam μ).2

end HumanMachine.Accuracy


