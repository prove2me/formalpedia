-- Prove2me | Definitions.Def_ChoiceCDLP_Asymptotic_cdlpValue
-- name    : ChoiceCDLP_Asymptotic_cdlpValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T06:32:54.635554+00:00
-- url     : https://prove2.me/theorems/a2b7cb9b-cb9b-4808-9adf-a49682fe5ced
-- title:
--   CDLP (2): feasible time allocations t(S) and the optimal value V^CDLP(c, T)
-- statement:
--   Given a choice-based network instance, capacities $c = (c_1,\dots,c_m) \in \mathbb{N}^m$ and a horizon of $T \in \mathbb{N}$ periods, a vector of times $t = (t(S))_{S \subseteq N}$ is **feasible for the CDLP** if
--   $$\sum_{S\subseteq N} \lambda\, Q(S)\, t(S) \le c,\qquad \sum_{S \subseteq N} t(S) \le T,\qquad t(S) \ge 0\ \ \forall S \subseteq N,$$
--   the first inequality holding componentwise. The **CDLP value** is
--   $$V^{\mathrm{CDLP}}(c,T) = \max\Big\{ \sum_{S \subseteq N} \lambda R(S)\, t(S) \;:\; t \text{ feasible} \Big\}.$$
--   The CDLP treats demand as deterministic and lets $t(S)$, the total time during which offer set $S$ is used, be fractional.
--
--   **Formalization Note.** The value is `sSup` of the objective over the feasible set. That set is nonempty ($t \equiv 0$ is feasible because $c \ge 0$, $T \ge 0$) and the objective is bounded on it ($0 \le t(S) \le T$ over finitely many $S$), so `sSup` is the LP's optimal value, and it is attained (the LP is feasible and bounded). The variables $t(S)$ are real; capacities and horizon are natural numbers because they also parametrize the stochastic problem.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 293, CDLP (2)

import Mathlib
import Definitions.Def_ChoiceCDLP_Asymptotic_ChoiceNetwork

namespace ChoiceCDLP.Asymptotic

/-- Feasibility for the choice-based deterministic linear program (CDLP) (2), p. 293, with
capacity vector `c` and horizon `T`: `t(S) ≥ 0` for every offer set `S ⊆ N`,
`∑_S λ Q(S) t(S) ≤ c` componentwise, and `∑_S t(S) ≤ T`. -/
def cdlpFeasible {m n : ℕ} (N : ChoiceNetwork m n) (c : Fin m → ℕ) (T : ℕ)
    (t : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ t S) ∧
  (∀ i, ∑ S : Finset (Fin n), N.lam * N.Q S i * t S ≤ (c i : ℝ)) ∧
  ∑ S : Finset (Fin n), t S ≤ (T : ℝ)

/-- CDLP objective `∑_{S ⊆ N} λ R(S) t(S)`. -/
def cdlpObjective {m n : ℕ} (N : ChoiceNetwork m n) (t : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), N.lam * N.R S * t S

/-- Optimal value `V^CDLP` of the CDLP (2): the supremum of the objective over the feasible
set. The feasible set is nonempty (`t = 0`) and the objective is bounded on it
(`0 ≤ t`, `∑_S t(S) ≤ T`, finitely many `S`), so this is the LP's true optimal value. -/
noncomputable def cdlpValue {m n : ℕ} (N : ChoiceNetwork m n) (c : Fin m → ℕ) (T : ℕ) : ℝ :=
  sSup (cdlpObjective N '' {t | cdlpFeasible N c T t})

end ChoiceCDLP.Asymptotic


