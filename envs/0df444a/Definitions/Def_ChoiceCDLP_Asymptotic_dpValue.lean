-- Prove2me | Definitions.Def_ChoiceCDLP_Asymptotic_dpValue
-- name    : ChoiceCDLP_Asymptotic_dpValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T06:33:17.563986+00:00
-- url     : https://prove2.me/theorems/8f498d47-0d28-4c15-af5f-644c831eff5b
-- title:
--   DP (1) with no overbooking: value-to-go V_t(x) and the optimal expected revenue V* = V_1(c)
-- statement:
--   For remaining capacity $x \in \mathbb{N}^m$, an offer set $S$ is **allowed** if no overbooking can occur, i.e. $x - A_j \ge 0$ for every $j \in S$; the empty set is always allowed. With $k$ periods remaining, the value-to-go $V^{(k)}$ is defined by $V^{(0)}(x) = 0$ and
--   $$V^{(k+1)}(x) = \max_{S \text{ allowed at } x} \Big\{ \sum_{j\in S} \lambda P_j(S)\big(r_j + V^{(k)}(x - A_j)\big) + \big(\lambda P_0(S) + 1 - \lambda\big) V^{(k)}(x) \Big\}.$$
--   This is the Bellman equation (1) of the paper with $V_t = V^{(T+1-t)}$ and terminal condition $V_{T+1} \equiv 0$. The **optimal expected revenue** over a horizon of $T$ periods from initial capacity $c$ is
--   $$V^*(c,T) = V^{(T)}(c) = V_1(c).$$
--
--   **Formalization Note.** The paper introduces $V^*$ as the value of the stochastic control problem (4) over nonanticipating admissible policies, and states that (4) is the DP (1) "written more abstractly"; here $V^*$ is defined directly by the recursion (1), without a measure-theoretic policy class. The paper's second boundary condition $V_t(0) = 0$ is not imposed separately: it follows from the recursion whenever every product uses at least one leg (a product is an itinerary), and imposing it on top of the recursion could contradict it when some product uses no leg. The subtraction $x - A_j$ is in $\mathbb{N}^m$ but is only evaluated for allowed $S$, where it does not truncate.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 292, §3.1, DP (1) and boundary conditions; p. 294, stochastic control problem (4)

import Mathlib
import Definitions.Def_ChoiceCDLP_Asymptotic_ChoiceNetwork

namespace ChoiceCDLP.Asymptotic

/-- Offer set `S` is allowed at remaining capacity `x` when no overbooking can occur:
`x - A_j ≥ 0` for every `j ∈ S` (p. 292). -/
def Allowed {m n : ℕ} (N : ChoiceNetwork m n) (x : Fin m → ℕ) (S : Finset (Fin n)) : Prop :=
  ∀ j ∈ S, ∀ i, N.A i j ≤ x i

instance {m n : ℕ} (N : ChoiceNetwork m n) (x : Fin m → ℕ) :
    DecidablePred (Allowed N x) :=
  fun S => by unfold Allowed; infer_instance

/-- The allowed offer sets at `x`; the empty offer set is always allowed. -/
def allowedSets {m n : ℕ} (N : ChoiceNetwork m n) (x : Fin m → ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (Allowed N x)

theorem allowedSets_nonempty {m n : ℕ} (N : ChoiceNetwork m n) (x : Fin m → ℕ) :
    (allowedSets N x).Nonempty :=
  ⟨∅, by simp [allowedSets, Allowed]⟩

/-- Value function of the DP (1), p. 292, indexed by the number `k` of periods remaining
(the paper's `V_t` is `valueToGo N (T + 1 - t)`): `valueToGo N 0 x = 0` (the boundary
condition `V_{T+1} ≡ 0`) and
`valueToGo N (k+1) x = max_{S allowed at x} { ∑_{j ∈ S} λ P_j(S) (r_j + valueToGo N k (x - A_j))
  + (λ P_0(S) + 1 - λ) valueToGo N k x }`. -/
noncomputable def valueToGo {m n : ℕ} (N : ChoiceNetwork m n) : ℕ → (Fin m → ℕ) → ℝ
  | 0, _ => 0
  | k + 1, x =>
    (allowedSets N x).sup' (allowedSets_nonempty N x) fun S =>
      ∑ j ∈ S, N.lam * N.P S j * (N.r j + valueToGo N k (x - fun i => N.A i j))
        + (N.lam * N.P0 S + 1 - N.lam) * valueToGo N k x

/-- `V*`: the optimal expected revenue over a horizon of `T` periods starting from initial
capacity `c`, i.e. `V_1(c)` of the DP (1), which (4) restates as a stochastic control problem. -/
noncomputable def dpValue {m n : ℕ} (N : ChoiceNetwork m n) (c : Fin m → ℕ) (T : ℕ) : ℝ :=
  valueToGo N T c

end ChoiceCDLP.Asymptotic


