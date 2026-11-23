-- Prove2me | Definitions.Def_MulticlassQNet_SingleStation_Supplement_Closed
-- name    : MulticlassQNet_SingleStation_Supplement_Closed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:29:02.972794+00:00
-- url     : https://prove2.me/theorems/20d6661d-8044-4ba0-a5c4-3946c0a8c61a
-- title:
--   §6 — Assumption A(a) for a closed network with F customers
-- statement:
--   In a **closed** multiclass network (§6) there are no external arrivals ($\lambda_{0r}=0$) and no exits ($p_{r0}=0$, i.e. $\sum_s p_{rs}=1$), so the total number of customers $\sum_r n_r$ never changes. With $F$ customers present, the state space is $\{\vec n\in\mathbb N^R:\ \sum_r n_r=F\}$.
--
--   A distribution $\pi$ on states **lives on population $F$** if it gives zero mass to every state with $\sum_r n_r\ne F$. For a sequencing policy of §2, **Assumption A(a)** in the closed network says that $\pi$ is an invariant distribution of the policy's Markov chain living on population $F$, and that it is the only invariant distribution living on population $F$.
--
--   This is the hypothesis of Theorem 6.1. Assumption A(b) is not needed: the state space is finite.
--
--   **Formalization Note** Uniqueness is asked only among distributions living on population $F$. Requiring uniqueness over all of $\mathbb N^R$ would be unsatisfiable, since every population level carries its own invariant distribution.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), pp. 24–25, §6; Assumption A(a), p. 7

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics

namespace MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- `π` lives on the population-`F` states `{n : ∑_r n_r = F}` of a closed network (§6, p. 24). -/
def SupportedOnPopulation {R : ℕ} (F : ℕ) (π : (Fin R → ℕ) → ℝ) : Prop :=
  ∀ n, π n ≠ 0 → ∑ r, n r = F

/-- Assumption A(a) for a closed network with `F` customers (§6, p. 25): `π` is an invariant
distribution of the policy's chain living on the population-`F` states, and it is the unique
invariant distribution living on those states. (Uniqueness is not required across other
population levels, which the closed chain never visits.) -/
def ClosedAssumptionA {N R : ℕ} {net : Network N R} (P : Policy net) (F : ℕ)
    (π : (Fin R → ℕ) → ℝ) : Prop :=
  P.IsInvariant π ∧ SupportedOnPopulation F π ∧
    ∀ π', P.IsInvariant π' → SupportedOnPopulation F π' → π' = π

end MulticlassQNet.SingleStation.Supplement


