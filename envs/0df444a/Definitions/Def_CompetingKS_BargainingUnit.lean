-- Prove2me | Definitions.Def_CompetingKS_BargainingUnit
-- name    : CompetingKS_BargainingUnit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:49.947191+00:00
-- url     : https://prove2.me/theorems/bbb789d9-7a24-4dc7-b5dd-099fb2f6f31b
-- title:
--   Bargaining units: individual rationality, Pareto optimality, the maxima (9)–(10), the Nash solution (1) and the Kalai–Smorodinsky solution (2)
-- statement:
--   A **bargaining unit** is a two-party bargaining problem over a one-dimensional contract. It consists of a set $W\subseteq\mathbb R$ of contracts, the seller's profit $S(w)$ and the buyer's profit $B(w)$ at contract $w$, and a **disagreement point** $(D,d)$, the profits of the seller and of the buyer if the negotiation fails. The set of profit allocations is $\{(S(w),B(w)):w\in W\}$.
--
--   A contract $w$ is **individually rational** if $w\in W$, $S(w)\ge D$ and $B(w)\ge d$. It is **Pareto-dominated** if some $w'\in W$ has $S(w')\ge S(w)$, $B(w')\ge B(w)$ and one of these inequalities strict, and **Pareto optimal** if it lies in $W$ and is not dominated. The **maximum profits** of the two parties are
--   $$
--   \overline S=\max\{S(w):w\in W,\ B(w)\ge d\},\qquad \overline B=\max\{B(w):w\in W,\ S(w)\ge D\}.
--   $$
--   Each is constrained by the individual rationality of the other party only.
--
--   Given the buyer's bargaining power $\theta$, the **generalized Nash bargaining solution** is an individually rational contract maximizing the Nash product
--   $$
--   \Omega(w)=(B(w)-d)^{\theta}\,(S(w)-D)^{1-\theta}
--   $$
--   over the individually rational contracts. The **Kalai–Smorodinsky solution** is an individually rational, Pareto optimal contract whose surpluses are proportional to the maximum surpluses,
--   $$
--   \frac{B(w)-d}{S(w)-D}=\frac{\overline B-d}{\overline S-D}.
--   $$
--
--   These are the two solution concepts of the mission, stated for an arbitrary unit so that the one-to-two and two-to-one channels are two instances.
--
--   **Formalization Note** The maxima are `sSup` of the image of the constraint set, and `IsSMaximizer`, `IsBMaximizer` record attainment, which Lemmas A.1 and A.4 prove for the concrete units. The ratio equation is cross-multiplied. The power is `Real.rpow`, with $0^0=1$ at $\theta\in\{0,1\}$; the product is only compared on individually rational contracts, where both bases are nonnegative. Pareto optimality is part of the Kalai–Smorodinsky solution: without it every contract with allocation $(D,d)$ would satisfy the equation as $0=0$.
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, §3, (1), p.7; (2), p.11; (9)–(10), p.17; online appendix p.3 (feasibility), p.5 (Pareto)

import Mathlib

namespace CompetingKS

/-- A bilateral bargaining problem over a one-dimensional contract, the object Feng, Li,
Shanthikumar, *Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution*,
accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, §3, pp.6–11 and §5.1.1, p.17
solve: a set `W` of contracts, the seller's profit `S w` and the buyer's profit `B w` at contract
`w`, and the disagreement point `(D, d)`, the seller's and the buyer's profit when the negotiation
fails. The profit allocation set of the paper is `{(S w, B w) : w ∈ W}`.

**Formalization Note** Nothing is assumed here about `W`, `S`, `B`: the structure carries data
only. Every result of the mission is about the concrete units `unitOT`, `unitTO`. -/
structure BargainingUnit where
  /-- The contract space. -/
  W : Set ℝ
  /-- The seller's (supplier's) profit at a contract. -/
  S : ℝ → ℝ
  /-- The buyer's (retailer's) profit at a contract. -/
  B : ℝ → ℝ
  /-- The seller's disagreement point. -/
  D : ℝ
  /-- The buyer's disagreement point. -/
  d : ℝ

namespace BargainingUnit

variable (U : BargainingUnit)

/-- Individual rationality: `w` is a contract and gives each party at least its disagreement
profit, so that both trade surpluses `S w - D`, `B w - d` are nonnegative (Feng, Li, Shanthikumar,
SSRN 3447674, online appendix p.3, "any feasible (wᵢ, wⱼ) should lead to nonnegative trade
surpluses"). -/
def IsIR (w : ℝ) : Prop := w ∈ U.W ∧ U.D ≤ U.S w ∧ U.d ≤ U.B w

/-- The allocation of `w` is Pareto-dominated within the unit's allocation set: some contract
gives both parties at least as much and one of them strictly more (axiom (i), Feng, Li,
Shanthikumar, SSRN 3447674, p.7). -/
def IsDominated (w : ℝ) : Prop :=
  ∃ w' ∈ U.W, U.S w ≤ U.S w' ∧ U.B w ≤ U.B w' ∧ (U.S w < U.S w' ∨ U.B w < U.B w')

/-- The contract `w` gives a Pareto optimal allocation of the unit's allocation set. -/
def IsPareto (w : ℝ) : Prop := w ∈ U.W ∧ ¬ U.IsDominated w

/-- The seller's maximum profit, display (9) of Feng, Li, Shanthikumar, SSRN 3447674, p.17:
`Π̄ = max {S w : B w ≥ d}`. The constraint is the buyer's individual rationality only.

**Formalization Note** `sSup` of an empty or unbounded set is `0` in Lean. Lemmas A.1 and A.4
(`lemma_A_1`, `lemma_A_4`) state that for the normalized units the supremum is attained at an
explicit contract; `IsSMaximizer` records attainment. -/
noncomputable def Sbar : ℝ := sSup (U.S '' {w ∈ U.W | U.d ≤ U.B w})

/-- The buyer's maximum profit, display (10) of Feng, Li, Shanthikumar, SSRN 3447674, p.17:
`π̄ = max {B w : S w ≥ D}`. The constraint is the seller's individual rationality only. The note on
`Sbar` applies. -/
noncomputable def Bbar : ℝ := sSup (U.B '' {w ∈ U.W | U.D ≤ U.S w})

/-- `x` attains the maximum in (9): it is a contract with `B x ≥ d` and it maximizes `S` over all
such contracts. -/
def IsSMaximizer (x : ℝ) : Prop :=
  x ∈ U.W ∧ U.d ≤ U.B x ∧ ∀ w ∈ U.W, U.d ≤ U.B w → U.S w ≤ U.S x

/-- `x` attains the maximum in (10): it is a contract with `S x ≥ D` and it maximizes `B` over all
such contracts. -/
def IsBMaximizer (x : ℝ) : Prop :=
  x ∈ U.W ∧ U.D ≤ U.S x ∧ ∀ w ∈ U.W, U.D ≤ U.S w → U.B w ≤ U.B x

/-- The generalized Nash product of display (1) of Feng, Li, Shanthikumar, SSRN 3447674, p.7:
`Ω = (π - d)^θ (Π - D)^(1-θ)`, where `θ` is the retailer's (buyer's) bargaining power.

**Formalization Note** The power is `Real.rpow`, the ordinary real power on nonnegative bases; the
product is only compared over individually rational contracts (`IsNBResponse`), where both bases
are nonnegative. `0 ^ 0 = 1` is the convention at `θ ∈ {0, 1}`. -/
noncomputable def nashProduct (θ w : ℝ) : ℝ :=
  (U.B w - U.d) ^ θ * (U.S w - U.D) ^ (1 - θ)

/-- The generalized Nash bargaining solution (1): `w` is individually rational and maximizes the
Nash product over the individually rational contracts. -/
def IsNBResponse (θ w : ℝ) : Prop :=
  U.IsIR w ∧ ∀ w', U.IsIR w' → U.nashProduct θ w' ≤ U.nashProduct θ w

/-- The Kalai-Smorodinsky solution: `w` is individually rational, its allocation is Pareto
optimal, and the surpluses satisfy equation (2) of Feng, Li, Shanthikumar, SSRN 3447674, p.11,
`(π - d)/(Π - D) = (π̄ - d)/(Π̄ - D)`.

**Formalization Note** (2) is cross-multiplied, so that it stays meaningful at `S w = D`. Pareto
optimality is part of the solution, as in axiom (i), p.7, and in the paper's derivation ("the best
response should lead to a Pareto profit allocation", online appendix p.5): without it every
contract with allocation `(D, d)` would satisfy (2) as `0 = 0`. -/
def IsKSResponse (w : ℝ) : Prop :=
  U.IsIR w ∧ U.IsPareto w ∧ (U.B w - U.d) * (U.Sbar - U.D) = (U.S w - U.D) * (U.Bbar - U.d)

end BargainingUnit

end CompetingKS


