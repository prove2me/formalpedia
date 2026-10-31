-- Prove2me | Definitions.Def_ExitSpirals_activity
-- name    : ExitSpirals_activity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:03.926456+00:00
-- url     : https://prove2.me/theorems/f832d114-247d-48d8-a69c-45b409373ea0
-- title:
--   Best response (4), equilibria, maximal equilibrium and activity
-- statement:
--   Fix two networks $E_R, E_C$ on $N=\{1,\dots,n\}$ and a set $W$ of **shocked** agents. For a set $A$ of active agents, the **best response** (4) makes agent $i$ active exactly when
--   $$i\notin W,\qquad \exists j\in A:\ (j\to i)\in E_R,\qquad \exists j\in A:\ (j\to i)\in E_C,$$
--   i.e. $i$ is unshocked and has at least one active supporter in each market. A set $A$ is an **equilibrium** if the best response to $A$ is $A$ itself.
--
--   The **maximal equilibrium** $y^*$ is the union of all equilibria; Proposition 2 shows it is an equilibrium, so it dominates every other equilibrium pointwise. The **activity** is the fraction of agents active in it,
--   $$\mathcal A(E_R,E_C,W)=\frac{|y^*|}{n}.$$
--
--   **Formalization Note** The best response (4) is taken as the primitive of the game with the shocked set $W$ as datum: costs, the benefit function $b$ and Assumptions 4.1–4.2 do not appear, because Assumption 4.2's cost law is not a distribution function as printed. The networks in (4) are the unstripped ones; the condition $i\notin W$ and the requirement of active supporters already ignore the shocked agents' links. At $n=0$ the activity is $0$.
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), (3), p.10 (activity of the maximal equilibrium); Assumption 4.1, p.21; (4), p.22 (best response)

import Mathlib
import Definitions.Def_ExitSpirals_Network

namespace ExitSpirals

/-- **The best response (4).**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, (4), p.22:
"R_i(a_{−i}) = 1 if i ∉ W and S_{i,R}(a_{−i}) · S_{i,C}(a_{−i}) > 0, and 0 otherwise", where
`S_{i,µ} = Σ_{j ∈ K⁻_{i,µ}} a_{j,µ}` (Assumption 4.1, p.21).

`bestResponse ER EC W A` is the set of agents active in `R(a)` when `A` is the set of active
agents: those not in the shocked set `W` with at least one active in-neighbour in `ER` and at
least one in `EC`.

**Formalization Note.** The rule (4) is taken as the primitive of the game, with the shocked set
`W` as a datum (the paper's identification of W with the cost draw, p.22). The costs, the benefit
function `b` and Assumptions 4.1–4.2 do not appear: as printed, Assumption 4.2's `F(c, x)` is not
a distribution function. Actions are the one-dimensional `y_i` of p.22, encoded by the set of
active agents. The networks here are the unstripped ones; the condition `i ∉ W` and the
requirement that supporting neighbours be active already ignore the shocked agents' links. -/
def bestResponse {n : ℕ} (ER EC : Network n) (W A : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ∉ W ∧ (∃ j ∈ A, (j, i) ∈ ER) ∧ (∃ j ∈ A, (j, i) ∈ EC)

/-- An equilibrium action profile: a fixed point `R(y) = y` of the best response (pp.10, 24). -/
def IsEquilibrium {n : ℕ} (ER EC : Network n) (W A : Finset (Fin n)) : Prop :=
  bestResponse ER EC W A = A

instance {n : ℕ} (ER EC : Network n) (W A : Finset (Fin n)) :
    Decidable (IsEquilibrium ER EC W A) :=
  inferInstanceAs (Decidable (bestResponse ER EC W A = A))

/-- **The maximal equilibrium** (p.10): "the action profile y played in this equilibrium pointwise
dominates the vector y′ corresponding to any other equilibrium". Defined as the union of the
active sets of all equilibria; that this union is itself an equilibrium is part of Proposition 2
(the milestone `ExitSpirals.proposition_2`). -/
def maxEq {n : ℕ} (ER EC : Network n) (W : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ A : Finset (Fin n), IsEquilibrium ER EC W A ∧ i ∈ A

/-- **Activity** (3), p.10: the fraction of active agents in the maximal equilibrium,
`A = |{i : y*_i = 1}| / n`, for the given networks and shocked set.

**Formalization Note.** (3) maximizes the expected fraction over equilibria; the maximal
equilibrium attains the maximum. At `n = 0` the value is `0 / 0 = 0`. -/
noncomputable def activity {n : ℕ} (ER EC : Network n) (W : Finset (Fin n)) : ℝ :=
  ((maxEq ER EC W).card : ℝ) / n

end ExitSpirals


