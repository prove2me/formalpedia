-- Prove2me | Definitions.Def_BudgetCoreExchange_InCore
-- name    : BudgetCoreExchange_InCore
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:03.95243+00:00
-- url     : https://prove2.me/theorems/0ec6ce2c-ae37-463b-8870-203e25aadd98
-- title:
--   Feasible outcomes, welfare and the core of a budget-constrained combinatorial exchange (CEx)
-- statement:
--   Fix an exchange with buyers $I$, sellers $J$, items $K$. An **outcome** assigns to every buyer $i$ a package $S_i\subseteq K$ ($\emptyset$ = nothing) and a payment $p_i$, and to every seller $j$ a supplied package $Z_j$ and a receipt $q_j$.
--
--   A **coalition** $C$ is a pair of sets $I(C)\subseteq I$, $J(C)\subseteq J$. An outcome is **feasible for $C$** if
--
--   1. (BC) $0\le p_i\le\min\{B_i,\,v_i(S_i)\}$ for every $i\in I(C)$;
--   2. (IRS) $Z_j\subseteq K(j)$, $q_j\ge0$ and $q_j\ge v_j(Z_j)$ for every $j\in J(C)$;
--   3. (BB) $\sum_{i\in I(C)}p_i=\sum_{j\in J(C)}q_j$;
--   4. (Supply) every item $k$ lies in the packages of at most as many buyers of $C$ as it lies in packages supplied by sellers of $C$.
--
--   An outcome is **feasible** if it is feasible for the grand coalition $N=I\cup J$. Payoffs are $\pi_i=v_i(S_i)-p_i$ and $\pi_j=q_j-v_j(Z_j)$, and the **welfare** (gains from trade) is
--   $$
--   \sum_{i\in I}v_i(S_i)-\sum_{j\in J}v_j(Z_j).
--   $$
--   A coalition $C$ **blocks** an outcome $o$ if some outcome feasible for $C$ gives every member of $C$ a strictly larger payoff than $o$. A **core outcome** is a feasible outcome blocked by no nonempty coalition (the grand coalition included).
--
--   These are the upper level, the lower levels and the constraint (Core) $d^C\le0$ of the bilevel program (CEx): $d^C>0$ exactly when some outcome feasible for $C$ strictly improves every member.
--
--   **Formalization Note** The package prices $p_i(S)x_i(S)$ of (CEx) become one payment per agent, as the paper itself remarks (p.12). Payments are real. A seller's improvement is measured in payoffs; the printed (Imp-S) compares payments only, which is the same when sellers value nothing, as in Appendix A. The empty coalition is excluded because it would block every outcome.
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, §2, p.7 (payoffs); program (CEx), p.11, and its explanation, p.12

import Mathlib
import Definitions.Def_BudgetCoreExchange_Exchange

namespace BudgetCoreExchange

/-- An **outcome** of an exchange (the upper-level variables of (CEx), Bichler–Waldherr,
arXiv:1807.08253v1, p.11): the package `S i` obtained by each buyer (`∅` = nothing), the package
`Z j` supplied by each seller, the payment `p i ≥ 0` made by each buyer and the payment `q j ≥ 0`
received by each seller.

**Formalization Note.** (CEx) has binary variables `xᵢ(S)`, `yⱼ(Z)` with (XOR-B), (XOR-S) (at most
one package per agent) and package prices `pᵢ(S)`, `pⱼ(Z)`; as noted on p.12, the bilinear terms
`Σ_S pᵢ(S)xᵢ(S)` are a single payment per agent. An agent holding no package is encoded by the
package `∅`, which is equivalent: (BC) forces the payment for `∅` to be `0`. -/
structure Outcome (Buyer Seller Item : Type) where
  S : Buyer → Finset Item
  Z : Seller → Finset Item
  p : Buyer → ℝ
  q : Seller → ℝ

/-- A **coalition** `C ⊆ N = I ∪ J`: its buyers `I(C)` and its sellers `J(C)`. -/
structure Coalition (Buyer Seller : Type) where
  buyers : Finset Buyer
  sellers : Finset Seller

/-- A coalition is nonempty if it has at least one buyer or seller. -/
def Coalition.Nonempty {Buyer Seller : Type} (C : Coalition Buyer Seller) : Prop :=
  C.buyers.Nonempty ∨ C.sellers.Nonempty

/-- The grand coalition `N = I ∪ J`. -/
def Coalition.grand (Buyer Seller : Type) [Fintype Buyer] [Fintype Seller] :
    Coalition Buyer Seller :=
  ⟨Finset.univ, Finset.univ⟩

variable {Buyer Seller Item : Type} [Fintype Buyer] [Fintype Seller] [DecidableEq Item]

/-- An outcome `o` is **feasible for the coalition `C`** (the lower level of (CEx), p.11, for `C`;
for the grand coalition, the upper level): only the members of `C` are constrained, and
* (BC) every buyer `i ∈ I(C)` pays `0 ≤ pᵢ ≤ min(Bᵢ, vᵢ(Sᵢ))`;
* (IRS) every seller `j ∈ J(C)` supplies items endowed to him, `Zⱼ ⊆ K(j)` (p.12), and receives
  `qⱼ ≥ vⱼ(Zⱼ)`, `qⱼ ≥ 0`;
* (BB) `Σ_{i ∈ I(C)} pᵢ = Σ_{j ∈ J(C)} qⱼ`;
* (Supply) every item `k` is in the packages of at most as many buyers of `C` as it is in the
  packages supplied by sellers of `C`.

The values of `o` at agents outside `C` are ignored. -/
def FeasibleFor (E : Exchange Buyer Seller Item ℝ) (C : Coalition Buyer Seller)
    (o : Outcome Buyer Seller Item) : Prop :=
  (∀ i ∈ C.buyers, 0 ≤ o.p i ∧ o.p i ≤ min (E.budget i) (E.bval i (o.S i))) ∧
  (∀ j ∈ C.sellers, o.Z j ⊆ E.endow j ∧ 0 ≤ o.q j ∧ E.sval j (o.Z j) ≤ o.q j) ∧
  (∑ i ∈ C.buyers, o.p i = ∑ j ∈ C.sellers, o.q j) ∧
  ∀ k : Item, (C.buyers.filter fun i => k ∈ o.S i).card ≤
    (C.sellers.filter fun j => k ∈ o.Z j).card

/-- A **feasible outcome** of the exchange: the constraints (BC), (IRS), (BB), (Supply), (XOR-B),
(XOR-S) of the upper level of (CEx), p.11, i.e. `FeasibleFor` the grand coalition. -/
def Feasible (E : Exchange Buyer Seller Item ℝ) (o : Outcome Buyer Seller Item) : Prop :=
  FeasibleFor E (Coalition.grand Buyer Seller) o

/-- The payoff `πᵢ = vᵢ(Sᵢ) − pᵢ` of buyer `i` (p.7). -/
def buyerPayoff (E : Exchange Buyer Seller Item ℝ) (o : Outcome Buyer Seller Item) (i : Buyer) : ℝ :=
  E.bval i (o.S i) - o.p i

/-- The payoff `πⱼ = qⱼ − vⱼ(Zⱼ)` of seller `j` (p.7). -/
def sellerPayoff (E : Exchange Buyer Seller Item ℝ) (o : Outcome Buyer Seller Item) (j : Seller) : ℝ :=
  o.q j - E.sval j (o.Z j)

/-- The **welfare** (gains from trade) of an outcome, the objective of (CEx), p.11:
`Σᵢ vᵢ(Sᵢ) − Σⱼ vⱼ(Zⱼ)`. -/
def welfare (E : Exchange Buyer Seller Item ℝ) (o : Outcome Buyer Seller Item) : ℝ :=
  ∑ i, E.bval i (o.S i) - ∑ j, E.sval j (o.Z j)

/-- The coalition `C` **blocks** the outcome `o`: some outcome `o'` feasible for `C` gives every
member of `C` a strictly larger payoff than `o` does. This is `d^C > 0` in (CEx), p.11, where
`d^C` is the largest achievable minimum improvement over the members of `C` ((Imp-B), (Imp-S)). -/
def Blocks (E : Exchange Buyer Seller Item ℝ) (C : Coalition Buyer Seller)
    (o : Outcome Buyer Seller Item) : Prop :=
  ∃ o' : Outcome Buyer Seller Item, FeasibleFor E C o' ∧
    (∀ i ∈ C.buyers, buyerPayoff E o i < buyerPayoff E o' i) ∧
    ∀ j ∈ C.sellers, sellerPayoff E o j < sellerPayoff E o' j

/-- A **core outcome** (Bichler–Waldherr, arXiv:1807.08253v1, (CEx), pp.11–12): a feasible
outcome that no nonempty coalition `C ⊆ N` blocks ("(Core) d^C ≤ 0 ∀ C"; "the prices have to be
set in such a way, that no coalition can benefit from deviating", p.12).

**Formalization Note.**
* Coalitions are all nonempty subsets of `N`, the grand coalition included (the empty coalition
  would block vacuously).
* Blocking requires a strict improvement of every member (`d^C > 0`).
* A seller's improvement is measured in payoffs `qⱼ − vⱼ(Zⱼ)` (p.7, "the improvements for each
  individual buyer and seller", p.12); the printed (Imp-S) compares payments only. The two agree
  when sellers value every package at `0`, as in the reduction of Appendix A.3.
* Payments are real numbers (`ℝ⁺₀` in (CEx)). -/
def InCore (E : Exchange Buyer Seller Item ℝ) (o : Outcome Buyer Seller Item) : Prop :=
  Feasible E o ∧ ∀ C : Coalition Buyer Seller, C.Nonempty → ¬ Blocks E C o

end BudgetCoreExchange


