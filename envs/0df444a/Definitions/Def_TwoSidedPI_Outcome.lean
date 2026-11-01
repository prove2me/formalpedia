-- Prove2me | Definitions.Def_TwoSidedPI_Outcome
-- name    : TwoSidedPI_Outcome
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:46.420106+00:00
-- url     : https://prove2.me/theorems/ceaf2510-dbb1-480a-bc7a-ddac41a50f1a
-- title:
--   Outcomes, utilities, welfare, DSIC, IR and direct-trade strong budget balance
-- statement:
--   In a double auction with unit-demand buyers $B$, unit-supply sellers $S$ and identical items, an **outcome** consists of the set of buyers who receive an item, the set of sellers who hold their item at the end, the payment $\pi_i$ made by each buyer and the payment $\rho_j$ received by each seller. With value $x$ for an item, the quasi-linear utility is
--   $$
--   u_i=x\cdot\mathbf 1[i\text{ served}]-\pi_i\quad(\text{buyer}),\qquad u_j=x\cdot\mathbf 1[j\text{ keeps}]+\rho_j\quad(\text{seller}),
--   $$
--   and the social welfare at a profile $v$ is $\sum_{i\text{ served}}v_i+\sum_{j\text{ keeps}}v_j$.
--
--   A mechanism, a map from report profiles $b\in[0,\infty)^{B\cup S}$ to outcomes, is
--
--   1. **DSIC** if for every agent $a$, every true value $x\ge0$ and every report profile $b$ (including $a$'s own report), reporting $x$ gives $a$ at least the utility of reporting $b_a$;
--   2. **IR** if for every report profile $b$, a truthful buyer $i$ has utility $\ge0$ and a truthful seller $j$ has utility $\ge b_j$, her value for the item she started with;
--   3. **DSBB** (direct-trade strongly budget-balanced) if for every report profile the outcome is a composition of bilateral trades $(i,j,p)$, with distinct buyers and distinct sellers, in which seller $j$'s item goes to buyer $i$ and buyer $i$ pays exactly $p$ to seller $j$: a buyer is served iff she is in a trade and pays its price, and a seller keeps her item iff she is in no trade and otherwise receives its price.
--
--   These are the properties Theorem 1 asserts for Mechanism 1.
--
--   **Formalization Note** Payments are recorded as two nonnegative-direction fields (`pay`, `recv`) instead of the paper's signed $P$. The outcome type carries no trade structure, so DSBB is a genuine property of the payments and allocation.
-- source:
--   Braun, Kesselheim, Truthful Mechanisms for Two-Sided Markets via Prophet Inequalities, arXiv:2105.15032v1, §2, p.7 (utilities, DSIC, IR, DWBB/DSBB, welfare)

import Mathlib

namespace TwoSidedPI

/-- The outcome of a mechanism in a double auction with unit-demand buyers `B` and unit-supply
sellers `S` and identical items (Braun, Kesselheim, arXiv:2105.15032v1, §2, p.7 and §3, p.8):
the allocation (`served`: the buyers who receive an item; `keeps`: the sellers who hold their
item at the end) and the payments (`pay i`: the money buyer `i` pays; `recv j`: the money seller
`j` receives).

**Formalization Note** The paper's sign convention (buyers' payments negative) is replaced by
two nonnegative-direction fields `pay` and `recv`; the outcome type does not presuppose any
trade structure, so budget balance is a property (`IsDSBB`), not a typing artefact. -/
structure Outcome (B S : Type*) where
  /-- The buyers who are allocated an item. -/
  served : Finset B
  /-- The sellers who hold their item at the end. -/
  keeps : Finset S
  /-- The payment made by each buyer. -/
  pay : B → ℝ
  /-- The payment received by each seller. -/
  recv : S → ℝ

variable {B S : Type*} [DecidableEq B] [DecidableEq S]

/-- The quasi-linear utility of agent `a` with value `x` for an item at outcome `o`
(Braun, Kesselheim, arXiv:2105.15032v1, §2, p.7): `u_i = v_i(X_i) − P_i` for a buyer and
`u_l = v_l(X_l) + P_l` for a seller, where a unit-demand buyer's value of her bundle is `x` if
she gets an item and `0` otherwise, and a unit-supply seller's is `x` if she keeps her item. -/
def utility (o : Outcome B S) : B ⊕ S → ℝ → ℝ
  | Sum.inl i, x => (if i ∈ o.served then x else 0) - o.pay i
  | Sum.inr j, x => (if j ∈ o.keeps then x else 0) + o.recv j

/-- The social welfare `v(X) = ∑_{i ∈ B ∪ S} v_i(X_i)` of an outcome at the value profile `v`
(Braun, Kesselheim, arXiv:2105.15032v1, §2, p.7). -/
def welfare [Fintype B] [Fintype S] (o : Outcome B S) (v : B ⊕ S → ℝ) : ℝ :=
  ∑ i ∈ o.served, v (Sum.inl i) + ∑ j ∈ o.keeps, v (Sum.inr j)

/-- Dominant-strategy incentive compatibility (Braun, Kesselheim, arXiv:2105.15032v1, §2, p.7):
for every agent `a`, every true value `x ≥ 0` and every report profile `b` with nonnegative
entries (the other agents' reports and `a`'s own misreport `b a`), reporting `x` gives `a` at
least the utility of reporting `b a`.

**Formalization Note** In the unit-demand, unit-supply setting a valuation is one number, so the
report space `V_a` is `[0, ∞)`. -/
def IsDSIC (mech : (B ⊕ S → ℝ) → Outcome B S) : Prop :=
  ∀ b : B ⊕ S → ℝ, (∀ a, 0 ≤ b a) → ∀ (a : B ⊕ S) (x : ℝ), 0 ≤ x →
    utility (mech b) a x ≤ utility (mech (Function.update b a x)) a x

/-- Individual rationality (Braun, Kesselheim, arXiv:2105.15032v1, §2, p.7): when an agent
reports truthfully, whatever the others report, a buyer's utility is `v_i(X_i) − P_i ≥ 0` and a
seller's is `v_l(X_l) + P_l ≥ v_l(I_l)`, where `v_l(I_l)` is her value `b l` for her one item. -/
def IsIR (mech : (B ⊕ S → ℝ) → Outcome B S) : Prop :=
  ∀ b : B ⊕ S → ℝ, (∀ a, 0 ≤ b a) →
    (∀ i : B, 0 ≤ utility (mech b) (Sum.inl i) (b (Sum.inl i))) ∧
    (∀ j : S, b (Sum.inr j) ≤ utility (mech b) (Sum.inr j) (b (Sum.inr j)))

/-- Direct-trade strong budget balance, DSBB (Braun, Kesselheim, arXiv:2105.15032v1, §2, p.7,
after Colini-Baldeschi et al. 2020): for every report profile, the outcome is a composition of
bilateral trades `(i, j, p)`, in each of which seller `j`'s item goes to buyer `i` and buyer `i`
pays `p` to seller `j` (equal payments), each item being traded at most once.

**Formalization Note** With unit-demand buyers and unit-supply sellers the trades form a finite
set `T` of triples with pairwise distinct buyers and pairwise distinct sellers. A buyer is
served iff she is in a trade, and pays its price; a seller keeps her item iff she is in no trade,
and otherwise receives its price; agents in no trade pay and receive `0`. -/
def IsDSBB [Fintype B] [Fintype S] (mech : (B ⊕ S → ℝ) → Outcome B S) : Prop :=
  ∀ b : B ⊕ S → ℝ, (∀ a, 0 ≤ b a) → ∃ T : Finset (B × S × ℝ),
    (∀ t ∈ T, ∀ t' ∈ T, t.1 = t'.1 → t = t') ∧
    (∀ t ∈ T, ∀ t' ∈ T, t.2.1 = t'.2.1 → t = t') ∧
    (∀ i : B, i ∈ (mech b).served ↔ ∃ t ∈ T, t.1 = i) ∧
    (∀ j : S, j ∈ (mech b).keeps ↔ ∀ t ∈ T, t.2.1 ≠ j) ∧
    (∀ i : B, (mech b).pay i = ∑ t ∈ T with t.1 = i, t.2.2) ∧
    (∀ j : S, (mech b).recv j = ∑ t ∈ T with t.2.1 = j, t.2.2)

end TwoSidedPI


