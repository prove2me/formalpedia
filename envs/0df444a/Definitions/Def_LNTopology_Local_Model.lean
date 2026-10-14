-- Prove2me | Definitions.Def_LNTopology_Local_Model
-- name    : LNTopology_Local_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:02.37918+00:00
-- url     : https://prove2.me/theorems/74d9b00a-7b83-4d28-af87-173da781e6b0
-- title:
--   §2–§2.2, pp. 4–5 — Lightning Network, supported flow, channel cost axioms (MO)–(SA), network cost, cost-minimizing network
-- statement:
--   This module fixes the model of §2 of Guasoni, Huberman and Shikhelman.
--
--   Let $V$ be a finite set of nodes and $c:\mathbb R\to\mathbb R_+$ a channel cost function.
--
--   1. **Lightning Network (LN).** A matrix $\Lambda=(\lambda_{u,v})_{u,v\in V}$ of real numbers, where $\lambda_{u,v}$ is the net flow from $u$ to $v$ in the channel between them ($\lambda_{u,v}=0$ when there is no channel), is a Lightning Network if it is anti-symmetric: $\lambda_{u,v}=-\lambda_{v,u}$ for all $u,v$.
--   2. **Support.** $\Lambda$ supports the payment flow $F=(f_i)_{i\in V}$ if for every node $i$
--   $$
--   \sum_{j\in V}\lambda_{i,j}=f_i .
--   $$
--   3. **Channel cost.** $c$ is a channel cost function if $c\ge 0$ and
--      - (MO) $c(x)>c(y)$ whenever $x>y\ge 0$;
--      - (SY) $c(-x)=c(x)$;
--      - (CI) $c(0)=0$;
--      - (SA) $c(x+y)<c(x)+c(y)$ for all $x,y>0$.
--   4. **Cost of a network.** $c(G)=\tfrac12\sum_{i,j\in V}c(\lambda_{i,j})$, which equals the sum of $c$ over the channels.
--   5. **Cost-minimizing.** $\Lambda$ is cost-minimizing for $F$ if it is an LN supporting $F$ and every LN $\Lambda'$ on the same node set $V$ that supports $F$ satisfies $c(\Lambda)\le c(\Lambda')$.
--
--   These are the objects every result of §3.1 is about: the theorems there show that certain local patterns can be removed at strictly lower cost, so a cost-minimizing network cannot contain them.
--
--   **Formalization Note** The node set is an arbitrary finite type rather than $\{1,\dots,n\}$, and the matrix is written `Λ` because `λ` is a Lean keyword. Support uses the row-sum display of §2.1, under which a net payer has $f_i>0$; the paper's examples (§2, Figure 1) use the opposite sign, and every statement of the paper is invariant under $F\mapsto -F$. The axiom (SA) is printed as "for $x>y\ge0$", which is unsatisfiable at $y=0$ ($c(x)<c(x)$); it is stated here for all $x,y>0$, the form Appendix D verifies. Alternatives in the definition of cost-minimizing range over networks on the same node set $V$ (no added hub). The paper's own words for the sign: the vector $F$ "describes the total flows out of each node" (p. 4), which is the row-sum display used here. The paper never defines "cost-minimizing" in a display; the definition is the one its proofs use (a supporting LN on the same nodes with strictly lower cost shows a network is not cost-minimizing, App. A).
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), pp. 4–5 (PDF 5–6), §2.1 (LN, support display), §2.2 ((MO), (SY), (CI), (SA), cost display), §3 (cost-minimizing)

import Mathlib

namespace LNTopology.Local

/-- A Lightning Network on the finite node set `V` (Guasoni–Huberman–Shikhelman, SSRN 4439190,
§2.1, p. 4): `Λ u v` is the net flow from `u` to `v` in the channel between them (`0` when there
is no channel), and the matrix is anti-symmetric, `Λ u v = -Λ v u`. -/
def IsLN {V : Type*} (Λ : V → V → ℝ) : Prop :=
  ∀ u v, Λ u v = -Λ v u

/-- The network `Λ` supports the payment flow `f` (§2.1, p. 4): for every node `i`,
`∑_j Λ i j = f i`. -/
def Supports {V : Type*} [Fintype V] (Λ : V → V → ℝ) (f : V → ℝ) : Prop :=
  ∀ i, ∑ j, Λ i j = f i

/-- A channel cost function `c : ℝ → ℝ₊` satisfying the axioms of §2.2 (p. 5):
(MO) monotonicity, (SY) symmetry, (CI) costless inaction, and (SA) strict subadditivity, the
latter in the corrected form `c (x + y) < c x + c y` for all `x, y > 0` (the printed range
`x > y ≥ 0` is unsatisfiable at `y = 0`; Appendix D verifies the axiom "for any x, y > 0"). -/
structure IsChannelCost (c : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ c x
  mono : ∀ x y, 0 ≤ y → y < x → c y < c x
  symm : ∀ x, c (-x) = c x
  zero : c 0 = 0
  subadd : ∀ x y, 0 < x → 0 < y → c (x + y) < c x + c y

/-- The cost of a network (§2.2, p. 5): `c(G) = ½ ∑_{i,j} c(λ_{i,j})`. -/
noncomputable def cost {V : Type*} [Fintype V] (c : ℝ → ℝ) (Λ : V → V → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, c (Λ i j)

/-- `Λ` is a cost-minimizing network for the flow `f` (§3): `Λ` is a Lightning Network on `V`
supporting `f`, and no Lightning Network on the same node set `V` supporting `f` costs less. -/
def IsCostMinimizing {V : Type*} [Fintype V] (c : ℝ → ℝ) (f : V → ℝ) (Λ : V → V → ℝ) : Prop :=
  IsLN Λ ∧ Supports Λ f ∧ ∀ Λ' : V → V → ℝ, IsLN Λ' → Supports Λ' f → cost c Λ ≤ cost c Λ'

end LNTopology.Local


