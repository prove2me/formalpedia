-- Prove2me | Definitions.Def_LNTopology_StarBound_Model
-- name    : LNTopology_StarBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:43.006014+00:00
-- url     : https://prove2.me/theorems/459f9081-9e11-4531-bdc8-3c2b1bae691c
-- title:
--   §2.1–§2.2 — Lightning Networks, supporting a payment flow, channel cost axioms (MO)–(SA), network cost
-- statement:
--   This module fixes the model of §2 of Guasoni, Huberman and Shikhelman.
--
--   Let $V$ be a finite set of nodes. A **payment flow** is a vector $\mathcal F=(f_i)_{i\in V}$ of real numbers, the net flow of each node.
--
--   1. **Lightning Network (LN).** A matrix $\Lambda=(\lambda_{i,j})_{i,j\in V}$ of real numbers, where $\lambda_{u,v}$ is the net flow from $u$ to $v$ in the channel between them and $\lambda_{u,v}=0$ means that there is no channel. It is anti-symmetric:
--   $$\lambda_{u,v}=-\lambda_{v,u}\qquad\text{for all }u,v\in V.$$
--   2. **Supporting a flow.** The LN $\Lambda$ supports $\mathcal F$ if, for every node $i$, the net flows of the channels involving $i$ add up to the flow of $i$:
--   $$\sum_{j\in V}\lambda_{i,j}=f_i .$$
--   3. **Channel cost function.** A function $c:\mathbb R\to\mathbb R_+$ with
--      - (MO) $c(x)>c(y)$ whenever $x>y\ge 0$;
--      - (SY) $c(-x)=c(x)$;
--      - (CI) $c(0)=0$;
--      - (SA) $c(x+y)<c(x)+c(y)$ for all $x,y>0$.
--   4. **Cost of a network.**
--   $$c(G)=\frac12\sum_{i,j\in V}c(\lambda_{i,j}),$$
--   the sum of the costs of all channels, each unordered pair counted once.
--
--   These are the objects in which every result on the minimal cost of a Lightning Network is stated.
--
--   **Formalization Note.** The node set is an arbitrary finite type rather than $\{1,\dots,n\}$. The axiom (SA) is printed as "$c(x+y)<c(x)+c(y)$ for $x>y\ge0$", which at $y=0$ reads $c(x)<c(x)$ and is unsatisfiable; it is stated here for all $x,y>0$, the form Appendix D verifies ("for any $x,y>0$"). Nonnegativity of $c$ is the codomain $\mathbb R_+$ of the paper. The cost uses the paper's own $\tfrac12\sum_{i,j}$ form, which equals $\sum_{i>j}$ for an anti-symmetric matrix and needs no order on $V$. The sign convention is the one of the §2.1 display (row sums), under which a net payer has $f_i>0$; the paper's numerical example in §2 uses the opposite sign, and every statement of this mission is invariant under $\mathcal F\mapsto-\mathcal F$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), pp. 4–5 (PDF 5–6), §2.1 and §2.2, (MO), (SY), (CI), (SA)

import Mathlib

namespace LNTopology.StarBound

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

end LNTopology.StarBound


