-- Prove2me | Definitions.Def_SupplyDemand_Model
-- name    : SupplyDemand_Model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:28:06.915566+00:00
-- url     : https://prove2.me/theorems/3f9907ab-82c1-45ad-ab7b-92f99a629172
-- title:
--   Supply-and-demand model: equilibrium, market curves, elasticity, example curves
-- statement:
--   This file fixes the vocabulary of the partial-equilibrium supply-and-demand model. Prices and quantities are real numbers, and supply and demand curves are functions $S, D:\mathbb R\to\mathbb R$ giving quantity as a function of price.
--
--   1. **Market equilibrium.** $(p,q)$ is an equilibrium of $(S,D)$ when the quantity demanded and the quantity supplied at price $p$ are both $q$:
--   $$\mathrm{IsEquilibrium}(S,D,p,q)\iff D(p)=q\ \text{and}\ S(p)=q.$$
--   2. **Market curve.** For a finite set $s$ of agents with individual curves $f_i$, the market curve is the horizontal sum $p\mapsto\sum_{i\in s}f_i(p)$.
--   3. **Point elasticity.** For a curve $Q$ and a price $P$, $\varepsilon_Q(P)=Q'(P)\,P/Q(P)$.
--   4. **Example curves from the source:** linear supply $Q(P)=3P-6$, linear demand $Q(P)=32-2P$, constant-elasticity supply $Q(P)=5P^{0.5}$, constant-elasticity demand $Q(P)=3P^{-2}$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** The derivative is Mathlib's `deriv` (equal to $0$ where $Q$ is not differentiable), and division by $Q(P)=0$ returns $0$. Real powers are `Real.rpow`, which is only meaningful here for $P>0$; all statements about the isoelastic curves assume $P>0$.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, sections "Supply schedule", "Demand schedule", "Equilibrium", "Market equilibrium"

import Mathlib

namespace SupplyDemand

/-- `(p, q)` is a market equilibrium (market-clearing price–quantity pair) for the supply
curve `S` and the demand curve `D`: at the price `p`, the quantity demanded and the quantity
supplied both equal `q`. -/
def IsEquilibrium (S D : ℝ → ℝ) (p q : ℝ) : Prop :=
  D p = q ∧ S p = q

/-- Market (aggregate) curve of a finite family of individual curves `f i`, `i ∈ s`:
at each price the individual quantities are added ("added horizontally"). -/
def marketCurve {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) : ℝ → ℝ :=
  fun p => ∑ i ∈ s, f i p

/-- Point price elasticity of a curve `Q` at the price `P`: `Q'(P) · P / Q(P)`. -/
noncomputable def pointElasticity (Q : ℝ → ℝ) (P : ℝ) : ℝ :=
  deriv Q P * P / Q P

/-- The source's example linear supply function `Q(P) = 3P - 6`. -/
def linearSupply (P : ℝ) : ℝ := 3 * P - 6

/-- The source's example linear demand function `Q(P) = 32 - 2P`. -/
def linearDemand (P : ℝ) : ℝ := 32 - 2 * P

/-- The source's example constant-elasticity supply function `Q(P) = 5 P^{0.5}`. -/
noncomputable def isoelasticSupply (P : ℝ) : ℝ := 5 * P ^ (0.5 : ℝ)

/-- The source's example constant-elasticity demand function `Q(P) = 3 P^{-2}`. -/
noncomputable def isoelasticDemand (P : ℝ) : ℝ := 3 * P ^ (-2 : ℝ)

end SupplyDemand


