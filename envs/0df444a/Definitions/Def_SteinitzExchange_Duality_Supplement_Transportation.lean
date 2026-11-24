-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_Transportation
-- name    : SteinitzExchange_Duality_Supplement_Transportation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:27:25.168291+00:00
-- url     : https://prove2.me/theorems/f2b7ea18-214e-4fff-95d2-e37bd8f59d5e
-- title:
--   Transportation upper bound (2.8)
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be finite and let $x,y\in B$. The arc set is
--   $$\widetilde A=\{(u,v):x(u)>y(u),\ x(v)<y(v),\ x-\chi_u+\chi_v\in B\}.$$
--   A transportation plan assigns a nonnegative real number $\lambda(u,v)$ to each arc. Its row sums are $x(u)-y(u)$ and its column sums are $y(v)-x(v)$, at the surplus and deficit vertices respectively. Define
--   $$\widetilde\omega(x,y)=\sup_{\lambda\text{ feasible}}\sum_{(u,v)\in\widetilde A}[\omega(x-\chi_u+\chi_v)-\omega(x)]\lambda(u,v).$$
--   On the source domain (finite integral base sets), the family is nonempty and the value is a finite attained maximum, as stated just before Theorem 2.3. Shipments remain real, including nonintegral shipments.
--
--   **Formalization Note.** The supremum is in `EReal`: an empty feasible family gives $-\infty$ and an unbounded-above family gives $+\infty$. Only actual arcs carry variables. When $x=y$, there are no arcs, the unique empty shipment is feasible and the value is zero.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), pp. 280–281, Eq. (2.8) and its finiteness assertion

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet

namespace SteinitzExchange.Duality.Supplement

/-- The feasible exchange arcs of the transportation problem (2.8), p. 280. -/
noncomputable def transportArcs {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (x y : V → ℤ) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun a => y a.1 < x a.1 ∧ x a.2 < y a.2 ∧
    x - chi a.1 + chi a.2 ∈ B)

/-- Nonnegative real shipments on the actual arc subtype, with the row and column
marginals of (2.8). No integrality restriction is imposed on shipments. -/
def IsTransport {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (x y : V → ℤ)
    (shipment : transportArcs B x y → ℝ) : Prop :=
  (∀ a, 0 ≤ shipment a) ∧
  (∀ u : V, y u < x u →
    (∑ a : transportArcs B x y, if a.1.1 = u then shipment a else 0) = (x u - y u : ℤ)) ∧
  (∀ v : V, x v < y v →
    (∑ a : transportArcs B x y, if a.1.2 = v then shipment a else 0) = (y v - x v : ℤ))

/-- Objective in (2.8); values of ω outside B are never read. -/
noncomputable def transportValue {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (x y : V → ℤ)
    (shipment : transportArcs B x y → ℝ) : ℝ :=
  ∑ a : transportArcs B x y, (ω (x - chi a.1.1 + chi a.1.2) - ω x) * shipment a

/-- Transportation maximum, represented in EReal: empty family is −∞,
unbounded-above family is +∞. Theorem 2.3 also states attainment and finiteness
on its source domain, so no real-supremum default can make the bound vacuous. -/
noncomputable def transportBound {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (x y : V → ℤ) : EReal :=
  ⨆ shipment : {shipment : transportArcs B x y → ℝ // IsTransport B x y shipment},
    (transportValue B ω x y shipment.1 : EReal)

end SteinitzExchange.Duality.Supplement


