-- Prove2me | Definitions.Def_LearnCollude_Model
-- name    : LearnCollude_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:37.916711+00:00
-- url     : https://prove2.me/theorems/2a604efe-f136-496f-8fc7-a7e8b97dd831
-- title:
--   The pricing duopoly: prices, box, demand, revenues, derivatives
-- statement:
--   Two firms $i\in\{1,2\}$ set prices $p=(p_1,p_2)\in\mathbb R^2$, with the Euclidean norm. The **feasible box** is $B=[0,p_1^{\max}]\times[0,p_2^{\max}]$, for caps $p_i^{\max}>0$. The **demand model** consists of demand functions $d_i$ that are continuously differentiable and nonnegative on $B$.
--
--   The expected revenues are
--   $$
--   r_i(p)=p_i\,d_i(p),\qquad r(p)=r_1(p)+r_2(p).
--   $$
--   Partial derivatives $\partial_{p_j}f$ and the gradient $\nabla f$ are taken within $B$. The module also fixes the notation $i'$ for the other firm and the profile in which firm $i$ charges a given price and the other firm a given price.
--
--   Every other object of the mission is built on these.
--
--   **Formalization Note** Firms are `0, 1 : Fin 2`. Each $d_i$ is a total measurable function, constrained on $B$ only, because the first perturbed prices of the policy may leave $B$. The box is convex with nonempty interior, so derivatives within it are unique also on its faces.
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), §2, pp. 8–9, eqs. (1), (3)

import Mathlib

open Set

namespace LearnCollude

/-- **Price vectors** `p = (p₁, p₂)`, with the Euclidean norm used throughout
Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06).

**Formalization Note** The firms `i = 1, 2` of the paper are `0, 1 : Fin 2`, and `p i` is firm `i`'s
price. -/
abbrev Prices := EuclideanSpace ℝ (Fin 2)

/-- The other firm `i'`. -/
def other (i : Fin 2) : Fin 2 := 1 - i

/-- The price vector in which firm `i` charges `own` and the other firm charges `rival`. -/
noncomputable def profile (i : Fin 2) (own rival : ℝ) : Prices :=
  WithLp.toLp 2 fun j => if j = i then own else rival

/-- The feasible box `[0, pmax₁] × [0, pmax₂]`, Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06),
§2, p. 8. -/
def box (pmax : Fin 2 → ℝ) : Set Prices := {p | ∀ i, p i ∈ Icc 0 (pmax i)}

/-- **The demand model**, Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06), §2, p. 8: price caps
`pmax i > 0` and demand functions `dᵢ` that are continuously differentiable and nonnegative on the
box.

**Formalization Note** The paper's `dᵢ` is defined on the box only, but `p̂ᵢ(1) ∈ (0, pmaxᵢ)` and
`θ_c,i < pmaxᵢ / 2` allow the first perturbed prices to leave the box. So `d` is total and measurable,
and it is constrained on the box only; its values elsewhere are arbitrary. Differentiability on the
closed box is `ContDiffOn`, one-sided on the faces. -/
structure Model where
  /-- The price caps. -/
  pmax : Fin 2 → ℝ
  pmax_pos : ∀ i, 0 < pmax i
  /-- The demand functions. -/
  d : Fin 2 → Prices → ℝ
  measurable_d : ∀ i, Measurable (d i)
  contDiffOn_d : ∀ i, ContDiffOn ℝ 1 (d i) (box pmax)
  nonneg_d : ∀ i, ∀ p ∈ box pmax, 0 ≤ d i p

namespace Model

variable (M : Model)

/-- The expected revenue `rᵢ(p) = pᵢ dᵢ(p)` of firm `i`, Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), eq. (3), p. 9. -/
noncomputable def r (i : Fin 2) (p : Prices) : ℝ := p i * M.d i p

/-- The expected joint revenue `r(p) = r₁(p) + r₂(p)`, Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), eq. (1), p. 9. -/
noncomputable def jointRevenue (p : Prices) : ℝ := ∑ i, M.r i p

/-- The partial derivative `∂_{p_j} f(p)`, taken within the box.

**Formalization Note** The box is convex with nonempty interior, so the derivative within it is
unique also on its faces. -/
noncomputable def pderiv (f : Prices → ℝ) (j : Fin 2) (p : Prices) : ℝ :=
  fderivWithin ℝ f (box M.pmax) p (EuclideanSpace.single j 1)

/-- The gradient `∇f(p) = (∂_{p₁} f(p), ∂_{p₂} f(p))`, taken within the box. -/
noncomputable def grad (f : Prices → ℝ) (p : Prices) : Prices :=
  WithLp.toLp 2 fun j => M.pderiv f j p

/-- A firm's derivative of its own revenue, `∂_{p_i} rᵢ(p)`. -/
noncomputable def ownPartial (i : Fin 2) (p : Prices) : ℝ := M.pderiv (M.r i) i p

end Model

end LearnCollude


