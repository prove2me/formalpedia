-- Prove2me | Definitions.Def_CompetingSellers_IsLargeBobEq
-- name    : CompetingSellers_IsLargeBobEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:22.370143+00:00
-- url     : https://prove2.me/theorems/13f124ed-4afa-4498-bc45-5b1bc66e9848
-- title:
--   Large-Bob-equalizer mechanisms $A^{LB}_R$ ($a<b$)
-- statement:
--   Let $a<b$, $\Delta=|a-b|$, $R\in(\Delta,b]$, $x=1-R/b\in[0,a/b)$, and let $u=u(x)$ be the root in $(0,ax/b)$ of
--   $$\ln\frac{a-(2b-a)u}{a-bx}=\int_u^x\frac{1+\alpha_u-\alpha_u y}{(1-y)(1-\alpha_u y)}\,dy,\qquad \alpha_u=\frac{b-a}{a-bu}\qquad(7)$$
--   if $x>0$, and $u=0$ if $x=0$. With $s_u=(a-bx)\frac{a-(b-a)u}{a-(2b-a)u}$, $A^{LB}_R$ is the mechanism whose upper allocation rule is
--   $$z^+(v)=\begin{cases}0,&0\le v<R-\Delta,\\ u,&R-\Delta\le v<s_u,\\ \dfrac{v-R+\Delta}{v+\alpha_u\,(v-\mathrm{util}(v))},&s_u\le v\le a,\end{cases}$$
--   constant after $a$, where $\mathrm{util}$ is the mechanism's own monopolist utility. These mechanisms attain Alice's optimum for $a<b$.
--
--   **Formalization Note** The third case is a differential equation for the utility ($\mathrm{util}'=z^+$), so the equalizer is a predicate on Alice's mechanisms, with $u$ an explicit parameter satisfying (7); Lemma B.6 provides the solution.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Definition 3.17 and eq. (7), p.28 (PDF 31)

import Mathlib
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- `α_u = (b − a)/(a − b u)` (eq. (7), p.28). -/
noncomputable def alphaU (a b u : ℝ) : ℝ := (b - a) / (a - b * u)

/-- `u = u(x)`, eq. (7), p.28 (= eq. (17), p.68): `u ∈ (0, ax/b)` and
`ln((a − (2b − a)u)/(a − bx)) = ∫_u^x (1 + α_u − α_u y)/((1 − y)(1 − α_u y)) dy`. -/
def IsURoot (a b x u : ℝ) : Prop :=
  u ∈ Set.Ioo 0 (a * x / b) ∧
    Real.log ((a - (2 * b - a) * u) / (a - b * x)) =
      ∫ y in u..x, (1 + alphaU a b u - alphaU a b u * y) / ((1 - y) * (1 - alphaU a b u * y))

/-- `s_u = (a − bx) · (a − (b − a)u)/(a − (2b − a)u)` (Definition 3.17, p.28; eq. (18), p.68). -/
noncomputable def sU (a b x u : ℝ) : ℝ := (a - b * x) * (a - (b - a) * u) / (a - (2 * b - a) * u)

variable {S : Type} [MeasurableSpace S] {null : S}

/-- **Large-Bob-equalizer mechanism `A^{LB}_R`** (Definition 3.17, p.28).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Definition 3.17, p.28 (PDF 31): "Let `a < b`. Given a parameter
`R ∈ (∆, b]`, let `x = 1 − R/b ∈ [0, a/b)` and `u = u(x)` be as in Equation (7) if `x > 0` and
`0` otherwise. Let `α_u` be as above and `s_u = (a − bx) · (a − (b − a)u)/(a − (2b − a)u)`. We
define the mechanism `A^{LB}_R` to be the mechanism with the following allocation rule:
`z⁺(v) = 0` if `0 ≤ v < R − ∆`, `u` if `R − ∆ ≤ v < s_u`,
`(v − R + ∆)/(v + α_u · (v − util_{A^{LB}_R}(v)))` if `s_u ≤ v ≤ a`. After `a`, the allocation
retains its value at `a`."

`IsLargeBobEq a b R u A`: `R ∈ (Δ, b]`, `u` is `u(x)` (or `0` when `x = 0`), and Alice's mechanism
`A` has this upper induced allocation rule on `[0, ∞)`, the third case being read with `A`'s own
utility `util_A`.

**Formalization Note.** The third case is a differential equation for `util_A`
(`util_A' = z⁺_A`); the equalizer is therefore a predicate on mechanisms, not a construction, and
Lemma B.6 supplies the solution. `Δ = |a − b|` (`= b − a` under the standing `a < b`, a
hypothesis of the theorems using it). -/
def IsLargeBobEq (a b R u : ℝ) (A : Mech S null) : Prop :=
  R ∈ Set.Ioc |a - b| b ∧
    ((1 - R / b = 0 ∧ u = 0) ∨ (0 < 1 - R / b ∧ IsURoot a b (1 - R / b) u)) ∧
    ∀ v, 0 ≤ v → mZPlus a A v =
      if v < R - |a - b| then 0
      else if v < sU a b (1 - R / b) u then u
      else if v ≤ a then (v - R + |a - b|) / (v + alphaU a b u * (v - mUtil a A v))
      else mZPlus a A a

end CompetingSellers


