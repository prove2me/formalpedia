-- Prove2me | Definitions.Def_CompetingSellers_Supplement_Prop49Condition
-- name    : CompetingSellers_Supplement_Prop49Condition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:32:28.117294+00:00
-- url     : https://prove2.me/theorems/5aebaa30-6dbf-4104-ae0c-faaae67656dd
-- title:
--   Proposition 4.9's condition: the optimal aligned equalizers $A^{ALB}_{R^*}$, $A^{ALA}_{R^*}$ and their allocation rules
-- statement:
--   Let $a,b>0$ and $\Delta=|a-b|$. The **aligned equalizers** have explicit allocation rules (Definitions 4.5, 4.7), which at the optimal parameters of Proposition 4.9 read as follows.
--
--   1. If $a<b$, $R^*_{ALB}=\Delta+a/e$ and
--   $$z^+_{A^*_{ALB}}(v)=\begin{cases}0,&0\le v<R^*_{ALB}-\Delta,\\ \dfrac ab\Big(1-\dfrac{R^*_{ALB}-\Delta}{v}\Big),&R^*_{ALB}-\Delta\le v\le a.\end{cases}$$
--   2. If $a\ge b$, $R^*_{ALA}=b\,e^{-a/b}$ and
--   $$z^+_{A^*_{ALA}}(v)=\begin{cases}0,&0\le v<R^*_{ALA}+\Delta,\\ 1-\dfrac{R^*_{ALA}}{v-\Delta},&R^*_{ALA}+\Delta\le v\le a.\end{cases}$$
--
--   The prescribed equilibrium allocation is $x_{eq}=\frac ab(1-\frac1e)$ if $a<b$ and $x_{eq}=1-e^{-a/b}$ if $a\ge b$.
--
--   An Alice mechanism $A$ satisfies **Proposition 4.9's condition** if its upper induced allocation rule agrees with the canonical one below $a$ and its lower one at $a$ is $x_{eq}$:
--   $$z^+_A(v)=z^+_{A^*}(v)\quad(0\le v<a),\qquad z^-_A(a)=x_{eq}.$$
--   No condition is imposed on $z^+_A(a)$. Here $z^{\pm}_A(v)$ are the largest and smallest maximizers of $v\,x-P_A(x)$, where $P_A$ is the proper pricing representation of $A$.
--
--   Proposition 4.9 states that this condition characterizes Alice's optimal mechanisms in the aligned model; Theorem 1.3 uses it as the explicit characterization.
--
--   **Formalization Note** The canonical rules are written as explicit formulas (`zAligned`) instead of constructing the canonical mechanisms; $z^{\pm}_A$ are the published `mZPlus a A`, `mZMinus a A`. The cases are split at $a<b$ versus $a\ge b$ exactly as in Proposition 4.9.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Proposition 4.9, p.38 (PDF 41); Definition 4.5, p.34 (PDF 37); Definition 4.7, p.36 (PDF 39)

import Mathlib
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers.Supplement

/-- **The allocation rule `z⁺` of the optimal aligned equalizer** (Definitions 4.5 and 4.7 at the
optimal parameters of Proposition 4.9).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Definition 4.5, p.34 (PDF 37): for `a ≥ b` and `R > 0`,
"`z⁺(v) = 0` for `0 ≤ v < R + ∆`, `1 − R/(v − ∆)` for `R + ∆ ≤ v ≤ a`"; Definition 4.7, p.36
(PDF 39): for `a < b` and `R > ∆`, "`z⁺(v) = 0` for `0 ≤ v < R − ∆`,
`(a/b)·(1 − (R − ∆)/v)` for `R − ∆ ≤ v ≤ a`"; Proposition 4.9, p.38 (PDF 41):
`R*_ALB = ∆ + a/e` (case `a < b`) and `R*_ALA = b·e^{−a/b}` (case `a ≥ b`), `∆ = |a − b|`.

**Formalization Note.** Only the values on `[0, a)` are used (Proposition 4.9 constrains `z⁺_A` on
`[0, a)`); the canonical mechanisms themselves need not be constructed. `R* > 0` in the first case
and `R* > ∆` in the second, so the `R > 0` / `R > ∆` branch of the definitions applies. -/
noncomputable def zAligned (a b v : ℝ) : ℝ :=
  if a < b then
    (if v < (|a - b| + a / Real.exp 1) - |a - b| then 0
      else a / b * (1 - ((|a - b| + a / Real.exp 1) - |a - b|) / v))
  else
    (if v < b * Real.exp (-(a / b)) + |a - b| then 0
      else 1 - b * Real.exp (-(a / b)) / (v - |a - b|))

/-- The prescribed value of `z⁻_A(a)` in Proposition 4.9 (p.38, PDF 41): `(a/b)·(1 − 1/e)` when
`a < b`, `1 − e^{−a/b}` when `a ≥ b` (the equilibrium allocation `x_eq = 1 − R*/b`). -/
noncomputable def xeqAligned (a b : ℝ) : ℝ :=
  if a < b then a / b * (1 - 1 / Real.exp 1) else 1 - Real.exp (-(a / b))

variable {S : Type} [MeasurableSpace S] {null : S}

/-- **The condition of Proposition 4.9** (aligned model, p.38).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Proposition 4.9, p.38 (PDF 41): "A mechanism `A` is optimal for
Alice if and only if the following condition holds:
1. When `a < b`, its allocation rule satisfies `z⁺_A(v) = z⁺_{A*_ALB}(v)` for all `v ∈ [0, a)`, and
`z⁻_A(a) = (a/b)·(1 − 1/e)`, where `R*_ALB = ∆ + a/e` and `A*_ALB = A^{ALB}_{R*_ALB}` as in
Definition 4.7.
2. When `a ≥ b`, its allocation rule satisfies `z⁺_A(v) = z⁺_{A*_ALA}(v)` for all `v ∈ [0, a)`, and
`z⁻_A(a) = 1 − e^{−a/b}`, where `R*_ALA = b·e^{−a/b}` and `A*_ALA = A^{ALA}_{R*_ALA}` as in
Definition 4.5.
In either case, the largest maximizer `z⁺_A(a)` may be any value in `[z⁻_A(a), 1]`."

**Formalization Note.** `z⁺_A`, `z⁻_A` are the induced allocation rules of Alice's mechanism
(`mZPlus a A`, `mZMinus a A`, computed from its proper pricing representation `P_A`). The canonical
allocation rule is written out explicitly (`zAligned`). No condition is placed on `z⁺_A(a)`; the
last sentence of the proposition is stated as a separate clause of Theorem 1.3. -/
def Prop49Condition (a b : ℝ) (A : Mech S null) : Prop :=
  (∀ v ∈ Set.Ico (0 : ℝ) a, mZPlus a A v = zAligned a b v) ∧ mZMinus a A a = xeqAligned a b

end CompetingSellers.Supplement


