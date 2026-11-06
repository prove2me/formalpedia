-- Prove2me | Definitions.Def_CompetingSellers_IsLargeAliceEq
-- name    : CompetingSellers_IsLargeAliceEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:11.380814+00:00
-- url     : https://prove2.me/theorems/7cc695d2-bb7e-4cf5-9cd0-81118c5c8be0
-- title:
--   Large-Alice-equalizer mechanisms $A^{LA}_R$ ($a\ge b$)
-- statement:
--   Let $a\ge b$, $\Delta=|a-b|$ and $R\in[0,b]$, and let $s=s(R)\in[R+\Delta,a]$ satisfy
--   $$\frac{b+R}{s-\Delta}-\ln\frac{b}{s-\Delta}=2\qquad(3).$$
--   $A^{LA}_R$ is the mechanism with upper allocation rule
--   $$z^+(v)=\begin{cases}0,&0\le v<R+\Delta,\\ 1-\frac{R}{s-\Delta},& R+\Delta\le v<s,\\ 1-\frac{R}{v-\Delta},& s\le v\le a,\end{cases}$$
--   constant after $a$. These mechanisms make Bob indifferent across a range of responses and attain Alice's optimum for $a\ge b$.
--
--   **Formalization Note** A predicate on Alice's mechanisms: $R\in[0,b]$, $s$ solves (3), and $z^+_A$ equals this rule on $[0,\infty)$. By Lemma 2.3 all such mechanisms share one proper pricing representation.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Definition 3.12 and eq. (3), p.25 (PDF 28)

import Mathlib
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- `s = s(R)`, eq. (3), p.25 (= eq. (15), p.63): `s ∈ [R + Δ, a]` satisfies
`(b + R)/(s − Δ) − ln(b/(s − Δ)) = 2`, with `Δ = |a − b|`. -/
def IsSRoot (a b R s : ℝ) : Prop :=
  s ∈ Set.Icc (R + |a - b|) a ∧
    (b + R) / (s - |a - b|) - Real.log (b / (s - |a - b|)) = 2

/-- The allocation rule of Definition 3.12: `0` on `[0, R + Δ)`, `1 − R/(s − Δ)` on
`[R + Δ, s)`, `1 − R/(v − Δ)` on `[s, a]`, and its value at `a` after `a`. -/
noncomputable def zLA (a b R s v : ℝ) : ℝ :=
  if v < R + |a - b| then 0
  else if v < s then 1 - R / (s - |a - b|)
  else if v ≤ a then 1 - R / (v - |a - b|)
  else 1 - R / (a - |a - b|)

variable {S : Type} [MeasurableSpace S] {null : S}

/-- **Large-Alice-equalizer mechanism `A^{LA}_R`** (Definition 3.12, p.25).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Definition 3.12, p.25 (PDF 28): "Let `a ≥ b`. Given a parameter
`R ∈ [0, b]`, let `s ∈ [R + ∆, a]` be as in Equation (3). We define the mechanism `A^{LA}_R` to be
the mechanism with the following allocation rule: `z⁺(v) = 0` if `0 ≤ v < R + ∆`,
`1 − R/(s − ∆)` if `R + ∆ ≤ v < s`, `1 − R/(v − ∆)` if `s ≤ v ≤ a`. After `a`, the allocation
retains its value at `a`."

`IsLargeAliceEq a b R s A`: `R ∈ [0, b]`, `s` solves eq. (3), and Alice's mechanism `A` has upper
induced allocation rule `z⁺_A` equal to this rule on `[0, ∞)`.

**Formalization Note.** The equalizer is defined by its allocation rule, so it is a predicate on
mechanisms: by Lemma 2.3 all such mechanisms have the same proper pricing representation (they
are the paper's `A^{LA}_R` up to essential equivalence). `a ≥ b` is a hypothesis of the theorems
using it. -/
def IsLargeAliceEq (a b R s : ℝ) (A : Mech S null) : Prop :=
  R ∈ Set.Icc 0 b ∧ IsSRoot a b R s ∧ ∀ v, 0 ≤ v → mZPlus a A v = zLA a b R s v

end CompetingSellers


