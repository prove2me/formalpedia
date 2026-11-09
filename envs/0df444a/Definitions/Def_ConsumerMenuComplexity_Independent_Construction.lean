-- Prove2me | Definitions.Def_ConsumerMenuComplexity_Independent_Construction
-- name    : ConsumerMenuComplexity_Independent_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:02:21.197392+00:00
-- url     : https://prove2.me/theorems/d7027ef1-4aa9-4280-bbe3-2113495ded00
-- title:
--   Equations (13), (14), (19) — full continuous witness, normalized density and caps
-- statement:
--   Set $c=1/8$. Define the target utility on nonnegative arguments by
--   $$r(v)=\begin{cases}v/4+v^2/8,&0\le v\le2,\\v-1,&v>2.\end{cases}$$
--   The item-1 menu contains the null option, $(1,0,1)$ and every tangent lottery $((1+t)/4,0,t^2/8)$ with real $0\le t\le2$. The full target menu $M^*$ also contains $(0,1,0)$. Its complete choice rule gives item 2 when $v_2>r(v_1)$; otherwise it takes the tangent with $t=v_1$ for $v_1\le2$ and $(1,0,1)$ for $v_1>2$. Item 1 is chosen at equality. In particular $t=0$ gives the non-null option $(1/4,0,0)$, and $v_1=2$ uses the tangent. The single-item implementation uses the same item-1 choice independently of $v_2$.
--
--   The unnormalized density is zero on the nonpositive half-line, and for $v>0$ equals
--   $$g(v)=e^{-v}\begin{cases}\sqrt{(v+2)/v},&v\le2,\\\sqrt2,&v>2.\end{cases}$$
--   Define $C=(\int_{\mathbb R}g(v)\,dv)^{-1}$ and $f_1=Cg$. The first law $D_1$ is Lebesgue measure with density $f_1$, mapped to nonnegative reals. The second law $D_2$ is Lebesgue measure restricted to $(0,1)$ and mapped to nonnegative reals. The prior is their product, and the caps are the actual expected allocations of the chosen target mechanism:
--   $$\alpha_i=\mathbb E_{D_1\times D_2}[x_i^{M^*}].$$
--   These formulas specify the construction without assuming normalization, probability mass, finite moments, menu implementability, valid caps or optimality. The source validations remain theorem conclusions. The raw density guard avoids evaluating its singular ratio at zero; values at zero carry no mass.
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, §5.3, equations (13)–(14), PDF pp.20–21 (printed pp.19–20); Appendix B.1, equation (19), PDF p.34 (printed p.33); caps PDF p.22 (printed p.21)

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Mechanisms
open MeasureTheory
open scoped ENNReal NNReal

namespace ConsumerMenuComplexity.Independent

/-- Equation (13), used only at nonnegative arguments. Both branches agree at 2. -/
noncomputable def targetUtility (v : ℝ) : ℝ := if v ≤ 2 then v / 4 + v ^ 2 / 8 else v - 1

noncomputable def tangentOption (t : ℝ) : Option := option ((1 + t) / 4) 0 (t ^ 2 / 8)

def targetItemOneMenu : Set Option :=
  {o | (∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 ∧ o = tangentOption t) ∨
    o = option 1 0 1 ∨ o = nullOption}

/-- Equation (14), with its implicit outside/null option included. -/
def targetMenu : Set Option := targetItemOneMenu ∪ {option 0 1 0}

/-- Complete tie rule: item 1 at equality, tangent t=v₁ through v₁=2. -/
noncomputable def targetChoice (v : TypeSpace) : Option :=
  if targetUtility (v 0) < (v 1 : ℝ) then option 0 1 0
  else if (v 0 : ℝ) ≤ 2 then tangentOption (v 0) else option 1 0 1

noncomputable def targetMechanism : Mechanism where
  q v := (targetChoice v).1
  s v := (targetChoice v).2

/-- The single-item implementation, independent of the second coordinate. -/
noncomputable def targetItemOneMechanism : Mechanism where
  q v := if (v 0 : ℝ) ≤ 2 then (tangentOption (v 0)).1 else (option 1 0 1).1
  s v := if (v 0 : ℝ) ≤ 2 then (tangentOption (v 0)).2 else 1

/-- Unnormalized density (19); the singular ratio is never evaluated at v=0. -/
noncomputable def rawDensity (v : ℝ) : ℝ :=
  if 0 < v then Real.exp (-v) *
    (if v ≤ 2 then Real.sqrt ((v + 2) / v) else Real.sqrt 2) else 0

noncomputable def normalizer : ℝ := (∫ v : ℝ, rawDensity v)⁻¹

noncomputable def firstDensity (v : ℝ) : ℝ := normalizer * rawDensity v

noncomputable def densityLaw (f : ℝ → ℝ) : Measure ℝ≥0 :=
  (volume.withDensity (fun v => ENNReal.ofReal (f v))).map Real.toNNReal

noncomputable def firstLaw : Measure ℝ≥0 := densityLaw firstDensity

noncomputable def uniformLaw : Measure ℝ≥0 :=
  (volume.restrict (Set.Ioo (0 : ℝ) 1)).map Real.toNNReal

noncomputable def constructedPrior : Measure TypeSpace := productLaw firstLaw uniformLaw

noncomputable def targetCaps : Fin 2 → ℝ := supply constructedPrior targetMechanism

noncomputable def chosenCosts : Fin 2 → ℝ := ![1, 1 / 8]

end ConsumerMenuComplexity.Independent


