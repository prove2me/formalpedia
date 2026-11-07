-- Prove2me | Definitions.Def_GrothendieckLB_MixedScheme
-- name    : GrothendieckLB_MixedScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:44.950195+00:00
-- url     : https://prove2.me/theorems/614b8dca-92f7-4eaf-9ab4-a7957e148f63
-- title:
--   Mixed rounding scheme (Definition 10.1)
-- statement:
--   A $d$-dimensional **mixed rounding scheme** is a probability distribution on pairs of measurable sign functions $f,g:\mathbb R^d\to\{\pm1\}$. One pair is sampled and then used for every vector in the rounding procedure.
--
--   **Formalization Note** The distribution is a random pair: a probability space $(\Omega,\mu)$ with families $F,G:\Omega\to(\mathbb R^d\to\mathbb R)$, jointly measurable in $(\omega,x)$ and sign-valued for each $\omega$. This avoids choosing a $\sigma$-algebra on a function space and makes the average below well defined. A finite mixture is the case of a finite $\Omega$. Oddness is not required, as on the page.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 10.1, p.42

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
open MeasureTheory

namespace GrothendieckLB

/-- A `d`-dimensional mixed rounding scheme: a probability distribution on pairs of measurable sign
functions `f, g : ℝ^d → {±1}` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 10.1, p.42).

**Formalization Note** The distribution is a random pair over a probability space `(Ω, μ)`, jointly
measurable in `(ω, x)`. This avoids a σ-algebra on a space of functions and makes
`ω ↦ H_{F ω, G ω}(t)` measurable. Finite mixtures are the case of a finite `Ω`. Oddness is not
required, as on the page. -/
structure MixedScheme (d : ℕ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [prob : IsProbabilityMeasure μ]
  F : Ω → (Fin d → ℝ) → ℝ
  G : Ω → (Fin d → ℝ) → ℝ
  measurable_F : Measurable (Function.uncurry F)
  measurable_G : Measurable (Function.uncurry G)
  sign_F : ∀ ω, IsSignFn (F ω)
  sign_G : ∀ ω, IsSignFn (G ω)

end GrothendieckLB


