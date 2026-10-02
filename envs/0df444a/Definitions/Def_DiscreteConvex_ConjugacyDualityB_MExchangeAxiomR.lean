-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_MExchangeAxiomR
-- name    : DiscreteConvex_ConjugacyDualityB_MExchangeAxiomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:31:13.072536+00:00
-- url     : https://prove2.me/theorems/a3eeeb5a-2f52-4035-8e1e-03b66e2ffbd5
-- title:
--   MExchangeAxiomR
-- statement:
--   Axiom (M-EXC[R]): the real-variable M-convexity exchange axiom.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, axiom (M-EXC[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.161, axiom (M-EXC[R])

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomR

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-EXC[R]): the real-variable M-convexity exchange axiom. -/
def MExchangeAxiomR (f : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomR f, ∀ y ∈ DomR f, ∀ u ∈ ({v | y v < x v} : Set V), ∃ v ∈ ({w | x w < y w} : Set V),
    ∃ alpha0 : ℝ, 0 < alpha0 ∧
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha0 →
        f x + f y ≥ f (fun w => x w - alpha * (IndicatorVec {u} w - IndicatorVec {v} w : ℝ)) +
          f (fun w => y w + alpha * (IndicatorVec {u} w - IndicatorVec {v} w : ℝ))

end DiscreteConvex.ConjugacyDualityB


