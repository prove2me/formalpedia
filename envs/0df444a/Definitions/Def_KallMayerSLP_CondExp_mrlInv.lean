-- Prove2me | Definitions.Def_KallMayerSLP_CondExp_mrlInv
-- name    : KallMayerSLP_CondExp_mrlInv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:30.699684+00:00
-- url     : https://prove2.me/theorems/5ac49bfa-760e-4542-a486-bc7efc5f61aa
-- title:
--   Generalized inverse of the mean residual life
-- statement:
--   For the mean residual life $l$ of a random variable $\xi$ and a bound $\gamma\in\mathbb R$,
--   $$
--   l^{-1}(\gamma)=\inf\{s\in\mathbb R\mid l(s)\le\gamma\}\in\mathbb R\cup\{\pm\infty\},
--   $$
--   with $\inf\emptyset=+\infty$. It is the right-hand side of the linear form of constraint (4.26).
--
--   **Formalization Note** The book prints $l^{-1}(z):=\inf\{z\mid l(z)\le\gamma\}$, using $z$ twice. The infimum is taken in `EReal`, so an empty level set gives $+\infty$ rather than the real default $0$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.2, p.159

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- The generalized inverse of the mean residual life `l`: `l⁻¹(γ) := inf {s | l(s) ≤ γ}`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.2, p.159 (PDF 169).

**Formalization Note** The book prints `l⁻¹(z) := inf{z | l(z) ≤ γ}`, reusing `z`; the reading is
`l⁻¹(γ) := inf {s | l(s) ≤ γ}`. The infimum is taken in `EReal`, so `inf ∅ = +∞` (no `s` satisfies
`l(s) ≤ γ`) rather than the real default `0`. -/
noncomputable def mrlInv {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ξ : Ω → ℝ) (γ : ℝ) :
    EReal :=
  sInf ((fun s : ℝ => (s : EReal)) '' {s | StochasticOrders.MeanResidualLife.mrl μ ξ s ≤ γ})

end KallMayerSLP.CondExp


