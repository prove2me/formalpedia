-- Prove2me | Definitions.Def_Helfgott_ArcCounting
-- name    : Helfgott_ArcCounting
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-04T23:08:54.819089+00:00
-- url     : https://prove2.me/theorems/d8f281fd-86ea-4bd4-9242-bb2be9fd3b1b
-- title:
--   Actual exponential sums, parity-dependent major arcs and Goldbach scale
-- statement:
--   Data definitions for the actual infinite von Mangoldt exponential sums on R/Z, the parity-dependent major arcs from equation (3.5), the ternary Fourier integrand, the nonnegative minor-arc mass, and x=N/(2+9/(196√(2π))). The arcs are open circular balls around reduced fractions a/q: odd q≤r have radius δr/(2qx), even q≤2r have radius δr/(qx), with q>0 and 0≤a<q. The circle has circumference 1 and uses its quotient metric, so arcs crossing 0 are included. These definitions assert no analytic bounds or integrability.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (3.1), (3.5), (7.14), (7.48) and (7.49). https://arxiv.org/html/1312.7748v2 . Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_WeightedCounting
import Definitions.Def_Helfgott_PrimePowerRemoval
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open MeasureTheory
open scoped BigOperators

namespace Helfgott

noncomputable def coordinatedExpSum (η : ℝ → ℝ) (x : ℝ)
    (α : AddCircle (1 : ℝ)) : ℂ :=
  expSum (fun n => ((ArithmeticFunction.vonMangoldt n*η ((n : ℝ)/x) : ℝ) : ℂ)) α

noncomputable def majorArcs (δ : ℝ) (r : ℕ) (x : ℝ) : Set (AddCircle (1 : ℝ)) :=
  {α | ∃ q a : ℕ, 0 < q ∧ a < q ∧ Nat.Coprime a q ∧
    ((Odd q ∧ q ≤ r ∧
      dist α ((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ)) < δ*r/(2*q*x)) ∨
     (Even q ∧ q ≤ 2*r ∧
      dist α ((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ)) < δ*r/(q*x)))}

noncomputable def ternaryIntegrand (x : ℝ) (N : ℕ)
    (α : AddCircle (1 : ℝ)) : ℂ :=
  coordinatedExpSum etaPlus x α * coordinatedExpSum etaPlus x α *
    coordinatedExpSum etaStar x α * fourier (-(N : ℤ)) α

noncomputable def minorArcMass (x : ℝ) : ℝ :=
  ∫ α in (majorArcs 8 150000 x)ᶜ,
    ‖coordinatedExpSum etaPlus x α‖^2 * ‖coordinatedExpSum etaStar x α‖
      ∂AddCircle.haarAddCircle

noncomputable def goldbachScale (N : ℕ) : ℝ :=
  (N : ℝ)/(2+9/(196*Real.sqrt (2*Real.pi)))

end Helfgott


