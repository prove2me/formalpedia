-- Prove2me | Definitions.Def_ConnesGreen_prime_overlap_loss
-- name    : ConnesGreen_prime_overlap_loss
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-09T02:58:29.83985+00:00
-- url     : https://prove2.me/theorems/ce42fdca-d77e-4eb6-80b5-2d59d38a821c
-- title:
--   Prime loss budget retaining individual support overlaps
-- statement:
--   For a real support parameter $T$ and a complex function $g$, write $M(g)=\int_{\mathbb R}|g|^2$ and $E(g)=\int_{\mathbb R}|g\prime|^2+M(g)/4$, using the existing original physical test energy. Let $A_T$ be the original finite set of prime powers with $\log n<2T$. Define the scalar arithmetic loss budget $$L_T(g)=\sum_{n\in A_T}\frac{2\Lambda(n)}{\sqrt n}\min\!\left(M(g),\ 2E(g)\max(2T-\log n,0)\right).$$ This records the smaller mass or support-overlap energy bound separately for each actual prime power. It is an auxiliary upper-bound budget, not a new prime sum, physical carrier or zero family. The original Weil distribution, actual von Mangoldt weights, strict active cutoff and admissible tests are unchanged.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/PrimeOverlapMass.lean, exact original-model auxiliary definition ConnesGreen.primeOverlapLoss, compiling local source 495a9f34f25d1dbfbeb6ba8dce6d4735559ae878

import Definitions.Def_ConnesGreen_arithmetic_mass_budget
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen
namespace ConnesGreen
def primeOverlapLoss (T : ℝ) (g : ℝ → ℂ) : ℝ :=
  ∑ n ∈ activePrimePowerFinset T,
    2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      min (∫ s : ℝ, ‖g s‖ ^ 2)
        (2 * physicalTestEnergy g * max (2 * T - Real.log n) 0)
end ConnesGreen


