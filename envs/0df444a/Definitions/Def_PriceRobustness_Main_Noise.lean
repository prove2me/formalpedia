-- Prove2me | Definitions.Def_PriceRobustness_Main_Noise
-- name    : PriceRobustness_Main_Noise
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:38:04.250886+00:00
-- url     : https://prove2.me/theorems/13dc6096-6835-4387-ac3a-72ea6e2bb0ca
-- title:
--   Independent bounded symmetric row noise
-- statement:
--   On an arbitrary measurable sample space with a measure $P$, a row family $(\eta_j)_{j\in J}$ consists of measurable real random variables, each taking values in $[-1,1]$ at every outcome and having the same law as its negative. The whole family indexed by $J$ is mutually independent under $P$. No identical-distribution, density, variance, or between-row independence assumption is made; atoms at zero and constant zero variables are allowed. Probability normalization is required by the theorems, rather than bundled in this predicate. Mathlib supplies equality in distribution and mutual independence.
-- source:
--   Bertsimas and Sim, The Price of Robustness, authors' preprint, August 2001; revised August, 2002; PDF SHA-256 63f0bffaff9128b706a084acc869e1020ce79adf86108ac23b5b0dd598f189cb; Model U, p. 4; Theorem 3, p. 10; standing independence clarified in §5, p. 17

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PriceRobustness.Main

def SymmetricNoise {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (J : Finset (Fin N)) (η : Fin N → Ω → ℝ) : Prop :=
  (∀ j ∈ J, Measurable (η j)) ∧
  (∀ j ∈ J, ∀ ω, η j ω ∈ Set.Icc (-1 : ℝ) 1) ∧
  (∀ j ∈ J, IdentDistrib (η j) (fun ω => -η j ω) P P) ∧
  iIndepFun (fun j : J => η j.val) P

end PriceRobustness.Main


