-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P24
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P24
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:10:55.797207+00:00
-- url     : https://prove2.me/theorems/d3989ee4-cfd0-4466-84f8-2f474dc1502d
-- title:
--   Definitions for The Uncertainty Relation for Smooth Entropies
-- statement:
--   The objects the formalized statements of *The Uncertainty Relation for Smooth Entropies* (arXiv:1009.2015) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `squaredOverlap`: PDF p.1, equation (2): the SQUARED largest-singular-value overlap of two finite POVMs. Nonempty outcome sets make this a genuine finite maximum.
--   - `incompatibilityBits`: PDF p.1, equation (2): q = log₂(1/c) = -log₂(c). For POVMs on a nonzero finite space, c is positive, so log at zero is unused.
-- source:
--   The Uncertainty Relation for Smooth Entropies, arXiv:1009.2015v3, https://arxiv.org/abs/1009.2015v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

/-!
Tomamichel--Renner, arXiv:1009.2015v3, PDF pp.1--4.
The two paper imports are pinned accepted library modules: their actual entropy
and measurement definitions are reused, without assuming their theorems.
All logarithms are in bits. The order form preserves the subnormalized zero
endpoint where the printed additive expression has opposite infinities.
The QKD sketches are inventoried as source ambiguities in HARD.md and GAPS.json.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P24

open QAlgorithms.Papers.Independent.Information100.P67
  (IsSubnormalized conditionalMinEntropy conditionalMaxEntropy
   smoothConditionalMinEntropy smoothConditionalMaxEntropyExtended)
open QAlgorithms.Papers.Independent.Dependency50.P35 (measured)

/-- PDF p.1, equation (2): the SQUARED largest-singular-value overlap of two
finite POVMs. Nonempty outcome sets make this a genuine finite maximum. -/
def squaredOverlap {A X Z : Type} [Fintype A] [DecidableEq A]
    [Fintype X] [Nonempty X] [Fintype Z] [Nonempty Z]
    (M : X → Matrix A A ℂ) (N : Z → Matrix A A ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun xz : X × Z => specNorm (cfc Real.sqrt (M xz.1) * cfc Real.sqrt (N xz.2)) ^ 2)

/-- PDF p.1, equation (2): q = log₂(1/c) = -log₂(c).
For POVMs on a nonzero finite space, c is positive, so log at zero is unused. -/
def incompatibilityBits {A X Z : Type} [Fintype A] [DecidableEq A]
    [Fintype X] [Nonempty X] [Fintype Z] [Nonempty Z]
    (M : X → Matrix A A ℂ) (N : Z → Matrix A A ℂ) : ℝ :=
  -Real.logb 2 (squaredOverlap M N)

example {A : Type} [Fintype A] [DecidableEq A] (M N : Matrix A A ℂ) :
    squaredOverlap (fun _ : Unit => M) (fun _ : Unit => N) =
      specNorm (cfc Real.sqrt M * cfc Real.sqrt N) ^ 2 := by
  simp [squaredOverlap]

example {A X Z : Type} [Fintype A] [DecidableEq A]
    [Fintype X] [Nonempty X] [Fintype Z] [Nonempty Z]
    (M : X → Matrix A A ℂ) (N : Z → Matrix A A ℂ)
    (h : squaredOverlap M N = 1) : incompatibilityBits M N = 0 := by
  simp [incompatibilityBits, h]

end QAlgorithms.Papers.Independent.Intakethird100.P24


