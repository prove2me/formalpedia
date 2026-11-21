-- Prove2me | Definitions.Def_SourceProof_200c032984224ec4322972ff
-- name    : SourceProof_200c032984224ec4322972ff
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:17:23.694058+00:00
-- url     : https://prove2.me/theorems/36efee4d-fe44-492d-86c1-5d7225f5c392
-- title:
--   LevyStochCalc source module: SourceProof_200c032984224ec4322972ff
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.ae_eq_zero_of_integral_char_joint` comes from the `LevyStochCalc.Driver.JointCharacters` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointCharacters_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Product characters of a Lévy driver separate

The coordinate values of the Brownian motion before `T` and the window counts of the Poisson
random measure before `T` form one family of real random variables, indexed by a sum type. Its
cylinder characters are the products of a Brownian cylinder character and a window character,
and the σ-algebra it generates is `σ(W_{≤T}) ⊔ windowSigma N T`, whose augmentation contains the
joint natural filtration at `T`. The generic separation theorem
`Probability.ae_eq_zero_of_integral_char_cylinder_eq_zero` therefore shows that an integrable
weight, measurable for the augmented joint filtration at `T` and orthogonal to every product
character, vanishes almost everywhere.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)


theorem _root_.Prove2MeSourceProof.h_200c032984224ec4322972ff (T : ℝ) {Z : Ω → ℂ} (hZ : Integrable Z P)
    (hZm : AEStronglyMeasurable[Probability.aug (D.filtration T) ‹MeasurableSpace Ω› P] Z P)
    (h : ∀ (F : Finset (Fin d × Set.Iic T)) (G : Finset (Poisson.WindowSet E ν T))
      (w : F → ℝ) (v : G → ℝ),
      ∫ ω, Complex.exp (((∑ p : F, (D.W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((∑ B : G, (D.N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal
            * v B : ℝ) : ℂ) * Complex.I) * Z ω ∂P = 0) :
    Z =ᵐ[P] 0 := by
  obtain ⟨Z₁, hZ₁m, hZZ₁⟩ := hZm
  have hZ₁m' :
      StronglyMeasurable[LevyStochCalc.Probability.aug (D.jointWindowSigma T) ‹MeasurableSpace Ω› P] Z₁ :=
    hZ₁m.mono (LevyStochCalc.Probability.aug_le_of_le_aug (D.filtration_le_aug_jointWindowSigma T))
  obtain ⟨Y, hYm, hZ₁Y⟩ := LevyStochCalc.Probability.aestronglyMeasurable_of_stronglyMeasurable_aug hZ₁m'
  have hZY : Z =ᵐ[P] Y := hZZ₁.trans hZ₁Y
  refine hZY.trans
    (D.ae_eq_zero_of_integral_char_jointWindowSigma T (hZ.congr hZY) hYm fun F G w v => ?_)
  rw [← h F G w v]
  refine integral_congr_ae ?_
  filter_upwards [hZY] with ω hω
  rw [hω]
end LevyDriver

end LevyStochCalc.Driver


