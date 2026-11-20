-- Prove2me | Definitions.Def_KolmogorovExtension4_KolmogorovExtension_F001
-- name    : KolmogorovExtension4_KolmogorovExtension_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:35:53.547834+00:00
-- url     : https://prove2.me/theorems/c5166ff0-4a83-4e89-9243-4341dd082c46
-- title:
--   Source declarations: KolmogorovExtension4.KolmogorovExtension
-- statement:
--   Source-preserving extracted declarations from KolmogorovExtension4.KolmogorovExtension. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_KolmogorovExtension4_KolmogorovExtension_F000
import Definitions.Def_SourceProof_f3bc758975e5f4bff03d6c2a

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open Set

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

section InnerRegular

variable [∀ i, TopologicalSpace (α i)] [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, SecondCountableTopology (α i)] [∀ I, IsFiniteMeasure (P I)]

local notation "Js" => measurableCylinders.finset

local notation "As" => measurableCylinders.set

end InnerRegular

section Polish

variable [∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)]
  [∀ i, PolishSpace (α i)] [∀ I, IsFiniteMeasure (P I)]

instance isFiniteMeasure_projectiveLimit (hP : IsProjectiveMeasureFamily P) :
    IsFiniteMeasure (projectiveLimit P hP) :=
  IsProjectiveLimit.isFiniteMeasure (_root_.Prove2MeSourceProof.h_f3bc758975e5f4bff03d6c2a hP)
instance isProbabilityMeasure_projectiveLimit [hι : Nonempty ι]
    {P : ∀ J : Finset ι, Measure (Π j : J, α j)} [∀ i, IsProbabilityMeasure (P i)]
    (hP : IsProjectiveMeasureFamily P) : IsProbabilityMeasure (projectiveLimit P hP) := by
  constructor
  rw [← cylinder_univ ({hι.some} : Finset ι),
    (_root_.Prove2MeSourceProof.h_f3bc758975e5f4bff03d6c2a hP).measure_cylinder _ MeasurableSet.univ]
  exact measure_univ
end Polish

end MeasureTheory


