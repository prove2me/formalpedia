-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:08:14.885197+00:00
-- url     : https://prove2.me/theorems/e3608478-df14-4013-91d5-6186c9c3fce1
-- title:
--   Cj Defs
-- statement:
--   Definitions and structural lemmas for Cj Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/CjDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolSemiDirect
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
def HasStableRangeOne (A : Type) [CommRing A] : Prop :=
  ∀ a b x y : A, a * x + b * y = 1 → ∃ t, IsUnit (a + t * b)
def AdeleStableRankOne : Prop := ∀ (F : Type) [Field F] [NumberField F], HasStableRangeOne (AF F)
def ElimSR1 : Prop :=
  ∀ (A : Type) [CommRing A], HasStableRangeOne A → ∀ (k : ℕ) (X : GL (Fin k) A),
    X ∈ Subgroup.closure ({g : GL (Fin k) A | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = Matrix.diagonal d})
def TransvHaar : Prop :=
  ∀ (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A] (k : ℕ)
    (i j : Fin k), i ≠ j → ∀ (c : A) (μ : Measure (Fin k → A)), μ.IsAddHaarMeasure →
      μ.map (Matrix.mulVec (Matrix.transvection i j c)) = μ
def OrthInv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (G X : Matrix (Fin k) (Fin k) (AF F)),
    IsUnit G.det → X.transpose * G * X = G →
    ∀ μ : Measure (Fin k → AF F), μ.IsAddHaarMeasure → μ.map (Matrix.mulVec X) = μ
def VMod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (g : HA (AF F) σ J) (μ : Measure (Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure →
      μ.map (lin (AF F) σ J g) = μ
end PI.VolSemiDirect.W.Cj


