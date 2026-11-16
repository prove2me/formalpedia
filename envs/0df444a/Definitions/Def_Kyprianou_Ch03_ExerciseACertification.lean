-- Prove2me | Definitions.Def_Kyprianou_Ch03_ExerciseACertification
-- name    : Kyprianou_Ch03_ExerciseACertification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:05:40.584312+00:00
-- url     : https://prove2.me/theorems/068f822a-625c-4717-9fbe-75aa8ba25bde
-- title:
--   Full, independently quantified obligations for exerciseGroupACertification
-- statement:
--   Each certificate reproduces the complete original theorem binders and conclusions; conjunction entails every member. Source item identities are preserved.
-- source:
--   Kyprianou (2006), Chapter 3 and solutions pp. 312-316.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch03

noncomputable def cert_exercise_3_1 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hCompleted : IsCompletedNaturalFiltration P X F),
    F.IsRightContinuous

noncomputable def cert_exercise_3_2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (y : ℝ) (hy : 0 ≤ y)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ omega, tau omega ≠ ⊤ →
      tau omega = (finiteTime omega : WithTop NNReal)),
    ∀ A : Set Omega,
      (∀ s : NNReal, MeasurableSet[F s]
        (A ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      ∀ f : ℝ → ℝ, Measurable f →
        (∃ C : ℝ, 0 ≤ C ∧ ∀ z, |f z| ≤ C) →
        ∀ t : NNReal,
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            f (reflectedSup X y (finiteTime omega + t) omega) ∂P) =
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            (∫ eta,
              f (max (reflectedSup X y (finiteTime omega) omega)
                    (LevyExtrema.SBA.runSup (fun s => X s eta) t) -
                    X t eta) ∂P) ∂P) ∧
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            f (reflectedInf X y (finiteTime omega + t) omega) ∂P) =
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            (∫ eta,
              f (max (reflectedInf X y (finiteTime omega) omega)
                    (LevyExtrema.SBA.runSup (fun s => -(X s eta)) t) +
                    X t eta) ∂P) ∂P)

noncomputable def cert_exercise_3_3a : Prop :=
  ∀ (g : ℝ → ℝ)
    (hg : IsSubmultiplicative g)
    (hgBounded : ∀ R : ℝ, 0 ≤ R →
       ∃ M : ℝ, ∀ x, |x| ≤ R → g x ≤ M),
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
       ∀ x : ℝ, g x ≤ a * Real.exp (b * |x|)

noncomputable def cert_exercise_3_3b : Prop :=
  IsSubmultiplicative (fun x : ℝ => max x 1) ∧
    (∀ alpha : ℝ, 0 < alpha →
       IsSubmultiplicative (fun x : ℝ => (max x 1) ^ alpha)) ∧
    IsSubmultiplicative (fun x : ℝ => max |x| 1) ∧
    (∀ alpha : ℝ, 0 < alpha →
       IsSubmultiplicative (fun x : ℝ => (max |x| 1) ^ alpha)) ∧
    (∀ beta : ℝ, 0 < beta → beta ≤ 1 →
       IsSubmultiplicative (fun x : ℝ => Real.exp (|x| ^ beta))) ∧
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (max |x| (Real.exp 1))) ∧
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (Real.log (max |x| (Real.exp (Real.exp 1)))))

noncomputable def cert_exercise_3_3c : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha cPlus cMinus eta : ℝ)
    (hAlpha : 0 < alpha ∧ alpha < 2)
    (hCPlus : 0 ≤ cPlus) (hCMinus : 0 ≤ cMinus)
    (hNonzero : 0 < cPlus + cMinus)
    (hMeasure : T.levyMeasure =
      (volume : Measure ℝ).withDensity
        (fun x : ℝ => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0)))
    (hEta : 0 < eta),
    (∀ t : NNReal, 0 < t →
       Integrable (fun omega => |X t omega| ^ eta) P) ↔ eta < alpha

noncomputable def exerciseGroupACertification : Prop :=
  cert_exercise_3_1 ∧
  cert_exercise_3_2 ∧
  cert_exercise_3_3a ∧
  cert_exercise_3_3b ∧
  cert_exercise_3_3c

end Kyprianou.Ch03


