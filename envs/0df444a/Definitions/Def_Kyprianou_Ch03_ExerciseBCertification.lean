-- Prove2me | Definitions.Def_Kyprianou_Ch03_ExerciseBCertification
-- name    : Kyprianou_Ch03_ExerciseBCertification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:06:12.482835+00:00
-- url     : https://prove2.me/theorems/180fc8c8-fd65-4f58-925a-8319e25d70dc
-- title:
--   Full, independently quantified obligations for exerciseGroupBCertification
-- statement:
--   Each certificate reproduces the complete original theorem binders and conclusions; conjunction entails every member. Source item identities are preserved. Additional fully quantified obligation: Exercise 3.4(ii)-(iv): gamma and stable Esscher classifications.
-- source:
--   Kyprianou (2006), Chapter 3 and solutions pp. 312-316.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch03

noncomputable def cert_exercise_3_4 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (cp ap gp cm am gm : ℝ)
    (hcp : 0 < cp) (hcm : 0 < cm)
    (hap : ap < 2) (ham : am < 2)
    (hgp : 0 < gp) (hgm : 0 < gm)
    (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStableSignedMeasure cp ap gp cm am gm),
    ∃ (OmegaP OmegaM : Type)
      (mP : MeasurableSpace OmegaP) (mM : MeasurableSpace OmegaM),
      letI : MeasurableSpace OmegaP := mP;
      letI : MeasurableSpace OmegaM := mM;
      ∃ (PP : Measure OmegaP) (PM : Measure OmegaM),
        ∃ (hPP : IsProbabilityMeasure PP) (hPM : IsProbabilityMeasure PM),
        letI : IsProbabilityMeasure PP := hPP;
        letI : IsProbabilityMeasure PM := hPM;
        ∃ (XP : NNReal → OmegaP → ℝ) (XM : NNReal → OmegaM → ℝ)
          (TP TM : ProbabilityTheory.LevyKhintchineTriple),
          ProbabilityTheory.IsLevyProcess XP PP ∧
          ProbabilityTheory.IsLevyProcess XM PM ∧
          TP.gaussianVariance = 0 ∧ TM.gaussianVariance = 0 ∧
          TP.levyMeasure = temperedStablePositiveMeasure cp ap gp ∧
          TM.levyMeasure = temperedStablePositiveMeasure cm am gm ∧
          (∀ (t : NNReal) (xi : ℝ),
            charFun (PP.map (XP t)) xi =
              Complex.exp (((t : ℝ) : ℂ) *
                Kyprianou.Ch01.levyTripleExponent TP xi)) ∧
          (∀ (t : NNReal) (xi : ℝ),
            charFun (PM.map (XM t)) xi =
              Complex.exp (((t : ℝ) : ℂ) *
                Kyprianou.Ch01.levyTripleExponent TM xi)) ∧
          (∀ t : NNReal,
            Measure.map
              (fun pair : OmegaP × OmegaM => XP t pair.1 - XM t pair.2)
              (PP.prod PM) =
            P.map (X t)) ∧
          (ap < 0 → temperedStablePositiveMeasure cp ap gp Set.univ < ⊤) ∧
          (am < 0 → temperedStablePositiveMeasure cm am gm Set.univ < ⊤) ∧
          (∀ alpha c gamma : ℝ, 0 < c → 0 < gamma →
            temperedStablePositiveMeasure c alpha gamma =
              (temperedStablePositiveMeasure c alpha 0).withDensity
                (fun x => ENNReal.ofReal (Real.exp (-gamma * x))))

noncomputable def cert_exercise_3_5 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F),
    L.ψ 0 = 0 ∧
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) L.ψ (Set.Ioi 0) ∧
    ConvexOn ℝ (Set.Ici 0) L.ψ ∧
    ((0 < L.σ ∨ L.ν ≠ 0) →
      StrictConvexOn ℝ (Set.Ioi 0) L.ψ) ∧
    ((¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega))) →
      Tendsto L.ψ atTop atTop)

noncomputable def cert_exercise_3_6 : Prop :=
  ∀ {Omega OmegaE : Type}
    [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : ℝ) (hq : 0 < q)
    (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {eta : OmegaE | t < e eta}).toReal =
        Real.exp (-q * (t : ℝ))),
    ∃ phi : ℝ, 0 < phi ∧ L.ψ phi = q ∧
      (∀ x y : ℝ, 0 < x → 0 < y →
        let tail (z : ℝ) :=
          ((P.prod Q) {pair : Omega × OmegaE |
             z < LevyExtrema.SBA.runSup
               (fun s => L.X s pair.1) (e pair.2)}).toReal;
        tail (x + y) = tail x * tail y) ∧
      (∀ x : ℝ, 0 ≤ x →
        ((P.prod Q) {pair : Omega × OmegaE |
          x < LevyExtrema.SBA.runSup
            (fun s => L.X s pair.1) (e pair.2)}).toReal =
        Real.exp (-phi * x)) ∧
      (∀ beta : ℝ, 0 ≤ beta →
        ∀ t : NNReal, Integrable
          (fun omega => Real.exp (beta * L.X t omega)) P) ∧
      (∃ phi0 : ℝ, 0 ≤ phi0 ∧ L.ψ phi0 = 0 ∧
        (∀ theta : ℝ, 0 ≤ theta →
          L.ψ theta = 0 → theta ≤ phi0) ∧
        ∀ x : ℝ, 0 ≤ x →
          (P {omega : Omega |
            ∃ t : NNReal, x < L.X t omega}).toReal =
          Real.exp (-phi0 * x))

noncomputable def cert_exercise_3_7 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha c : ℝ) (hAlpha : 0 < alpha ∧ alpha < 2)
    (hC : 0 < c) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStablePositiveMeasure c alpha 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun omega => scale ^ (1 / alpha) * X t omega)),
    (alpha < 1 →
      (∃ C : ℝ, 0 < C ∧
        (∀ theta : ℝ, 0 ≤ theta →
          Real.log (∫ omega,
            Real.exp (-theta * X 1 omega) ∂P) =
              -C * theta ^ alpha)) ∧
      (∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega))) ∧
    (1 < alpha →
      (∃ C : ℝ, 0 < C ∧
        ∀ theta : ℝ, 0 ≤ theta →
          Real.log (∫ omega,
            Real.exp (-theta * X 1 omega) ∂P) =
              C * theta ^ alpha) ∧
      (∀ n : ℕ, 2 ≤ n →
        ¬ Integrable (fun omega => |X 1 omega| ^ n) P) ∧
      (∀ᵐ omega ∂P, ∀ M : ℝ,
        ∃ n : ℕ, ∃ times : Fin (n + 1) → NNReal,
          times 0 = 0 ∧ times (Fin.last n) ≤ 1 ∧
          (∀ i : Fin n, times i.castSucc < times i.succ) ∧
          M < ∑ i : Fin n,
            |X (times i.succ) omega -
              X (times i.castSucc) omega|))

noncomputable def cert_exercise_3_4_regimes : Prop :=
  ∀ (c gamma : ℝ) (hc : 0 < c) (hgamma : 0 < gamma),
    (∀ q : ℝ, 0 ≤ q →
      (∫ x in Set.Ioi (0 : ℝ),
        (1 - Real.exp (-q * x)) ∂
          (temperedStablePositiveMeasure c 0 gamma)) =
        c * Real.log (1 + q / gamma)) ∧
    (temperedStablePositiveMeasure c 1 gamma).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
      temperedStablePositiveMeasure c 1 0 ∧
    (∀ alpha : ℝ, (0 < alpha ∧ alpha < 1) ∨
        (1 < alpha ∧ alpha < 2) →
      (temperedStablePositiveMeasure c alpha gamma).withDensity
        (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
        temperedStablePositiveMeasure c alpha 0)

noncomputable def exerciseGroupBCertification : Prop :=
  cert_exercise_3_4 ∧
  cert_exercise_3_5 ∧
  cert_exercise_3_6 ∧
  cert_exercise_3_7 ∧
  cert_exercise_3_4_regimes

end Kyprianou.Ch03


