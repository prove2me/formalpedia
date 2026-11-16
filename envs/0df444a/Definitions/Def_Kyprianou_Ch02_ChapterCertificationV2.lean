-- Prove2me | Definitions.Def_Kyprianou_Ch02_ChapterCertificationV2
-- name    : Kyprianou_Ch02_ChapterCertificationV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:23:06.74421+00:00
-- url     : https://prove2.me/theorems/cfa4aed3-59f9-45a5-8f01-754a970e8141
-- title:
--   Corrected Chapter 2 proof obligations including path structure
-- statement:
--   Revised universal source-theorem certificates with exact filtration, finite-band hypotheses and path-type statements.
-- source:
--   A. E. Kyprianou (2006), Chapter 2, pp. 33–66

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

open MeasureTheory ProbabilityTheory Kyprianou Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
/-- Encodes precisely the stored open theorem Kyprianou.poissonRandomMeasureExists as a proposition. -/
noncomputable def certificateV2_poissonRandomMeasureExists : Prop :=
  ∀ (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure],
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        Nonempty (LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)

/-- Encodes precisely the stored open theorem Kyprianou.poissonRandomMeasureSupportCountable as a proposition. -/
noncomputable def certificateV2_poissonRandomMeasureSupportCountable : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure),
    (∀ᵐ ω ∂P,
      Set.Countable {z : ℝ × ℝ | N.N ω {z} ≠ 0}) ∧
    ∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
      LevyStochCalc.Poisson.referenceIntensity levyMeasure A < ⊤ →
      ∀ᵐ ω ∂P,
        Set.Finite {z : ℝ × ℝ | z ∈ A ∧ N.N ω {z} ≠ 0}

/-- Encodes precisely the stored open theorem Kyprianou.poissonRandomMeasureIntegralLaws as a proposition. -/
noncomputable def certificateV2_poissonRandomMeasureIntegralLaws : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f),
    ((∀ᵐ ω ∂P,
      Integrable f (ProbabilityTheory.poissonRandomMeasure K Y ω)) ↔
      Integrable (fun x => min (1 : ℝ) |f x|) m) ∧
    (Integrable (fun x => min (1 : ℝ) |f x|) m →
      ∀ ξ : ℝ,
        charFun (P.map (fun ω =>
          ∫ x, f x ∂(ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
        Complex.exp
          (∫ x, (Complex.exp (Complex.I *
            (((ξ * f x : ℝ) : ℂ))) - 1) ∂m)) ∧
    (Integrable f m →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
        ∫ x, f x ∂m) ∧
    ((Integrable f m ∧ MemLp f 2 m) →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
          (∫ x, f x ^ 2 ∂m) + (∫ x, f x ∂m) ^ 2)

/-- Encodes precisely the stored open theorem Kyprianou.largeJumpProcessLevy as a proposition. -/
noncomputable def certificateV2_largeJumpProcessLevy : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure),
    ProbabilityTheory.IsLevyProcess (largeJumpProcess P levyMeasure N) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (largeJumpProcess P levyMeasure N t)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in {x : ℝ | 1 ≤ |x|},
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure)

/-- Encodes precisely the stored open theorem Kyprianou.compensatedBandIsL2Martingale as a proposition. -/
noncomputable def certificateV2_compensatedBandIsL2Martingale : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1),
    ∃ (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale
        (compensatedSmallJumpBand P levyMeasure N ε) ℱ P ∧
      ∀ t : ℝ≥0,
        MemLp (compensatedSmallJumpBand P levyMeasure N ε t) 2 P

/-- Encodes precisely the stored open theorem Kyprianou.smallJumpLimitCadlag as a proposition. -/
noncomputable def certificateV2_smallJumpLimitCadlag : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure),
    ∃ (M : ℝ≥0 → Ω → ℝ)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      ProbabilityTheory.IsLevyProcess M P ∧
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale M ℱ P ∧
      (∀ t, MemLp (M t) 2 P) ∧
      (∀ᵐ ω ∂P,
        (∀ t : ℝ≥0,
          ContinuousWithinAt (fun s => M s ω) (Set.Ici t) t) ∧
        ∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ,
            Tendsto (fun s => M s ω)
              (nhdsWithin t (Set.Iio t)) (nhds l)) ∧
      (∀ᵐ ω ∂P,
        Set.Countable {t : ℝ≥0 |
          ¬ ContinuousAt (fun s => M s ω) t}) ∧
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ)

/-- Encodes precisely the stored open theorem Kyprianou.sumOfIndependentLevyProcesses as a proposition. -/
noncomputable def certificateV2_sumOfIndependentLevyProcesses : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : ProbabilityTheory.IsLevyProcess Xgauss P)
    (hlarge : ProbabilityTheory.IsLevyProcess Xlarge P)
    (hsmall : ProbabilityTheory.IsLevyProcess Xsmall P)
    (hind : IndependentLevyItoComponents P Xgauss Xlarge Xsmall),
    ProbabilityTheory.IsLevyProcess
      (fun t ω => Xgauss t ω + Xlarge t ω + Xsmall t ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
        charFun (P.map (Xgauss t)) ξ *
        charFun (P.map (Xlarge t)) ξ *
        charFun (P.map (Xsmall t)) ξ

/-- Encodes precisely the stored open theorem Kyprianou.levyItoDecomposition as a proposition. -/
noncomputable def certificateV2_levyItoDecomposition : Prop :=
  ∀ (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure),
    ∃ (hσ : SigmaFinite levyMeasure),
      letI : SigmaFinite levyMeasure := hσ
      ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
        letI : MeasurableSpace Ω := measΩ
        ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
          letI : IsProbabilityMeasure P := probP
          ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
      (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      (∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) ∧
      (∀ t ω, Xlarge t ω = largeJumpProcess P levyMeasure N t ω) ∧
      ProbabilityTheory.IsLevyProcess Xgauss P ∧
      ProbabilityTheory.IsLevyProcess Xlarge P ∧
      ProbabilityTheory.IsLevyProcess Xsmall P ∧
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale Xsmall ℱ P ∧
      (∀ t, MemLp (Xsmall t) 2 P) ∧
      (∀ᵐ ω ∂P,
        (∀ t : ℝ≥0,
          ContinuousWithinAt (fun s => Xsmall s ω) (Set.Ici t) t) ∧
        Set.Countable
          {t : ℝ≥0 | ¬ ContinuousAt (fun s => Xsmall s ω) t} ∧
        ∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ,
            Tendsto (fun s => Xsmall s ω) (nhdsWithin t (Set.Iio t)) (nhds l) ∧
            (Xsmall t ω ≠ l → |Xsmall t ω - l| < 1)) ∧
      (∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (Xsmall t)) ξ =
          Complex.exp ((((t : ℝ) : ℂ)) *
            ∫ x in Set.Ioo (-1 : ℝ) 1,
              ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure)) ∧
      IndependentLevyItoComponents P Xgauss Xlarge Xsmall ∧
      ProbabilityTheory.IsLevyProcess
        (fun t ω => Xgauss t ω + Xlarge t ω + Xsmall t ω) P ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun
          (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
          Complex.exp ((((t : ℝ) : ℂ)) *
            Kyprianou.Ch01.levyTripleExponent
              ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)


/-- Universal Chapter 2 path-structure certificate. -/
noncomputable def certificateV2_boundedVariationCriterionCh02 : Prop :=
  ∀ (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    ⦃Ω : Type⦄ [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)),
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => X t ω) Set.univ) ↔
    σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure

/-- Universal Chapter 2 path-structure certificate. -/
noncomputable def certificateV2_compoundPoissonDriftCriterionCh02 : Prop :=
  ∀ (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    ⦃Ω : Type⦄ [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)),
    (∃ (d : ℝ) (ν : Measure ℝ),
      ν Set.univ < ⊤ ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (X t)) ξ =
          Complex.exp ((((t : ℝ) : ℂ)) *
            (Complex.I * (((d * ξ : ℝ) : ℂ)) +
              ∫ x, (Complex.exp (Complex.I *
                (((ξ * x : ℝ) : ℂ))) - 1) ∂ν))) ↔
      σ = 0 ∧ levyMeasure Set.univ < ⊤

/-- Universal Chapter 2 path-structure certificate. -/
noncomputable def certificateV2_subordinatorCriterionCh02 : Prop :=
  ∀ (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    ⦃Ω : Type⦄ [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)),
    (∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) ↔
    levyMeasure (Set.Iio (0 : ℝ)) = 0 ∧
    σ = 0 ∧
    Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (levyMeasure.restrict (Set.Ioi (0 : ℝ))) ∧
    0 ≤ -a + ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure

/-- Universal Chapter 2 path-structure certificate. -/
noncomputable def certificateV2_independentSubordinationCh02 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (Ψ : ℝ → ℂ) (Ξ : ℂ → ℂ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess
       (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (hψ : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ψ ξ))
    (hξ : ∀ (t : ℝ≥0) (z : ℂ), 0 ≤ z.re →
      ∫ ω, Complex.exp (-z * (((τ t ω : ℝ) : ℂ))) ∂P =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z)),
    ProbabilityTheory.IsLevyProcess
      (fun t ω => X (τ t ω) ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
      Complex.exp (-(((t : ℝ) : ℂ)) * Ξ (Ψ ξ))

end Kyprianou.Ch02


