-- Prove2me | Definitions.Def_Kyprianou_Ch02_ChapterCertificationV3
-- name    : Kyprianou_Ch02_ChapterCertificationV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T19:29:58.047036+00:00
-- url     : https://prove2.me/theorems/d45b5c2a-bebb-4dac-929d-c918400d45c1
-- title:
--   Chapter 2 V3: complete source-faithful new theorem and exercise certificates
-- statement:
--   Exact universally quantified logical certificates for the corrected and added Chapter 2 textbook results and all exercises, each generated from its canonical full open theorem statement. Reuses the unchanged V2 certificates for the published foundational milestones; excludes the superseded Lemma 2.14 sign.
-- source:
--   Kyprianou (2006), Chapter 2, pp. 33-66; corrections and exercise solutions in source-issues.json

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV2
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Mathlib

open MeasureTheory ProbabilityTheory Complex Filter Kyprianou Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

/- V3 source-exact certificates for new mandatory results and exercises. -/

noncomputable def certificateV3_subordinatorCriterionCh02V3 : Prop :=
  ∀ (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
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
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure

noncomputable def certificateV3_poissonRandomMeasureExistsGenericCh02V3 : Prop :=
  ∀ (E : Type) [MeasurableSpace E] (m : Measure E) [SigmaFinite m],
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ N : Ω → Measure E,
          (∀ (A : Set E), MeasurableSet A →
            Measurable (fun ω => N ω A)) ∧
          (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
            ∀ᵐ ω ∂P, ∃ n : ℕ, N ω A = n) ∧
          (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
            P.map (fun ω => N ω A) =
              (ProbabilityTheory.poissonMeasure (m A).toNNReal).map
                (Nat.cast : ℕ → ENNReal)) ∧
          (∀ (A : Set E), MeasurableSet A → m A = ⊤ →
            ∀ᵐ ω ∂P, N ω A = ⊤) ∧
          (∀ {ι : Type} [Countable ι] (A : ι → Set E),
            (∀ i, MeasurableSet (A i)) →
            Pairwise (fun i j => Disjoint (A i) (A j)) →
            ProbabilityTheory.iIndepFun (fun i (ω : Ω) => N ω (A i)) P)

noncomputable def certificateV3_poissonRestrictionAndIndependenceCh02V3 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν),
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A → MeasurableSet B →
       LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B) < ⊤ →
       P.map (fun ω => N.N ω (A ∩ B)) =
         LevyStochCalc.Poisson.poissonMeasureENN
           (LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B)).toNNReal) ∧
    (∀ {ι : Type} [Countable ι]
       (A : ι → Set (ℝ × ℝ)) (B : Set (ℝ × ℝ)),
       MeasurableSet B →
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       (∀ i, A i ⊆ B) →
       ProbabilityTheory.iIndepFun
          (fun i (ω : Ω) => (N.N ω).restrict B (A i)) P) ∧
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A →
      MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set (ℝ × ℝ) |
             C ⊆ A ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)
        (⨆ D ∈ {D : Set (ℝ × ℝ) |
             D ⊆ B ∧ MeasurableSet D},
          MeasurableSpace.comap (fun ω => N.N ω D) inferInstance)
        P)

noncomputable def certificateV3_finiteRegionPoissonIntegralCh02V3 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤),
    ProbabilityTheory.IsLevyProcess
      (fun t ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => ∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν)

noncomputable def certificateV3_compensatedGeneralRegionMartingaleCh02V3 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B)),
    ∃ (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ ∧
      MeasureTheory.Martingale
        (fun (t : ℝ≥0) ω =>
          (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
             z.2 ∂(N.N ω)) -
          (t : ℝ) * (∫ x in B, x ∂ν)) ℱ P ∧
      (MemLp (fun x : ℝ => x) 2 (ν.restrict B) →
       ∀ t : ℝ≥0, MemLp
         (fun ω =>
           (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
              z.2 ∂(N.N ω)) -
           (t : ℝ) * (∫ x in B, x ∂ν)) 2 P)

noncomputable def certificateV3_exercise2_1_AllPartsCh02V3 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℕ → ℝ≥0) (N : ℕ → Ω → ℕ)
    (hlaw : ∀ k, P.map (N k) = ProbabilityTheory.poissonMeasure (rate k))
    (hind : ProbabilityTheory.iIndepFun N P),
    (((∑' k, (rate k : ℝ≥0∞)) < ⊤) →
       (P.map (fun ω => ∑' k, ((N k ω : ℕ) : ℝ≥0∞)) =
          (ProbabilityTheory.poissonMeasure
            ((∑' k, (rate k : ℝ≥0∞)).toNNReal)).map
              (Nat.cast : ℕ → ENNReal)) ∧
       (∀ᵐ ω ∂P, (∑' k, ((N k ω : ℕ) : ℝ≥0∞)) < ⊤)) ∧
    (((∑' k, (rate k : ℝ≥0∞)) = ⊤) →
       ∀ᵐ ω ∂P, (∑' k, ((N k ω : ℕ) : ℝ≥0∞)) = ⊤)

noncomputable def certificateV3_exercise2_3_AllPartsCh02V3 : Prop :=
  ∀ {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x),
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) ↔
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤

noncomputable def certificateV3_exercise2_4_AllPartsCh02V3 : Prop :=
  let isCadlagOnUnit : (ℝ → ℝ) → Prop := fun f =>
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t) ∧
    (∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℝ,
        Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l))
  ((∀ (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ),
      (∀ n, isCadlagOnUnit (fn n)) →
      (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |fn n t - f t| < ε) →
      isCadlagOnUnit f) ∧
   (∀ (f : ℝ → ℝ), isCadlagOnUnit f →
      (∀ c : ℝ, 0 < c →
        Set.Finite {t : ℝ |
          t ∈ Set.Ioc (0 : ℝ) 1 ∧
          ∃ l : ℝ,
            Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l) ∧
            c < |f t - l|}) ∧
      Set.Countable {t : ℝ |
        t ∈ Set.Ioc (0 : ℝ) 1 ∧
        ¬ ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) t}))

noncomputable def certificateV3_exercise2_6_AllPartsCh02V3 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (n : ℕ) (hn : 2 ≤ n),
    (∀ (t : ℝ≥0), 0 < t →
       ((∫⁻ ω, ∫⁻ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
            ENNReal.ofReal (|z.2| ^ n) ∂(N.N ω) ∂P) < ⊤ ↔
        Integrable (fun x : ℝ => |x| ^ n)
          (ν.restrict {x : ℝ | 1 ≤ |x|}))) ∧
    (Integrable (fun x : ℝ => |x| ^ n)
        (ν.restrict {x : ℝ | 1 ≤ |x|}) →
      ∃ ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
        Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ ∧
        MeasureTheory.Martingale
          (fun (t : ℝ≥0) ω =>
            (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
               z.2 ^ n ∂(N.N ω)) -
            (t : ℝ) * ∫ x, x ^ n ∂ν) ℱ P)

noncomputable def certificateV3_exercise2_8_AllPartsCh02V3 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ),
    ∃ (Spos Sneg : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess Spos P ∧
      ProbabilityTheory.IsLevyProcess Sneg P ∧
      (∀ᵐ ω ∂P, Monotone (fun t => Spos t ω)) ∧
      (∀ᵐ ω ∂P, Monotone (fun t => Sneg t ω)) ∧
      ProbabilityTheory.iIndepFun
        (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then Spos t ω else Sneg t ω) P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = Spos t ω - Sneg t ω)

noncomputable def certificateV3_exercise2_11_AllPartsCh02V3 : Prop :=
  ∀ (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hsub : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω))
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, ν, hν⟩ ξ)),
    let d : ℝ := -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν
    (∀ q : ℝ, 0 ≤ q →
       ∫ ω, Real.exp (-q * X 1 ω) ∂P =
       Real.exp (-(d * q +
         ∫ x in Set.Ioi (0 : ℝ),
           (1 - Real.exp (-q * x)) ∂ν))) ∧
    (∀ q : ℝ, 0 < q →
       ∫ x in Set.Ioi (0 : ℝ),
          (1 - Real.exp (-q * x)) ∂ν =
       q * ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-q * x) * (ν (Set.Ioi x)).toReal ∂volume) ∧
    Tendsto (fun q : ℝ =>
       (d * q +
         ∫ x in Set.Ioi (0 : ℝ),
           (1 - Real.exp (-q * x)) ∂ν) / q)
       atTop (nhds d)

noncomputable def certificateV3_exercise2_2_AllPartsCh02V3 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (hrate : 0 < rate)
    (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (hNlaw : ∀ t, P.map (N t) =
      ProbabilityTheory.poissonMeasure (rate * t))
    (hNlevy : ProbabilityTheory.IsLevyProcess
      (fun t ω => (N t ω : ℝ)) P)
    (harrival : ∀ᵐ ω ∂P, ∀ (n : ℕ), 0 < n →
      ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t)),
    (∀ (t : ℝ≥0), 0 < t → ∀ (n : ℕ), 0 < n →
      ∀ (A : Set (Fin n → ℝ)), MeasurableSet A →
        P {ω | N t ω = n ∧
          (fun i : Fin n => ((T (i.val + 1) ω : ℝ))) ∈ A} =
        P {ω | N t ω = n} *
          ENNReal.ofReal ((Nat.factorial n : ℝ) / ((t : ℝ) ^ n)) *
          volume (A ∩
            {v : Fin n → ℝ |
              (∀ i, 0 ≤ v i ∧ v i ≤ (t : ℝ)) ∧
              Monotone v})) ∧
    (∀ (t : ℝ≥0), 0 < t → ∀ (n : ℕ), 0 < n →
      ∀ (U V : Fin n → Ω → ℝ),
        (∀ i, P.map (U i) =
          (ENNReal.ofReal (t : ℝ))⁻¹ •
            (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)))) →
        ProbabilityTheory.iIndepFun U P →
        (∀ᵐ ω ∂P,
          Monotone (fun i : Fin n => V i ω) ∧
          (List.ofFn (fun i : Fin n => V i ω)).Perm
            (List.ofFn (fun i : Fin n => U i ω))) →
        ((P.restrict {ω | N t ω = n}).map
          (fun ω => fun i : Fin n => (T (i.val + 1) ω : ℝ))) =
        (P {ω | N t ω = n}) •
          (P.map (fun ω => fun i : Fin n => V i ω)))

noncomputable def certificateV3_exercise2_7_AllPartsCh02V3 : Prop :=
  ∀ (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, ν, hν⟩ ξ)),
    let piecewiseLinear : (ℝ≥0 → ℝ) → Prop := fun f =>
      ∃ (T : ℕ → ℝ≥0), T 0 = 0 ∧ StrictMono T ∧
        Tendsto T atTop atTop ∧
        ∀ n : ℕ, ∃ (slope intercept : ℝ),
          ∀ t : ℝ≥0, T n ≤ t → t < T (n + 1) →
            f t = slope * (t : ℝ) + intercept
    (∀ (t : ℝ≥0) (threshold : ℝ), 0 < threshold →
      P {ω | ∃ s : ℝ≥0, 0 < s ∧ s ≤ t ∧
        ∃ l : ℝ,
          Tendsto (fun u => X u ω)
            (nhdsWithin s (Set.Iio s)) (nhds l) ∧
          threshold < |X s ω - l|} =
      ENNReal.ofReal (1 -
        Real.exp (-(t : ℝ) *
          (ν {x : ℝ | threshold < |x|}).toReal))) ∧
    ((∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) ↔
      ν = 0) ∧
    ((∀ᵐ ω ∂P, piecewiseLinear (fun t => X t ω)) ↔
      σ = 0 ∧ ν Set.univ < ⊤) ∧
    (ν Set.univ = ⊤ →
      ∀ᵐ ω ∂P,
        closure {t : ℝ≥0 |
          ¬ ContinuousAt (fun s : ℝ≥0 => X s ω) t} =
          Set.univ)

noncomputable def certificateV3_exercise2_10_AllPartsCh02V3 : Prop :=
  ∀ (d : ℕ) (hd : 1 < d) (a : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hApos : ∀ v : Fin d → ℝ,
      0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j)
    (ν : Measure (Fin d → ℝ))
    (hzero : ν {0} = 0)
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤),
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ X : ℝ≥0 → Ω → (Fin d → ℝ),
          (∀ᵐ ω ∂P,
            (∀ t : ℝ≥0,
              ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) ∧
            ∀ t : ℝ≥0, 0 < t →
              ∃ l : Fin d → ℝ,
                Tendsto (fun s => X s ω)
                  (nhdsWithin t (Set.Iio t)) (nhds l)) ∧
          (∀ᵐ ω ∂P, X 0 ω = 0) ∧
          (∀ (s t : ℝ≥0), s ≤ t →
            ProbabilityTheory.Indep
              (MeasurableSpace.comap
                (fun ω => X t ω - X s ω) inferInstance)
              (⨆ u ∈ Set.Iic s,
                MeasurableSpace.comap (X u) inferInstance) P) ∧
          (∀ (s t : ℝ≥0), s ≤ t →
            P.map (fun ω => X t ω - X s ω) =
              P.map (X (t - s))) ∧
          (∀ (t : ℝ≥0) (θ : Fin d → ℝ),
            ∫ ω, Complex.exp (Complex.I *
              (((∑ i : Fin d, θ i * X t ω i : ℝ)) : ℂ)) ∂P =
            Complex.exp (-(t : ℝ) *
              (Complex.I *
                (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
               (((∑ i : Fin d, ∑ j : Fin d,
                   θ i * A i j * θ j : ℝ) / 2) : ℂ) +
               ∫ x, (1 -
                 Complex.exp (Complex.I *
                   (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
                 Complex.I *
                   (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
                   (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν)))

noncomputable def certificateV3_exercise2_5_AllPartsCh02V3 : Prop :=
  (∃ (F : ℝ → ℝ),
      ContinuousOn F (Set.Icc (0 : ℝ) 1) ∧
      MonotoneOn F (Set.Icc (0 : ℝ) 1) ∧
      F 0 = 0 ∧ F 1 = 1 ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / 3),
        F x = (1 / 2 : ℝ) * F (3 * x)) ∧
      (∀ x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3),
        F x = (1 / 2 : ℝ)) ∧
      (∀ x ∈ Set.Icc (2 / 3 : ℝ) 1,
        F x = (1 / 2 : ℝ) + (1 / 2 : ℝ) * F (3 * x - 2)) ∧
      let inverse : ℝ → ℝ := fun x =>
        if x < 1 then sInf
          {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ x < F θ}
        else 1
      ∀ (a : ℝ),
        let g : ℝ → ℝ := fun x => inverse x - a * x
        (MonotoneOn g (Set.Icc (0 : ℝ) 1) ↔ a ≤ 0) ∧
        LocallyBoundedVariationOn g (Set.Icc (0 : ℝ) 1) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1,
          ContinuousWithinAt g (Set.Icc x 1) x) ∧
        (∀ x ∈ Set.Ioc (0 : ℝ) 1, ∃ l : ℝ,
          Tendsto g (nhdsWithin x (Set.Iio x)) (nhds l) ∧
          l ≤ g x) ∧
        closure {x : ℝ |
          x ∈ Set.Icc (0 : ℝ) 1 ∧
          ∃ l : ℝ,
            Tendsto g (nhdsWithin x (Set.Iio x)) (nhds l) ∧
            l < g x} = Set.Icc (0 : ℝ) 1) ∧
    (∃ f : ℝ → ℝ,
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        ContinuousWithinAt f (Set.Icc x 1) x) ∧
      (∀ x ∈ Set.Ioc (0 : ℝ) 1,
        ∃ l : ℝ,
          Tendsto f (nhdsWithin x (Set.Iio x)) (nhds l)) ∧
      ¬ LocallyBoundedVariationOn f (Set.Icc (0 : ℝ) 1) ∧
      (∀ (n k : ℕ), 0 < n → Odd k →
        (k : ℝ) / (2 : ℝ) ^ n ≤ 1 →
        ∃ l : ℝ,
          Tendsto f
            (nhdsWithin ((k : ℝ) / (2 : ℝ) ^ n)
              (Set.Iio ((k : ℝ) / (2 : ℝ) ^ n)))
            (nhds l) ∧
          f ((k : ℝ) / (2 : ℝ) ^ n) - l =
          (if k % 4 = 1 then (1 : ℝ) / (2 : ℝ) ^ n
            else -(1 : ℝ) / (2 : ℝ) ^ n)))

noncomputable def certificateV3_exercise2_9_AllPartsCh02V3 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (α β c σ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hσ : 0 < σ)
    (Γ : ℝ≥0 → Ω → ℝ≥0)
    (hΓlevy : ProbabilityTheory.IsLevyProcess
      (fun t ω => (Γ t ω : ℝ)) P)
    (hΓsub : ∀ᵐ ω ∂P, Monotone (fun t => Γ t ω))
    (hΓlaplace : ∀ (q : ℝ), 0 ≤ q → ∀ (t : ℝ≥0),
      ∫ ω, Real.exp (-q * (Γ t ω : ℝ)) ∂P =
        Real.exp (-(t : ℝ) * β * Real.log (1 + q / α)))
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then B.W (t : ℝ) ω else (Γ t ω : ℝ)) P),
    let X : ℝ≥0 → Ω → ℝ := fun t ω =>
      c * (Γ t ω : ℝ) + σ * B.W (Γ t ω : ℝ) ω
    let αpos : ℝ :=
      (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α))
        + c / (2 * α))⁻¹
    let αneg : ℝ :=
      (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α))
        - c / (2 * α))⁻¹
    (ProbabilityTheory.IsLevyProcess X P ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (X t)) ξ =
        Complex.exp (-(((t : ℝ) : ℂ)) * (β : ℂ) *
          Complex.log (1 - Complex.I *
            (((ξ * c / α : ℝ) : ℂ)) +
            (((σ ^ 2 * ξ ^ 2 / (2 * α) : ℝ) : ℂ)))) ∧
    (∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
      letI : MeasurableSpace Ω' := measΩ'
      ∃ (P' : Measure Ω') (probP' : IsProbabilityMeasure P'),
        letI : IsProbabilityMeasure P' := probP'
        ∃ (Γpos Γneg : ℝ≥0 → Ω' → ℝ≥0),
          ProbabilityTheory.IsLevyProcess
            (fun t ω => (Γpos t ω : ℝ)) P' ∧
          ProbabilityTheory.IsLevyProcess
            (fun t ω => (Γneg t ω : ℝ)) P' ∧
          (∀ᵐ ω ∂P', Monotone (fun t => Γpos t ω)) ∧
          (∀ᵐ ω ∂P', Monotone (fun t => Γneg t ω)) ∧
          ProbabilityTheory.iIndepFun
            (fun (i : Fin 2) (ω : Ω') => fun t : ℝ≥0 =>
              if i = 0 then (Γpos t ω : ℝ) else (Γneg t ω : ℝ)) P' ∧
          (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
            ∫ ω, Real.exp (-q * (Γpos t ω : ℝ)) ∂P' =
              Real.exp (-(t : ℝ) * β *
                Real.log (1 + q / αpos))) ∧
          (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
            ∫ ω, Real.exp (-q * (Γneg t ω : ℝ)) ∂P' =
              Real.exp (-(t : ℝ) * β *
                Real.log (1 + q / αneg))) ∧
          (∀ t : ℝ≥0, ∀ ξ : ℝ,
            charFun (P.map (X t)) ξ =
            charFun (P'.map (fun ω =>
              (Γpos t ω : ℝ) - (Γneg t ω : ℝ))) ξ)))

noncomputable def certificateV3_exercise2_12_AllPartsCh02V3 : Prop :=
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P]
       (α C : ℝ) (hα : 0 < α) (hα2 : α < 2) (hC : 0 < C)
       (B : LevyStochCalc.Brownian.BrownianMotion P)
       (τ : ℝ≥0 → Ω → ℝ≥0)
       (hτ : ProbabilityTheory.IsLevyProcess
         (fun t ω => (τ t ω : ℝ)) P)
       (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
       (hlaplace : ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
         ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P =
         Real.exp (-(t : ℝ) * C * q ^ (α / 2)))
       (hind : ProbabilityTheory.iIndepFun
         (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then B.W (t : ℝ) ω else (τ t ω : ℝ)) P),
       ProbabilityTheory.IsLevyProcess
         (fun t ω => B.W (τ t ω : ℝ) ω) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map (fun ω => B.W (τ t ω : ℝ) ω)) ξ =
         Complex.exp ((-(t : ℝ) * C * ((ξ ^ 2 / 2) ^ (α / 2)) : ℝ))) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P] (a : ℝ) (ha : 0 < a)
       (B : LevyStochCalc.Brownian.BrownianMotion P)
       (τ : ℝ≥0 → Ω → ℝ≥0)
       (hτ : ProbabilityTheory.IsLevyProcess
         (fun t ω => (τ t ω : ℝ)) P)
       (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
       (hlaplace : ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
         ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P =
         Real.exp (-(t : ℝ) * (2 / a) * (q / (q + a ^ 2))))
       (hind : ProbabilityTheory.iIndepFun
         (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then B.W (t : ℝ) ω else (τ t ω : ℝ)) P),
       ProbabilityTheory.IsLevyProcess
         (fun t ω => Real.sqrt 2 * B.W (τ t ω : ℝ) ω) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map
           (fun ω => Real.sqrt 2 * B.W (τ t ω : ℝ) ω)) ξ =
         Complex.exp ((-(t : ℝ) * (2 / a) *
           (ξ ^ 2 / (ξ ^ 2 + a ^ 2)) : ℝ))) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P] (rate σ : ℝ)
       (hrate : 0 < rate) (hσ : 0 < σ)
       (B : LevyStochCalc.Brownian.BrownianMotion P)
       (N : ℝ≥0 → Ω → ℕ)
       (hNlaw : ∀ t : ℝ≥0,
         P.map (N t) =
         ProbabilityTheory.poissonMeasure (⟨2 * rate * (t : ℝ), by positivity⟩))
       (hNlevy : ProbabilityTheory.IsLevyProcess
         (fun t ω => (N t ω : ℝ)) P)
       (hind : ProbabilityTheory.iIndepFun
         (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then B.W (t : ℝ) ω else (N t ω : ℝ)) P),
       ProbabilityTheory.IsLevyProcess
         (fun t ω => σ * B.W (N t ω : ℝ) ω) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map
           (fun ω => σ * B.W (N t ω : ℝ) ω)) ξ =
         Complex.exp ((-(t : ℝ) * 2 * rate *
           (1 - Real.exp (-(σ ^ 2 * ξ ^ 2) / 2)) : ℝ))) ∧
    (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
       [IsProbabilityMeasure P]
       (α β C : ℝ) (hα : 0 < α) (hα2 : α < 2)
       (hβ : 0 < β) (hβ1 : β < 1)
       (hadmissible : α / β ≤ 2) (hC : 0 < C)
       (X : ℝ≥0 → Ω → ℝ)
       (hX : ProbabilityTheory.IsLevyProcess X P)
       (hXstable : ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map (X t)) ξ =
         Complex.exp ((-(t : ℝ) * C * |ξ| ^ α : ℝ))),
       ∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
         letI : MeasurableSpace Ω' := measΩ'
         ∃ (P' : Measure Ω') (probP' : IsProbabilityMeasure P'),
           letI : IsProbabilityMeasure P' := probP'
           ∃ (Y : ℝ≥0 → Ω' → ℝ) (τ : ℝ≥0 → Ω' → ℝ≥0),
             ProbabilityTheory.IsLevyProcess Y P' ∧
             ProbabilityTheory.IsLevyProcess
               (fun t ω => (τ t ω : ℝ)) P' ∧
             (∀ᵐ ω ∂P', Monotone (fun t => τ t ω)) ∧
             (∀ (t : ℝ≥0) (ξ : ℝ),
               charFun (P'.map (Y t)) ξ =
               Complex.exp ((-(t : ℝ) *
                 (C ^ (1 / β)) * |ξ| ^ (α / β) : ℝ))) ∧
             (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
               ∫ ω, Real.exp (-q * (τ t ω : ℝ)) ∂P' =
               Real.exp (-(t : ℝ) * q ^ β)) ∧
             ProbabilityTheory.iIndepFun
               (fun (i : Fin 2) (ω : Ω') => fun t : ℝ≥0 =>
                 if i = 0 then Y t ω else (τ t ω : ℝ)) P' ∧
             ProbabilityTheory.IsLevyProcess
               (fun t ω => Y (τ t ω) ω) P' ∧
             (∀ (t : ℝ≥0),
               P.map (X t) =
                 P'.map (fun ω => Y (τ t ω) ω)))

noncomputable def certificateV3_poissonRandomMeasureSupportGenericCh02V3 : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hfamily : ProbabilityTheory.IsPoissonPointFamily K Y m P),
    (∀ᵐ ω ∂P,
      Set.Countable
        {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0}) ∧
    (m Set.univ < ⊤ →
      ∀ᵐ ω ∂P,
        Set.Finite
          {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0})

noncomputable def certificateV3_independentSubordinationCh02V3 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (Ψ : ℝ → ℂ)
    (aτ : ℝ) (στ : ℝ≥0) (ντ : Measure ℝ)
    (hντ : ProbabilityTheory.IsLevyMeasure ντ)
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
    (hτchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => (τ t ω : ℝ))) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-aτ, στ ^ 2, ντ, hντ⟩ ξ)),
    let d : ℝ := -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ
    let Ξ : ℂ → ℂ := fun z =>
      (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ),
        (1 - Complex.exp (-z * ((x : ℝ) : ℂ))) ∂ντ
    ProbabilityTheory.IsLevyProcess
      (fun t ω => X (τ t ω) ω) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => X (τ t ω) ω)) ξ =
      Complex.exp (-(((t : ℝ) : ℂ)) * Ξ (Ψ ξ))

noncomputable def certificateV3_markedCompoundPoissonRandomMeasureCh02V4 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFzero : F {0} = 0)
    (N : ℝ≥0 → Ω → ℕ)
    (T : ℕ → Ω → ℝ≥0)
    (ξ : ℕ → Ω → ℝ)
    (hNlevy : ProbabilityTheory.IsLevyProcess
       (fun t ω => (N t ω : ℝ)) P)
    (hNlaw : ∀ t : ℝ≥0,
       P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (harrival : ∀ᵐ ω ∂P,
       ∀ (n : ℕ), 0 < n →
         ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t))
    (hmarklaw : ∀ k : ℕ, P.map (ξ k) = F)
    (hIID : ProbabilityTheory.iIndepFun ξ P)
    (hcross : ProbabilityTheory.Indep
      (⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (N t) inferInstance) P),
    let μ : Ω → Measure (ℝ × ℝ) := fun ω =>
      Measure.sum (fun n : ℕ =>
        Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))
    let intensity : Measure (ℝ × ℝ) :=
      (volume.restrict (Set.Ici (0 : ℝ))).prod ((rate : ENNReal) • F)
    (∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
       intensity A < ⊤ →
       P.map (fun ω => μ ω A) =
         (ProbabilityTheory.poissonMeasure (intensity A).toNNReal).map
           (Nat.cast : ℕ → ENNReal)) ∧
    (∀ {ι : Type} [Countable ι] (A : ι → Set (ℝ × ℝ)),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => μ ω (A i)) P) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
       μ ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) = (N t ω : ENNReal))

noncomputable def certificateV3_compoundPoissonDriftPathCriterionCh02V3 : Prop :=
  ∀ (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)),
    ((∃ (d : ℝ),
      (levyMeasure = 0 ∧
       ∀ (t : ℝ≥0), ∀ᵐ ω ∂P, X t ω = d * (t : ℝ)) ∨
      (∃ (r : ℝ≥0) (hr : 0 < r)
         (F : Measure ℝ) (hF : IsProbabilityMeasure F),
         letI : IsProbabilityMeasure F := hF
         levyMeasure = (r : ENNReal) • F ∧
         ∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
           letI : MeasurableSpace Ω' := measΩ'
           ∃ (P' : Measure Ω') (hP' : IsProbabilityMeasure P'),
             letI : IsProbabilityMeasure P' := hP'
             ∃ (τ Y : ℕ → Ω' → ℝ),
               LevyFoundations.IsCompoundPoissonDriver τ Y r F P' ∧
               ∀ (t : ℝ≥0),
                 P.map (X t) =
                   P'.map (fun ω =>
                     LevyFoundations.compoundPoisson d τ Y (t : ℝ) ω))) ↔
     σ = 0 ∧ levyMeasure Set.univ < ⊤)

end Kyprianou.Ch02


