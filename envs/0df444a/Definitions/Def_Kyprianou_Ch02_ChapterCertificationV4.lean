-- Prove2me | Definitions.Def_Kyprianou_Ch02_ChapterCertificationV4
-- name    : Kyprianou_Ch02_ChapterCertificationV4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T16:36:58.028303+00:00
-- url     : https://prove2.me/theorems/5b0213af-f694-444a-89cf-5ff92eeff60b
-- title:
--   Chapter 2 V4: repaired Brownian and marked-Poisson certificates
-- statement:
--   Source-equivalent V4 certificates for Exercises 2.2, 2.9, 2.12 and marked Lemma 2.2, retaining V2/V3 independently valid certificates.
-- source:
--   Kyprianou 2006 chapter 2 pp. 33-66; correction ledger 2026-11-16

import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV3
open MeasureTheory ProbabilityTheory Complex Filter Kyprianou Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

noncomputable def certificateV4_exercise2_9_AllPartsCh02V4 : Prop :=
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
      c * (Γ t ω : ℝ) + σ * (B.W (Γ t ω : ℝ) ω - B.W 0 ω)
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

noncomputable def certificateV4_exercise2_12_AllPartsCh02V4 : Prop :=
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
         (fun t ω => (B.W (τ t ω : ℝ) ω - B.W 0 ω)) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map (fun ω => (B.W (τ t ω : ℝ) ω - B.W 0 ω))) ξ =
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
         (fun t ω => Real.sqrt 2 * (B.W (τ t ω : ℝ) ω - B.W 0 ω)) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map
           (fun ω => Real.sqrt 2 * (B.W (τ t ω : ℝ) ω - B.W 0 ω))) ξ =
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
         (fun t ω => σ * (B.W (N t ω : ℝ) ω - B.W 0 ω)) P ∧
       ∀ (t : ℝ≥0) (ξ : ℝ),
         charFun (P.map
           (fun ω => σ * (B.W (N t ω : ℝ) ω - B.W 0 ω))) ξ =
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

noncomputable def certificateV4_exercise2_2_AllPartsCh02V4 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (hrate : 0 < rate)
    (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (hTmeas : ∀ n : ℕ, Measurable (T n))
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

noncomputable def certificateV4_markedCompoundPoissonRandomMeasureCh02V5 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFzero : F {0} = 0)
    (N : ℝ≥0 → Ω → ℕ)
    (T : ℕ → Ω → ℝ≥0)
    (ξ : ℕ → Ω → ℝ)
    (hTmeas : ∀ n : ℕ, Measurable (T n))
    (hξmeas : ∀ k : ℕ, Measurable (ξ k))
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
    (∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
       intensity A = ⊤ →
       ∀ᵐ ω ∂P, μ ω A = ⊤) ∧
    (∀ {ι : Type} [Countable ι] (A : ι → Set (ℝ × ℝ)),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => μ ω (A i)) P) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
       μ ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) = (N t ω : ENNReal))

end Kyprianou.Ch02


