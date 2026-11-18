-- Prove2me | Definitions.Def_Kyprianou_Ch02_ChapterCertificationV6
-- name    : Kyprianou_Ch02_ChapterCertificationV6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T12:33:22.475206+00:00
-- url     : https://prove2.me/theorems/50b329db-7a2e-48b4-935c-192fe0d24e15
-- title:
--   Chapter 2 V6: positive arrival-index quantified source certificates
-- statement:
--   Source-exact quantified certificates for marked Lemma 2.2 and Exercise 2.2 without an unused index-zero measurability assumption. Imports previously published V5 certificates; the old immutable theorems and certificates remain available as historical references.
-- source:
--   Kyprianou (2006), Chapter 2 pp. 37-38, 63-64; source-fidelity reverse-domain audit, 2026-11-17

import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV5
open MeasureTheory ProbabilityTheory Complex Filter Kyprianou Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

noncomputable def certificateV6_markedCompoundPoissonRandomMeasureCh02V6 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFzero : F {0} = 0)
    (N : ℝ≥0 → Ω → ℕ)
    (T : ℕ → Ω → ℝ≥0)
    (ξ : ℕ → Ω → ℝ)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
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
noncomputable def certificateV6_exercise2_2_AllPartsCh02V6 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (rate : ℝ≥0) (hrate : 0 < rate)
    (N : ℝ≥0 → Ω → ℕ) (T : ℕ → Ω → ℝ≥0)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
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

end Kyprianou.Ch02


