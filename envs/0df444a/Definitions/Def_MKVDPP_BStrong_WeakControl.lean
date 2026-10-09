-- Prove2me | Definitions.Def_MKVDPP_BStrong_WeakControl
-- name    : MKVDPP_BStrong_WeakControl
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:29.820707+00:00
-- url     : https://prove2.me/theorems/f6de2352-a1ad-4e8d-97b7-d333c846c30c
-- title:
--   Weak, strong and common noise adapted controls
-- statement:
--   A weak control $\gamma$ contains a probability space, two filtrations, a continuous state $X$, independent idiosyncratic and common Brownian increments after the initial time, a predictable control $\alpha$, and conditional laws $\mu,\bar\mu$. These laws are tied to the underlying probability by conditional expectation. The state obeys the McKean–Vlasov SDE and $\alpha$ has finite quadratic energy.
--
--   A strong control uses the probability augmented natural filtrations. A $\mathbb B$ strong control additionally has $\alpha$ predictable for common noise. Its intrinsic value is
--
--   $$V_S^{\mathbb B}(t,\nu)=\sup_{\gamma\in\Gamma_S^{\mathbb B}(t,\nu)}J(t,\gamma).$$
--
--   This definition is the control side of Proposition 2.10.
--
--   **Formalization Note** Conditional law identities hold for Lebesgue almost every time and probability almost every sample point. The continuous measure valued path is an explicit version of Remark 2.4.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, pp. 5–8, Definition 2.1, equations (2.5)–(2.7), Definition 2.6, equation (2.9)

import Definitions.Def_MKVDPP_BStrong_Setting

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

variable {T : ℝ≥0} {n d ell : ℕ} {U : Type*}
variable [MetricSpace U] [CompleteSpace U] [TopologicalSpace.SeparableSpace U]
variable [Nonempty U] [MeasurableSpace U] [BorelSpace U]

/-- The four canonical coordinates stopped as in (2.7): W remains unstopped. -/
noncomputable def hatStopped (s : ℝ≥0) (z : OmegaHat T n d ell) :
    OmegaHat T n d ell :=
  (stopPath s z.1, (z.2.1).comp (stopTimeMap s), z.2.2.1,
    stopPath s z.2.2.2)

/-- Definition 2.1, including (2.2)–(2.4), and the continuous conditional-law
version μ̂ of Remark 2.4. -/
structure WeakControl (M : Model T n d ell U) (Ω : Type) [mΩ : MeasurableSpace Ω]
    (t : ℝ≥0) (ν : ProbabilityMeasure (Cpath T n)) where
  P : ProbabilityMeasure Ω
  F : Filtration ℝ≥0 mΩ
  G : Filtration ℝ≥0 mΩ
  G_le_F : ∀ s, G s ≤ F s
  X : Ω → Cpath T n
  A : Ω → CR T
  W : Ω → Cpath T d
  B : Ω → Cpath T ell
  X_measurable : Measurable X
  A_measurable : Measurable A
  W_measurable : Measurable W
  B_measurable : Measurable B
  α : ℝ≥0 → Ω → U
  α_predictable : Measurable[F.predictable] (fun z : ℝ≥0 × Ω => α z.1 z.2)
  μ : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n)
  μbar : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n × U)
  μ_predictable : Measurable[G.predictable] (fun z : ℝ≥0 × Ω => μ z.1 z.2)
  μbar_predictable : Measurable[G.predictable] (fun z : ℝ≥0 × Ω => μbar z.1 z.2)
  μhat : Ω → C(Set.Icc (0 : ℝ) (T : ℝ), ProbabilityMeasure (OmegaHat T n d ell))
  μhat_measurable : Measurable μhat
  immersion : ∀ s, s ≤ T → ∀ D : Set Ω,
    MeasurableSet[F s ⊔ MeasurableSpace.comap W inferInstance] D →
      (P.toMeasure[D.indicator (fun _ => (1 : ℝ)) | G s]) =ᵐ[P.toMeasure]
      (P.toMeasure[D.indicator (fun _ => (1 : ℝ)) | G T])
  X_adapted : ∀ s, s ≤ T → Measurable[F s] (fun ω => pathAt (X ω) s)
  W_adapted : ∀ s, s ≤ T → Measurable[F s] (fun ω => pathAt (W ω) s)
  B_adapted : ∀ s, s ≤ T → Measurable[F s] (fun ω => pathAt (B ω) s)
  B_G_adapted : ∀ s, s ≤ T → Measurable[G s] (fun ω => pathAt (B ω) s - pathAt (B ω) t)
  W_brownian : IsFBrownianOn F P.toMeasure t T (fun s ω => pathAt (W ω) s)
  B_brownian : IsFBrownianOn F P.toMeasure t T (fun s ω => pathAt (B ω) s)
  W_B_independent : Indep
    (MeasurableSpace.comap (shiftedPath t ∘ W) inferInstance)
    (MeasurableSpace.comap (shiftedPath t ∘ B) inferInstance) P.toMeasure
  initial_common_independent : Indep
    (F t ⊔ MeasurableSpace.comap W inferInstance) (G T) P.toMeasure
  energy :
    (∫⁻ ω, ENNReal.ofReal (‖X ω‖ ^ 2) ∂P.toMeasure) +
      (∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) (T : ℝ),
        edist (α s.toNNReal ω) M.u₀ ^ (2 : ℝ) ∂volume ∂P.toMeasure) < ⊤
  μ_conditional : ∀ᵐ s ∂volume.restrict (Set.Icc (t : ℝ) (T : ℝ)),
    ∃ m : Ω → ProbabilityMeasure (Cpath T n),
      @IsCondLaw Ω (Cpath T n) mΩ (inferInstance) (G s.toNNReal) P.toMeasure
        (fun ω => stopPath s.toNNReal (X ω)) m ∧
      μ s.toNNReal =ᵐ[P.toMeasure] m
  μbar_conditional : ∀ᵐ s ∂volume.restrict (Set.Icc (t : ℝ) (T : ℝ)),
    ∃ m : Ω → ProbabilityMeasure (Cpath T n × U),
      @IsCondLaw Ω (Cpath T n × U) mΩ (inferInstance) (G s.toNNReal) P.toMeasure
        (fun ω => (stopPath s.toNNReal (X ω), α s.toNNReal ω)) m ∧
      μbar s.toNNReal =ᵐ[P.toMeasure] m
  initial_law : Measure.map (stopPath t ∘ X) P.toMeasure =
    Measure.map (stopPath t) (ν : Measure (Cpath T n))
  A_formula : ∀ s, s ≤ T → ∀ᵐ ω ∂P.toMeasure,
    scalarAt (A ω) s = ∫ r in (t : ℝ)..(max s t : ℝ), M.π (α r.toNNReal ω)
  μhat_before : ∀ s, s ≤ t → s ≤ T → ∀ᵐ ω ∂P.toMeasure,
    ((μhat ω) ⟨min (s : ℝ) (T : ℝ), ⟨le_min s.property T.property, min_le_right _ _⟩⟩ : Measure (OmegaHat T n d ell)) =
      Measure.map (hatStopped s ∘ fun ω => (X ω, A ω, W ω, B ω)) P.toMeasure
  μhat_after : ∀ s, t < s → s ≤ T →
    ∃ m : Ω → ProbabilityMeasure (OmegaHat T n d ell),
      @IsCondLaw Ω (OmegaHat T n d ell) mΩ (inferInstance) (G s) P.toMeasure
        (hatStopped s ∘ fun ω => (X ω, A ω, W ω, B ω)) m ∧
      (fun ω => (μhat ω) ⟨min (s : ℝ) (T : ℝ), ⟨le_min s.property T.property, min_le_right _ _⟩⟩) =ᵐ[P.toMeasure] m
  sde : SDEEquation M t P.toMeasure F X W B α μbar

/-- The canonical conditional state law μ̂_s ◦ X̂_{s∧·}^{-1}. -/
noncomputable def WeakControl.muAt {M : Model T n d ell U} {Ω : Type}
    [MeasurableSpace Ω] {t : ℝ≥0} {ν : ProbabilityMeasure (Cpath T n)}
    (γ : WeakControl M Ω t ν) (s : ℝ≥0) (ω : Ω) :
    ProbabilityMeasure (Cpath T n) :=
  ((γ.μhat ω) ⟨min (s : ℝ) (T : ℝ),
    ⟨le_min s.property T.property, min_le_right _ _⟩⟩).map
      ((measurable_stopPath s).comp measurable_fst |>.aemeasurable)

/-- Reward (2.5) for a weak control. -/
noncomputable def Jweak {M : Model T n d ell U} {Ω : Type}
    [MeasurableSpace Ω] {t : ℝ≥0} {ν : ProbabilityMeasure (Cpath T n)}
    (γ : WeakControl M Ω t ν) : EReal :=
  eExp γ.P.toMeasure (fun ω =>
    timeInt t T (fun s => (M.L s (stopPath s (γ.X ω)) (γ.μbar s ω) (γ.α s ω) : EReal)) +
      (M.g (γ.X ω) (γ.muAt T ω) : EReal))

/-- The raw common-noise filtration of Definition 2.6. -/
noncomputable def WeakControl.rawG {M : Model T n d ell U} {Ω : Type}
    [MeasurableSpace Ω] {t : ℝ≥0} {ν : ProbabilityMeasure (Cpath T n)}
    (γ : WeakControl M Ω t ν) (s : ℝ≥0) : MeasurableSpace Ω :=
  if s < t then ⊥ else
    ⨆ r : ℝ≥0, ⨆ _ : t ≤ r ∧ r ≤ s,
      MeasurableSpace.comap (fun ω => pathAt (γ.B ω) r - pathAt (γ.B ω) t) inferInstance

/-- The raw full filtration of Definition 2.6. -/
noncomputable def WeakControl.rawF {M : Model T n d ell U} {Ω : Type}
    [MeasurableSpace Ω] {t : ℝ≥0} {ν : ProbabilityMeasure (Cpath T n)}
    (γ : WeakControl M Ω t ν) (s : ℝ≥0) : MeasurableSpace Ω :=
  if s < t then MeasurableSpace.comap (stopPath s ∘ γ.X) inferInstance else
    MeasurableSpace.comap (stopPath t ∘ γ.X) inferInstance ⊔
    (⨆ r : ℝ≥0, ⨆ _ : t ≤ r ∧ r ≤ s,
      MeasurableSpace.comap
        (fun ω => (pathAt (γ.W ω) r - pathAt (γ.W ω) t,
          pathAt (γ.B ω) r - pathAt (γ.B ω) t)) inferInstance)

/-- Augmentation of a σ-algebra by all ambient null subsets. -/
def augmented {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : MeasurableSpace Ω) : MeasurableSpace Ω :=
  H ⊔ MeasurableSpace.generateFrom
    {A | ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ A ⊆ N}

/-- Definition 2.6: a weak control whose filtrations are P-augmentations
of the raw ones. -/
def IsStrong {M : Model T n d ell U} {Ω : Type}
    [MeasurableSpace Ω] {t : ℝ≥0} {ν : ProbabilityMeasure (Cpath T n)}
    (γ : WeakControl M Ω t ν) : Prop :=
  (∀ s, γ.F s = augmented γ.P.toMeasure (γ.rawF s)) ∧
  (∀ s, γ.G s = augmented γ.P.toMeasure (γ.rawG s))

/-- A B-strong control also uses a common-noise-predictable control. -/
def IsBStrong {M : Model T n d ell U} {Ω : Type}
    [MeasurableSpace Ω] {t : ℝ≥0} {ν : ProbabilityMeasure (Cpath T n)}
    (γ : WeakControl M Ω t ν) : Prop :=
  IsStrong γ ∧ Measurable[γ.G.predictable] (fun z : ℝ≥0 × Ω => γ.α z.1 z.2)

/-- The strong formulation (2.9), with arbitrary sample spaces in universe zero. -/
noncomputable def VSBWeak (M : Model T n d ell U) (t : ℝ≥0)
    (ν : ProbabilityMeasure (Cpath T n)) : EReal :=
  ⨆ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ⨆ (γ : WeakControl M Ω t ν), ⨆ (_ : IsBStrong γ), Jweak γ

end MKVDPP.BStrong


