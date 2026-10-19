-- Prove2me | Definitions.Def_MKVLimit_Value_Setting
-- name    : MKVLimit_Value_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:11.353793+00:00
-- url     : https://prove2.me/theorems/f315f75f-b94c-4137-bb16-1d2d5a37f2ac
-- title:
--   Path spaces, Wasserstein laws, conditional laws, and Assumptions 2.1 and 2.12
-- statement:
--   Let $C^k=C([0,T],\mathbb R^k)$ with its uniform norm, and let $A$ be the Polish control space with base point $a_0$. The definitions give stopped paths and stopped laws, finite $p$th moments, and the Wasserstein distance
--
--   $$\mathcal W_p(\mu,\nu)=\left(\inf_{\lambda\in\Pi(\mu,\nu)}\int\rho(x,y)^p\,d\lambda(x,y)\right)^{1/p}. $$
--
--   The coefficient data $(b,\sigma,\sigma_0,L,g)$ carry Assumption 2.1's measurable, nonanticipative, continuous, Lipschitz, growth, coercive and lower semicontinuous conditions. Assumption 2.12 says $b,\sigma,L$ depend on a joint state-control law only through its state marginal, and $\sigma_0$ does not depend on the control. The interface also defines conditional laws, the Brownian property relative to a filtration, and the expectation convention $\infty-\infty=-\infty$.
--
--   These definitions are the common model for the strong and particle control values.
--
--   **Formalization Note** Time is nonnegative real, paths are continuous maps on $[0,T]$, matrices use the Frobenius norm, and $\mathcal W_p$ is extended nonnegative. The paper leaves the measure topology unnamed; continuity is read sequentially on finite-moment laws in $\mathcal W_p$. The Euclidean-control hypothesis means an isometric embedding into $\mathbb R^j$. The displayed chain $0\le\hat p\le2$ permits $\hat p=0$.
-- source:
--   Djete, Possamaï & Tan, McKean–Vlasov optimal control: limit theory and equivalence between different formulations, arXiv:2001.00925v2, pp. 3–4, 8, Notations (i), (iii), Assumptions 2.1 and 2.12

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_completedSDEPast

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVLimit.Value

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)
abbrev Cpath (T : ℝ≥0) (k : ℕ) := C(Set.Icc (0 : ℝ) (T : ℝ), Rn k)
instance (T : ℝ≥0) (k : ℕ) : MeasurableSpace (Cpath T k) := borel _
instance (T : ℝ≥0) (k : ℕ) : BorelSpace (Cpath T k) := ⟨rfl⟩
instance (n d : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin d) ℝ) := borel _

noncomputable def stopTimeMap {T : ℝ≥0} (t : ℝ≥0) :
    C(Set.Icc (0 : ℝ) (T : ℝ), Set.Icc (0 : ℝ) (T : ℝ)) :=
  ⟨fun s => ⟨min (s : ℝ) (t : ℝ),
    ⟨le_min s.property.1 t.property, (min_le_left (s : ℝ) (t : ℝ)).trans s.property.2⟩⟩,
    by fun_prop⟩
noncomputable def stopPath {T : ℝ≥0} {k : ℕ} (t : ℝ≥0) (x : Cpath T k) : Cpath T k :=
  x.comp (stopTimeMap t)
theorem measurable_stopPath {T : ℝ≥0} {k : ℕ} (t : ℝ≥0) :
    Measurable (stopPath (T := T) (k := k) t) :=
  (ContinuousMap.continuous_precomp (stopTimeMap t)).measurable
noncomputable def pathAt {T : ℝ≥0} {k : ℕ} (x : Cpath T k) (s : ℝ≥0) : Rn k :=
  x ⟨min (s : ℝ) (T : ℝ), ⟨le_min s.property T.property, min_le_right _ _⟩⟩
noncomputable def stopLaw {T : ℝ≥0} {n : ℕ} {U : Type*} [MeasurableSpace U]
    (t : ℝ≥0) (μ : ProbabilityMeasure (Cpath T n × U)) :
    ProbabilityMeasure (Cpath T n × U) :=
  μ.map ((Measurable.prodMk (measurable_stopPath t |>.comp measurable_fst)
    measurable_snd).aemeasurable)

def HasMoment {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E]
    (p : ℝ) (μ : ProbabilityMeasure E) : Prop :=
  ∃ e₀ : E, ∫⁻ e, edist e e₀ ^ p ∂(μ : Measure E) < ⊤

def IsCoupling {E : Type*} [MeasurableSpace E] (μ ν : ProbabilityMeasure E)
    (κ : ProbabilityMeasure (E × E)) : Prop :=
  Measure.map Prod.fst (κ : Measure (E × E)) = (μ : Measure E) ∧
  Measure.map Prod.snd (κ : Measure (E × E)) = (ν : Measure E)
noncomputable def Wp {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E]
    (p : ℝ) (μ ν : ProbabilityMeasure E) : ℝ≥0∞ :=
  (⨅ κ : ProbabilityMeasure (E × E), ⨅ _ : IsCoupling μ ν κ,
    ∫⁻ z, edist z.1 z.2 ^ p ∂(κ : Measure (E × E))) ^ (1 / p)

def IsCondLaw {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (G : MeasurableSpace Ω) (P : @Measure Ω mΩ) (ξ : Ω → E)
    (m : Ω → @ProbabilityMeasure E mE) : Prop :=
  Measurable ξ ∧ Measurable[G] m ∧ ∀ A : Set E, MeasurableSet A →
    (fun ω => ((m ω : Measure E) A).toReal) =ᵐ[P]
      (P[A.indicator (fun _ => (1 : ℝ)) ∘ ξ | G])

noncomputable def eExp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → EReal) : EReal :=
  ((∫⁻ ω, (ξ ω).toENNReal ∂P : ℝ≥0∞) : EReal) -
  ((∫⁻ ω, (-ξ ω).toENNReal ∂P : ℝ≥0∞) : EReal)
noncomputable def timeInt (a b : ℝ≥0) (f : ℝ≥0 → EReal) : EReal :=
  ((∫⁻ s in Set.Icc (a : ℝ) (b : ℝ), (f s.toNNReal).toENNReal ∂volume : ℝ≥0∞) : EReal) -
  ((∫⁻ s in Set.Icc (a : ℝ) (b : ℝ), (-f s.toNNReal).toENNReal ∂volume : ℝ≥0∞) : EReal)
noncomputable def frobenius {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)
noncomputable def tripleNorm {n d ℓ : ℕ} (v : Rn n)
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin ℓ) ℝ) : ℝ :=
  Real.sqrt (‖v‖ ^ 2 + frobenius A ^ 2 + frobenius B ^ 2)
noncomputable def pairNorm {n d ℓ : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin ℓ) ℝ) : ℝ :=
  Real.sqrt (frobenius A ^ 2 + frobenius B ^ 2)

structure Model (T : ℝ≥0) (n d ℓ : ℕ) (U : Type*)
    [MetricSpace U] [MeasurableSpace U] where
  a₀ : U
  b : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U → Rn n
  σ : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U → Matrix (Fin n) (Fin d) ℝ
  σ₀ : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U → Matrix (Fin n) (Fin ℓ) ℝ
  L : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U → ℝ
  g : Cpath T n → ProbabilityMeasure (Cpath T n) → ℝ

/-- Borel measurability on the paper's time domain [0,T]. -/
def TimeMeasurable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (T : ℝ≥0) (f : ℝ≥0 × A → B) : Prop :=
  Measurable (fun z : {z : ℝ≥0 × A // z.1 ≤ T} => f z.1)

noncomputable def momentJoint {T : ℝ≥0} {n : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] (a₀ : U)
    (μ : ProbabilityMeasure (Cpath T n × U)) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖z.1‖ ^ p + dist a₀ z.2 ^ p) ∂(μ : Measure (Cpath T n × U))
noncomputable def momentPath {T : ℝ≥0} {n : ℕ}
    (μ : ProbabilityMeasure (Cpath T n)) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖x‖ ^ p) ∂(μ : Measure (Cpath T n))

/-- Sequential continuity in path, Wasserstein measure, and control arguments. -/
def SeqContinuous4 {T : ℝ≥0} {n : ℕ} {U V : Type*}
    [MetricSpace U] [MeasurableSpace U] [TopologicalSpace V]
    (p : ℝ) (f : Cpath T n → ProbabilityMeasure (Cpath T n × U) → U → V) : Prop :=
  ∀ (x : ℕ → Cpath T n) (μ : ℕ → ProbabilityMeasure (Cpath T n × U))
    (a : ℕ → U) (x₀ : Cpath T n) (μ₀ : ProbabilityMeasure (Cpath T n × U)) (a₀ : U),
    (∀ k, HasMoment p (μ k)) → HasMoment p μ₀ →
    Tendsto x atTop (𝓝 x₀) → Tendsto (fun k => Wp p (μ k) μ₀) atTop (𝓝 0) →
    Tendsto a atTop (𝓝 a₀) →
    Tendsto (fun k => f (x k) (μ k) (a k)) atTop (𝓝 (f x₀ μ₀ a₀))

def SeqLsc4 {T : ℝ≥0} {n : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U]
    (p : ℝ) (f : Cpath T n → ProbabilityMeasure (Cpath T n × U) → U → ℝ) : Prop :=
  ∀ (x : ℕ → Cpath T n) (μ : ℕ → ProbabilityMeasure (Cpath T n × U))
    (a : ℕ → U) (x₀ : Cpath T n) (μ₀ : ProbabilityMeasure (Cpath T n × U)) (a₀ : U),
    (∀ k, HasMoment p (μ k)) → HasMoment p μ₀ →
    Tendsto x atTop (𝓝 x₀) → Tendsto (fun k => Wp p (μ k) μ₀) atTop (𝓝 0) →
    Tendsto a atTop (𝓝 a₀) →
    (f x₀ μ₀ a₀ : EReal) ≤ liminf (fun k => (f (x k) (μ k) (a k) : EReal)) atTop

def SeqLscG {T : ℝ≥0} {n : ℕ}
    (p : ℝ) (f : Cpath T n → ProbabilityMeasure (Cpath T n) → ℝ) : Prop :=
  ∀ (x : ℕ → Cpath T n) (μ : ℕ → ProbabilityMeasure (Cpath T n))
    (x₀ : Cpath T n) (μ₀ : ProbabilityMeasure (Cpath T n)),
    (∀ k, HasMoment p (μ k)) → HasMoment p μ₀ →
    Tendsto x atTop (𝓝 x₀) → Tendsto (fun k => Wp p (μ k) μ₀) atTop (𝓝 0) →
    (f x₀ μ₀ : EReal) ≤ liminf (fun k => (f (x k) (μ k) : EReal)) atTop

/-- Assumption 2.1, including the paper's standing measurability, nonanticipativity,
continuity, Lipschitz, growth and lower semicontinuity clauses. -/
def Assumption21 {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] (M : Model T n d ℓ U) (p p' : ℝ) : Prop :=
  2 ≤ p ∧ p < p' ∧ ∃ C : ℝ, ∃ C_L : ℝ, ∃ phat : ℝ,
    0 < C ∧ 0 < C_L ∧ 0 ≤ phat ∧ phat ≤ 2 ∧
    TimeMeasurable T (fun z : ℝ≥0 × Cpath T n × ProbabilityMeasure (Cpath T n × U) × U =>
      M.b z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
    TimeMeasurable T (fun z : ℝ≥0 × Cpath T n × ProbabilityMeasure (Cpath T n × U) × U =>
      M.σ z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
    TimeMeasurable T (fun z : ℝ≥0 × Cpath T n × ProbabilityMeasure (Cpath T n × U) × U =>
      M.σ₀ z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
    TimeMeasurable T (fun z : ℝ≥0 × Cpath T n × ProbabilityMeasure (Cpath T n × U) × U =>
      M.L z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
    Measurable (fun z : Cpath T n × ProbabilityMeasure (Cpath T n) => M.g z.1 z.2) ∧
    (∀ t x μ a, t ≤ T →
      M.b t x μ a = M.b t (stopPath t x) (stopLaw t μ) a ∧
      M.σ t x μ a = M.σ t (stopPath t x) (stopLaw t μ) a ∧
      M.σ₀ t x μ a = M.σ₀ t (stopPath t x) (stopLaw t μ) a ∧
      M.L t x μ a = M.L t (stopPath t x) (stopLaw t μ) a) ∧
    (∀ t, t ≤ T → SeqContinuous4 p (M.b t) ∧
      SeqContinuous4 p (M.σ t) ∧ SeqContinuous4 p (M.σ₀ t)) ∧
    (∀ t x x' μ μ' a, t ≤ T →
      (tripleNorm (M.b t x μ a - M.b t x' μ' a)
        (M.σ t x μ a - M.σ t x' μ' a)
        (M.σ₀ t x μ a - M.σ₀ t x' μ' a) : EReal) ≤
      (C : EReal) * ((‖x - x'‖ : EReal) + ((Wp p μ μ' : ℝ≥0∞) : EReal))) ∧
    (∀ t x μ a, t ≤ T →
      (‖M.b t x μ a‖ : EReal) ≤
        (C : EReal) * (1 + (‖x‖ : EReal) + ((momentJoint M.a₀ μ p ^ (1 / p) : ℝ≥0∞) : EReal) + (dist M.a₀ a : EReal)) ∧
      (pairNorm (M.σ t x μ a) (M.σ₀ t x μ a) ^ 2 : EReal) ≤
        (C : EReal) * (1 + ((‖x‖ ^ phat : ℝ) : EReal) +
          ((momentJoint M.a₀ μ p ^ (phat / p) : ℝ≥0∞) : EReal) + ((dist M.a₀ a ^ phat : ℝ) : EReal))) ∧
    SeqLscG p M.g ∧ (∀ t, t ≤ T → SeqLsc4 p (M.L t)) ∧
    (∀ x μ, ((|M.g x μ| : ℝ) : EReal) ≤
      (C : EReal) * (1 + ((‖x‖ ^ p : ℝ) : EReal) + ((momentPath μ p : ℝ≥0∞) : EReal))) ∧
    (∀ t x μ a, t ≤ T →
      (M.L t x μ a : EReal) ≤
        (C : EReal) * (1 + ((‖x‖ ^ p : ℝ) : EReal) + ((momentJoint M.a₀ μ p : ℝ≥0∞) : EReal)) -
          ((C_L * dist M.a₀ a ^ p' : ℝ) : EReal) ∧
      -(C : EReal) * (1 + ((‖x‖ ^ p : ℝ) : EReal) + ((momentJoint M.a₀ μ p : ℝ≥0∞) : EReal)) ≤
        (M.L t x μ a : EReal))

/-- Assumption 2.12: coefficients factor through the state marginal. -/
def Assumption212 {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] (M : Model T n d ℓ U) : Prop :=
  ∃ bFac : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n) → U → Rn n,
    ∃ sigFac : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n) → U → Matrix (Fin n) (Fin d) ℝ,
    ∃ LFac : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n) → U → ℝ,
    ∃ sig0Fac : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n) → Matrix (Fin n) (Fin ℓ) ℝ,
    TimeMeasurable T (fun z : ℝ≥0 × Cpath T n × ProbabilityMeasure (Cpath T n) × U => bFac z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
    TimeMeasurable T (fun z : ℝ≥0 × Cpath T n × ProbabilityMeasure (Cpath T n) × U => sigFac z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
    TimeMeasurable T (fun z : ℝ≥0 × Cpath T n × ProbabilityMeasure (Cpath T n) × U => LFac z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
    TimeMeasurable T (fun z : ℝ≥0 × Cpath T n × ProbabilityMeasure (Cpath T n) => sig0Fac z.1 z.2.1 z.2.2) ∧
    ∀ t x μ a, t ≤ T → M.b t x μ a = bFac t x (μ.map measurable_fst.aemeasurable) a ∧
      M.σ t x μ a = sigFac t x (μ.map measurable_fst.aemeasurable) a ∧
      M.L t x μ a = LFac t x (μ.map measurable_fst.aemeasurable) a ∧
      M.σ₀ t x μ a = sig0Fac t x (μ.map measurable_fst.aemeasurable)

def AEmbedsEuclid (U : Type*) [MetricSpace U] : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ ∃ ι : U → Rn j, Isometry ι

/-- Sequential Wp-continuity of L and g in every argument on their moment domains. -/
def IsContinuousLg {T : ℝ≥0} {n d ℓ : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] (M : Model T n d ℓ U) (p : ℝ) : Prop :=
  (∀ (t : ℕ → ℝ≥0) (x : ℕ → Cpath T n)
      (μ : ℕ → ProbabilityMeasure (Cpath T n × U)) (a : ℕ → U)
      (t₀ : ℝ≥0) (x₀ : Cpath T n) (μ₀ : ProbabilityMeasure (Cpath T n × U)) (a₀ : U),
      (∀ k, t k ≤ T) → t₀ ≤ T → (∀ k, HasMoment p (μ k)) → HasMoment p μ₀ →
      Tendsto t atTop (𝓝 t₀) → Tendsto x atTop (𝓝 x₀) →
      Tendsto (fun k => Wp p (μ k) μ₀) atTop (𝓝 0) → Tendsto a atTop (𝓝 a₀) →
      Tendsto (fun k => M.L (t k) (x k) (μ k) (a k)) atTop (𝓝 (M.L t₀ x₀ μ₀ a₀))) ∧
  (∀ (x : ℕ → Cpath T n) (μ : ℕ → ProbabilityMeasure (Cpath T n))
      (x₀ : Cpath T n) (μ₀ : ProbabilityMeasure (Cpath T n)),
      (∀ k, HasMoment p (μ k)) → HasMoment p μ₀ →
      Tendsto x atTop (𝓝 x₀) → Tendsto (fun k => Wp p (μ k) μ₀) atTop (𝓝 0) →
      Tendsto (fun k => M.g (x k) (μ k)) atTop (𝓝 (M.g x₀ μ₀)))

/-- A Brownian motion relative to the full past filtration, with Gaussian vector increments. -/
def IsFBrownian {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω)
    (T : ℝ≥0) (W : ℝ≥0 → Ω → Rn k) : Prop :=
  (∀ ω, ContinuousOn (fun s => W s ω) (Set.Icc 0 T)) ∧
  (∀ᵐ ω ∂P, W 0 ω = 0) ∧
  (∀ s, s ≤ T → Measurable[F s] (W s)) ∧
  ∀ s u, s ≤ u → u ≤ T →
    Indep (MeasurableSpace.comap (fun ω => W u ω - W s ω) inferInstance) (F s) P ∧
    Measure.map (fun ω => W u ω - W s ω) P =
      (Measure.pi (fun _ : Fin k => gaussianReal 0 ⟨(u - s : ℝ≥0), by positivity⟩)).map
        (fun v : Fin k → ℝ => (WithLp.toLp 2 v : Rn k))

end MKVLimit.Value


