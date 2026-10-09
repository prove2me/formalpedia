-- Prove2me | Definitions.Def_MKVDPP_BStrong_Setting
-- name    : MKVDPP_BStrong_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T13:22:48.008127+00:00
-- url     : https://prove2.me/theorems/d6441ff4-dda3-405f-9f77-faa7b43a2865
-- title:
--   Paths, laws, conditional laws and Assumption 2.8
-- statement:
--   State and noise paths are continuous Euclidean valued paths on $[0,T]$, with the uniform norm. The notation $\mathcal P_2(E)$ means probability laws with a finite second moment; $W_2$ is the quadratic transport distance obtained by minimizing over couplings. A stopped path is constant after its stopping time.
--
--   The model has Borel measurable, nonanticipative coefficients $b,\sigma,\sigma_0$, rewards $L,g$, a Polish control space $U$, and an embedding $\pi:U\to[0,1]$. Assumption 2.8 requires one constant $C>0$ for both the Lipschitz and growth bounds, including
--
--   $$\|(b,\sigma,\sigma_0)(t,x,\bar\nu,u)-(b,\sigma,\sigma_0)(t,x',\bar\nu',u)\|\le C(\|x-x'\|+W_2(\bar\nu,\bar\nu')).$$
--
--   Conditional laws, regular conditional probabilities, filtration relative Brownian motion and the paper's expectation convention also belong to this interface. They support both the intrinsic and fixed space control formulations.
--
--   **Formalization Note** Time uses nonnegative real numbers. Product spaces use Mathlib's product metric. Matrix norms are Frobenius. The local Itô integral requires pathwise quadratic energy and almost sure integrable drift; $\infty-\infty=-\infty$.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, pp. 4–8, Notations (i)–(v), §2 preamble, Definition 2.1(iv), Assumption 2.8

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_completedSDEPast

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

/-- The path space C([0,T],ℝᵏ), with the uniform norm. -/
abbrev Cpath (T : ℝ≥0) (k : ℕ) :=
  C(Set.Icc (0 : ℝ) (T : ℝ), EuclideanSpace ℝ (Fin k))

/-- The scalar path space used for the integrated control. -/
abbrev CR (T : ℝ≥0) := C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)

instance (T : ℝ≥0) (k : ℕ) : MeasurableSpace (Cpath T k) := borel _
instance (T : ℝ≥0) (k : ℕ) : BorelSpace (Cpath T k) := ⟨rfl⟩
instance (T : ℝ≥0) : MeasurableSpace (CR T) := borel _
instance (T : ℝ≥0) : BorelSpace (CR T) := ⟨rfl⟩

/-- The continuous time clamp s ↦ s ∧ t. -/
noncomputable def stopTimeMap {T : ℝ≥0} (t : ℝ≥0) :
    C(Set.Icc (0 : ℝ) (T : ℝ), Set.Icc (0 : ℝ) (T : ℝ)) :=
  ⟨(fun s : Set.Icc (0 : ℝ) (T : ℝ) =>
    (⟨min (s : ℝ) (t : ℝ),
      ⟨le_min s.property.1 t.property,
        (min_le_left (s : ℝ) (t : ℝ)).trans s.property.2⟩⟩ :
      Set.Icc (0 : ℝ) (T : ℝ))), by fun_prop⟩

/-- The path stopped at t, extended constantly to T. -/
noncomputable def stopPath {T : ℝ≥0} {k : ℕ} (t : ℝ≥0) (x : Cpath T k) : Cpath T k :=
  x.comp (stopTimeMap t)

theorem measurable_stopPath {T : ℝ≥0} {k : ℕ} (t : ℝ≥0) :
    Measurable (stopPath (T := T) (k := k) t) :=
  (ContinuousMap.continuous_precomp (stopTimeMap t)).measurable

/-- The canonical four-coordinate path space of Section 4.1. -/
abbrev OmegaHat (T : ℝ≥0) (n d ell : ℕ) :=
  Cpath T n × CR T × Cpath T d × Cpath T ell

noncomputable instance (T : ℝ≥0) (n d ell : ℕ) :
    MeasurableSpace (C(Set.Icc (0 : ℝ) (T : ℝ),
      ProbabilityMeasure (OmegaHat T n d ell))) := borel _
instance (T : ℝ≥0) (n d ell : ℕ) :
    BorelSpace (C(Set.Icc (0 : ℝ) (T : ℝ),
      ProbabilityMeasure (OmegaHat T n d ell))) := ⟨rfl⟩

/-- Evaluation of a path at a time clamped to [0,T]. -/
noncomputable def pathAt {T : ℝ≥0} {k : ℕ} (x : Cpath T k) (s : ℝ≥0) :
    EuclideanSpace ℝ (Fin k) :=
  x ⟨min (s : ℝ) (T : ℝ), ⟨le_min s.property T.property, min_le_right _ _⟩⟩

/-- The Brownian path shifted to start at zero at time t. -/
noncomputable def shiftedPath {T : ℝ≥0} {k : ℕ} (t : ℝ≥0)
    (x : Cpath T k) : Cpath T k :=
  ⟨(fun s : Set.Icc (0 : ℝ) (T : ℝ) =>
    x ⟨max (min (s : ℝ) (T : ℝ)) (min (t : ℝ) (T : ℝ)),
      ⟨le_max_of_le_left (le_min s.property.1 T.property),
        max_le (min_le_right _ _) (min_le_right _ _)⟩⟩ - pathAt x t), by fun_prop⟩

/-- Scalar path evaluation. -/
noncomputable def scalarAt {T : ℝ≥0} (x : CR T) (s : ℝ≥0) : ℝ :=
  x ⟨min (s : ℝ) (T : ℝ), ⟨le_min s.property T.property, min_le_right _ _⟩⟩

/-- Probability measures having a finite kth moment about a base point. -/
def IsPMoment {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E]
    (k : ℝ) (μ : ProbabilityMeasure E) (e₀ : E) : Prop :=
  ∫⁻ e, edist e e₀ ^ k ∂(μ : Measure E) < ⊤

def IsP2 {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E]
    (μ : ProbabilityMeasure E) : Prop := ∃ e₀, IsPMoment 2 μ e₀

/-- A probability coupling of two laws. -/
def IsCoupling {E : Type*} [MeasurableSpace E] (μ ν : ProbabilityMeasure E)
    (κ : ProbabilityMeasure (E × E)) : Prop :=
  Measure.map Prod.fst (κ : Measure (E × E)) = (μ : Measure E) ∧
  Measure.map Prod.snd (κ : Measure (E × E)) = (ν : Measure E)

/-- Quadratic Wasserstein distance, including its possibly infinite value. -/
noncomputable def W2 {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E]
    (μ ν : ProbabilityMeasure E) : ℝ≥0∞ :=
  (⨅ κ : ProbabilityMeasure (E × E), ⨅ _ : IsCoupling μ ν κ,
    ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(κ : Measure (E × E))) ^ (1 / 2 : ℝ)

/-- The paper's expectation convention: ∞ − ∞ = −∞. -/
noncomputable def eExp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → EReal) : EReal :=
  ((∫⁻ ω, (ξ ω).toENNReal ∂P : ℝ≥0∞) : EReal) -
  ((∫⁻ ω, (-ξ ω).toENNReal ∂P : ℝ≥0∞) : EReal)

/-- The paper's signed Lebesgue integral, with ∞ − ∞ = −∞. -/
noncomputable def timeInt (a b : ℝ≥0) (f : ℝ≥0 → EReal) : EReal :=
  ((∫⁻ s in Set.Icc (a : ℝ) (b : ℝ), (f s.toNNReal).toENNReal ∂volume : ℝ≥0∞) : EReal) -
  ((∫⁻ s in Set.Icc (a : ℝ) (b : ℝ), (-f s.toNNReal).toENNReal ∂volume : ℝ≥0∞) : EReal)

/-- The paper's upper semi-analyticity condition. -/
def IsUpperSemianalytic {E : Type*} [TopologicalSpace E] (f : E → EReal) : Prop :=
  ∀ c : ℝ, AnalyticSet {x | (c : EReal) < f x}

/-- A regular conditional law, stated by its defining conditional-expectation property. -/
def IsCondLaw {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (G : MeasurableSpace Ω) (P : @Measure Ω mΩ) (ξ : Ω → E)
    (m : Ω → @ProbabilityMeasure E mE) : Prop :=
  Measurable ξ ∧ Measurable[G] m ∧ ∀ A : Set E, MeasurableSet A →
    (fun ω => ((m ω : Measure E) A).toReal) =ᵐ[P]
      (P[A.indicator (fun _ => (1 : ℝ)) ∘ ξ | G])

/-- An r.c.p.d. with the pointwise atom condition of Notations (iii). -/
def IsRCPD {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (G : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    (κ : Ω → @ProbabilityMeasure Ω mΩ) : Prop :=
  G ≤ mΩ ∧
  (∃ C : Set (Set Ω), C.Countable ∧ G = MeasurableSpace.generateFrom C) ∧
  Measurable[G] κ ∧
  (∀ A B : Set Ω, MeasurableSet[mΩ] A → MeasurableSet[G] B →
    P (A ∩ B) = ∫⁻ ω in B, (@ProbabilityMeasure.toMeasure Ω mΩ (κ ω)) A ∂P) ∧
  ∀ ω, (@ProbabilityMeasure.toMeasure Ω mΩ (κ ω))
    (⋂₀ {A : Set Ω | MeasurableSet[G] A ∧ ω ∈ A}) = 1

/-- The Frobenius norm of a real matrix. -/
noncomputable def frobenius {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

noncomputable def tripleNorm {n d ell : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin n) (Fin d) ℝ)
    (B : Matrix (Fin n) (Fin ell) ℝ) : ℝ :=
  Real.sqrt (‖v‖ ^ 2 + frobenius A ^ 2 + frobenius B ^ 2)

/-- Assumption 2.8, with its exponent fixed at two. The triple norm is the Euclidean
product norm of drift and the two diffusion matrices. -/
def Assumption28 {U : Type*} [MeasurableSpace U] [MetricSpace U]
    (T : ℝ≥0) (n d ell : ℕ) (u₀ : U)
    (b : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U →
      EuclideanSpace ℝ (Fin n))
    (σ : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U →
      Matrix (Fin n) (Fin d) ℝ)
    (σ₀ : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U →
      Matrix (Fin n) (Fin ell) ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∀ t x x' μ μ' u, t ≤ T → IsP2 μ → IsP2 μ' →
      tripleNorm (b t x μ u - b t x' μ' u)
        (σ t x μ u - σ t x' μ' u)
        (σ₀ t x μ u - σ₀ t x' μ' u) ≤
        C * (‖x - x'‖ + (W2 μ μ').toReal)) ∧
    (∀ t x μ u, t ≤ T → IsP2 μ →
      tripleNorm (b t x μ u) (σ t x μ u) (σ₀ t x μ u) ^ 2 ≤
        C * (1 + ‖x‖ ^ 2 +
          (∫⁻ z, (edist z.1 (0 : Cpath T n) ^ (2 : ℝ) +
            edist z.2 u₀ ^ (2 : ℝ)) ∂(μ : Measure (Cpath T n × U))).toReal +
          dist u u₀ ^ 2))

/-- A standard k-dimensional Brownian motion on [t,T] relative to F and P. -/
def IsFBrownianOn {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω)
    (t T : ℝ≥0) (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin k)) : Prop :=
  (∀ ω, ContinuousOn (fun s : ℝ≥0 => W s ω) (Set.Icc 0 T)) ∧
  (∀ s, t ≤ s → s ≤ T → Measurable[F s] (fun ω => W s ω - W t ω)) ∧
  ∀ s u, t ≤ s → s ≤ u → u ≤ T →
    Indep (MeasurableSpace.comap (fun ω => W u ω - W s ω) inferInstance) (F s) P ∧
    Measure.map (fun ω => W u ω - W s ω) P =
      (Measure.pi (fun _ : Fin k => gaussianReal 0 ⟨(u - s : ℝ≥0), by positivity⟩)).map
        (fun v : Fin k → ℝ => (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin k)))

instance (n d : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin d) ℝ) := borel _

noncomputable def stopLaw {T : ℝ≥0} {n : ℕ} {U : Type*} [MeasurableSpace U]
    (t : ℝ≥0) (μ : ProbabilityMeasure (Cpath T n × U)) :
    ProbabilityMeasure (Cpath T n × U) :=
  μ.map ((Measurable.prodMk (measurable_stopPath t |>.comp measurable_fst)
    measurable_snd).aemeasurable)

/-- The jointly measurable, nonanticipative coefficients fixed in Section 2. -/
structure Model (T : ℝ≥0) (n d ell : ℕ) (U : Type*)
    [MetricSpace U] [MeasurableSpace U] where
  u₀ : U
  π : U → ℝ
  π_measurableEmbedding : MeasurableEmbedding π
  π_range : ∀ u, π u ∈ Set.Icc (0 : ℝ) 1
  b : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U →
    EuclideanSpace ℝ (Fin n)
  σ : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U →
    Matrix (Fin n) (Fin d) ℝ
  σ₀ : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U →
    Matrix (Fin n) (Fin ell) ℝ
  L : ℝ≥0 → Cpath T n → ProbabilityMeasure (Cpath T n × U) → U → ℝ
  g : Cpath T n → ProbabilityMeasure (Cpath T n) → ℝ
  b_measurable : Measurable (fun z : ℝ≥0 × Cpath T n ×
    ProbabilityMeasure (Cpath T n × U) × U => b z.1 z.2.1 z.2.2.1 z.2.2.2)
  σ_measurable : Measurable (fun z : ℝ≥0 × Cpath T n ×
    ProbabilityMeasure (Cpath T n × U) × U => σ z.1 z.2.1 z.2.2.1 z.2.2.2)
  σ₀_measurable : Measurable (fun z : ℝ≥0 × Cpath T n ×
    ProbabilityMeasure (Cpath T n × U) × U => σ₀ z.1 z.2.1 z.2.2.1 z.2.2.2)
  L_measurable : Measurable (fun z : ℝ≥0 × Cpath T n ×
    ProbabilityMeasure (Cpath T n × U) × U => L z.1 z.2.1 z.2.2.1 z.2.2.2)
  g_measurable : Measurable (fun z : Cpath T n × ProbabilityMeasure (Cpath T n) => g z.1 z.2)
  b_nonanticipative : ∀ t x μ u, t ≤ T → b t x μ u =
    b t (stopPath t x) (stopLaw t μ) u
  σ_nonanticipative : ∀ t x μ u, t ≤ T → σ t x μ u =
    σ t (stopPath t x) (stopLaw t μ) u
  σ₀_nonanticipative : ∀ t x μ u, t ≤ T → σ₀ t x μ u =
    σ₀ t (stopPath t x) (stopLaw t μ) u
  L_nonanticipative : ∀ t x μ u, t ≤ T → L t x μ u =
    L t (stopPath t x) (stopLaw t μ) u

/-- The event on which the diffusion integrands have finite pathwise quadratic energy. -/
noncomputable def goodDiffusion {T : ℝ≥0} {n d ell : ℕ} {U Ω : Type*}
    [MetricSpace U] [MeasurableSpace U] [MeasurableSpace Ω]
    (M : Model T n d ell U) (t : ℝ≥0)
    (X : Ω → Cpath T n) (α : ℝ≥0 → Ω → U)
    (μbar : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n × U)) : Set Ω :=
  {ω | ∫⁻ r in Set.Icc (t : ℝ) (T : ℝ),
    ENNReal.ofReal
      ((frobenius (M.σ r.toNNReal (stopPath r.toNNReal (X ω))
        (μbar r.toNNReal ω) (α r.toNNReal ω))) ^ 2 +
       (frobenius (M.σ₀ r.toNNReal (stopPath r.toNNReal (X ω))
        (μbar r.toNNReal ω) (α r.toNNReal ω))) ^ 2) ∂volume < ⊤}

/-- Equation (2.4)/(A.1), with the paper's implicitly well-defined local Itô
integrals made explicit. The stochastic primitives J are witnessed by the
published local Itô relation and hence are not arbitrary solution data. -/
def SDEEquation {T : ℝ≥0} {n d ell : ℕ} {U Ω : Type*}
    [MetricSpace U] [MeasurableSpace U] [MeasurableSpace Ω]
    (M : Model T n d ell U) (t : ℝ≥0) (P : Measure Ω)
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X : Ω → Cpath T n) (W : Ω → Cpath T d) (B : Ω → Cpath T ell)
    (α : ℝ≥0 → Ω → U)
    (μbar : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n × U)) : Prop :=
  P (goodDiffusion M t X α μbar)ᶜ = 0 ∧
  (∀ᵐ ω ∂P, IntervalIntegrable
    (fun r : ℝ => M.b r.toNNReal (stopPath r.toNNReal (X ω))
      (μbar r.toNNReal ω) (α r.toNNReal ω)) volume (t : ℝ) (T : ℝ)) ∧
  ∃ (Jσ : Fin n → Fin d → ℝ≥0 → Ω → ℝ)
    (Jσ₀ : Fin n → Fin ell → ℝ≥0 → Ω → ℝ),
    (∀ i j, EthierKurtz.HasBrownianItoIntegral P
      (EthierKurtz.completedSDEPast P F)
      (fun s ω => pathAt (W ω) s j)
      (fun r ω => if t < r ∧ r ≤ T ∧ ω ∈ goodDiffusion M t X α μbar then
        M.σ r (stopPath r (X ω)) (μbar r ω) (α r ω) i j else 0)
      (Jσ i j)) ∧
    (∀ i j, EthierKurtz.HasBrownianItoIntegral P
      (EthierKurtz.completedSDEPast P F)
      (fun s ω => pathAt (B ω) s j)
      (fun r ω => if t < r ∧ r ≤ T ∧ ω ∈ goodDiffusion M t X α μbar then
        M.σ₀ r (stopPath r (X ω)) (μbar r ω) (α r ω) i j else 0)
      (Jσ₀ i j)) ∧
    ∀ s, t ≤ s → s ≤ T → ∀ᵐ ω ∂P, ∀ i : Fin n,
      pathAt (X ω) s i = pathAt (X ω) t i +
        (∫ r in (t : ℝ)..(s : ℝ),
          M.b r.toNNReal (stopPath r.toNNReal (X ω))
            (μbar r.toNNReal ω) (α r.toNNReal ω)) i +
        ∑ j : Fin d, (Jσ i j s ω - Jσ i j t ω) +
        ∑ j : Fin ell, (Jσ₀ i j s ω - Jσ₀ i j t ω)

/-- The cemetery value of the inverse of π on EReal. -/
noncomputable def piInv {T : ℝ≥0} {n d ell : ℕ} {U : Type*}
    [MetricSpace U] [MeasurableSpace U] (M : Model T n d ell U) (x : EReal) : Option U :=
  by
    classical
    exact if h : ∃ u : U, (M.π u : EReal) = x then some (Classical.choose h) else none

end MKVDPP.BStrong


