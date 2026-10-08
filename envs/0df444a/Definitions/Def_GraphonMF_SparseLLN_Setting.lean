-- Prove2me | Definitions.Def_GraphonMF_SparseLLN_Setting
-- name    : GraphonMF_SparseLLN_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:49.291696+00:00
-- url     : https://prove2.me/theorems/67a66e15-6c9a-4fbf-b3d6-870481701452
-- title:
--   Graphons, percolated particle systems, and their graphon limit
-- statement:
--   Fix a finite time horizon $T>0$ and dimension $d\ge1$. A **graphon** is a measurable, symmetric function $G:[0,1]^2\to[0,1]$. The setting defines the cut norm $\|G\|_\square$, the operator norm $\|G\|_{\infty\to1}$, continuous paths $\mathcal C_d=C([0,T];\mathbb R^d)$, Wasserstein distances, and the class $\mathcal M$ of measurable path-law families with uniformly bounded second moments.
--
--   It also defines independent initial states and Brownian motions, the limiting graphon system (4.2), and the finite percolated system (4.1). In the latter, edge $\xi^n_{ij}$ is Bernoulli with mean $\beta_nG_n(i/n,j/n)$ and each drift interaction is divided by $n\beta_n$; the diffusion is the state-only matrix $\sigma(X_i^n)$. Conditions 2.2(a,b), 4.1, 4.2, and 4.3 are available as separate predicates. The empirical law and the averaged continuum law are probability measures on $\mathcal C_d$.
--
--   These definitions supply the common model for the LLN and its intermediate estimates.
--
--   **Formalization Note** Particle indices in Lean start at zero, with label $(i+1)/n$. Paths are continuous maps; $\mathbb R^d$ uses a fixed sup norm, and matrices use an entrywise maximum norm. Time is $\mathbb R_{\ge0}$. The stochastic equations use natural, uncompleted filtrations and the referenced Itô-process notion. The law family is required to lie in $\mathcal M$; nonnegative expectations use lower integrals, preventing Lean's default-zero Bochner integral from changing the claim. Convergence in probability uses the weak topology on probability measures.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3590–3597, §1.2, Remark 2.1, (2.1)–(2.5), Conditions 2.2, 4.1–4.3, (4.1)–(4.2); https://doi.org/10.1214/22-AAP1901

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_GraphonMF_Stability_Setting
import Definitions.Def_GraphonMF_DenseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option autoImplicit false
noncomputable section

namespace GraphonMF.SparseLLN

abbrev Vec (d : ℕ) := Fin d → ℝ

instance (T : ℝ≥0) (d : ℕ) : BorelSpace (GraphonMF.Stability.Cd T d) := ⟨rfl⟩

/-- The cut norm of a bounded measurable kernel, with Borel test sets. -/
def cutNorm (W : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) : ℝ :=
  ⨆ (S : Set GraphonMF.Stability.I) (U : Set GraphonMF.Stability.I) (_ : MeasurableSet S ∧ MeasurableSet U),
    |∫ u in S, ∫ v in U, W u v|

/-- The law families with measurable dependence on the label and bounded second moments. -/
structure InM {T : ℝ≥0} {d : ℕ} (μ : GraphonMF.Stability.I → Measure (GraphonMF.Stability.Cd T d)) : Prop where
  measurable : Measurable μ
  probability : ∀ u, IsProbabilityMeasure (μ u)
  moment : (⨆ u, ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ u)) < ⊤

/-- The initial states and all Brownian motions share one probability space. -/
structure NoiseSetting {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d)
    (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d) : Prop where
  probability : IsProbabilityMeasure P
  initial_measurable : ∀ u, Measurable (X0 u)
  brownian : ∀ u, Peng1990.SMP.IsStdBrownian P (B u)
  independent : iIndep (fun z : GraphonMF.Stability.I ⊕ GraphonMF.Stability.I =>
    match z with
    | Sum.inl u => MeasurableSpace.comap (X0 u) inferInstance
    | Sum.inr u => MeasurableSpace.comap (fun ω => fun t => B u t ω) inferInstance) P

/-- The natural filtration of the initial state and driving Brownian motion at `u`. -/
def filtU {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X0 : GraphonMF.Stability.I → Ω → Vec d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d}
    (h : NoiseSetting P X0 B) (u : GraphonMF.Stability.I) : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  Filtration.natural (fun t ω => (X0 u ω, B u t ω))
    (fun t => ((h.initial_measurable u).prodMk ((h.brownian u).meas t)).stronglyMeasurable)

/-- Evaluation of a continuous path, held constant after the horizon. -/
def atTime {T : ℝ≥0} {d : ℕ} (x : GraphonMF.Stability.Cd T d) (t : ℝ≥0) : Vec d :=
  x ⟨min t T, ⟨bot_le, min_le_right _ _⟩⟩

/-- The initial law family is constructed from the initial random variables. -/
def initialLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (u : GraphonMF.Stability.I) : Measure (Vec d) :=
  P.map (X0 u)

/-- Condition 2.2(a): a finite interval cover and W₂ continuity of initial laws on each interval. -/
def Cond22a {d : ℕ} (μ0 : GraphonMF.Stability.I → Measure (Vec d))
    {N : ℕ} (J : Fin N → Set GraphonMF.Stability.I) : Prop :=
  (∀ i, Set.OrdConnected (J i)) ∧
  (⋃ i, J i) = Set.univ ∧
  ∀ i, ∀ u ∈ J i, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ J i, dist v u < δ → GraphonMF.Stability.W2 (μ0 v) (μ0 u) < ENNReal.ofReal ε

/-- Condition 2.2(b): continuity in the kernel's two variables away from a null section. -/
def Cond22b (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) {N : ℕ} (J : Fin N → Set GraphonMF.Stability.I) : Prop :=
  ∀ i, ∀ u ∈ interior (J i), ∃ A : Set GraphonMF.Stability.I,
    volume A = 0 ∧ ∀ v ∉ A, ContinuousAt (Function.uncurry G) (u, v)

/-- A fixed entrywise maximum norm on the diffusion matrices. -/
def matrixNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖fun p : Fin d × Fin d => M p.1 p.2‖

/-- Condition 4.1, with the inverse of a matrix interpreted as its matrix inverse. -/
def Cond41 {d : ℕ} (μ0 : GraphonMF.Stability.I → Measure (Vec d))
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (β : ℕ → ℝ) : Prop :=
  Measurable μ0 ∧
  (∀ u, IsProbabilityMeasure (μ0 u)) ∧
  (⨆ u, ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ0 u)) < ⊤ ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖b x y‖ ≤ C) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ x x' y y',
    ‖b x y - b x' y'‖ ≤ K * (‖x - x'‖ + ‖y - y'‖)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ x, matrixNorm (σ x) ≤ C) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ x y, matrixNorm (σ x - σ y) ≤ K * ‖x - y‖) ∧
  (∀ x, IsUnit (σ x).det) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ x, matrixNorm ((σ x)⁻¹) ≤ C) ∧
  (∀ n, 1 ≤ n → 0 < β n ∧ β n ≤ 1) ∧
  Tendsto (fun n : ℕ => (n : ℝ) * β n) atTop atTop

/-- The unordered pairs of particle labels, including diagonal pairs. -/
abbrev EdgeIndex (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- The sigma algebra generated by all initial states and Brownian paths. -/
def noiseSigma {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d) : MeasurableSpace Ω :=
  (⨆ u, MeasurableSpace.comap (X0 u) inferInstance) ⊔
  (⨆ u, MeasurableSpace.comap (fun ω => fun t => B u t ω) inferInstance)

/-- Bernoulli edges for one graphon sequence, symmetric and independent of the noise. -/
def EdgesFrom {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (β : ℕ → ℝ) : Prop :=
  (∀ n i j, Measurable (fun ω => ξ n ω i j)) ∧
  (∀ n i j, (fun ω => ξ n ω i j) =ᵐ[P] (fun ω => ξ n ω j i)) ∧
  (∀ n i j, (∀ᵐ ω ∂P, ξ n ω i j = 0 ∨ ξ n ω i j = 1) ∧
    P {ω | ξ n ω i j = 1} = ENNReal.ofReal (β n * Gs n (GraphonMF.Stability.lab n i) (GraphonMF.Stability.lab n j))) ∧
  ∀ n, iIndep (fun z : EdgeIndex n ⊕ Unit =>
    match z with
    | Sum.inl p => MeasurableSpace.comap (fun ω => ξ n ω p.1.1 p.1.2) inferInstance
    | Sum.inr _ => noiseSigma X0 B) P

def Cond42ab {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (β : ℕ → ℝ) : Prop :=
  (∀ n, 1 ≤ n → GraphonMF.Stability.IsStepGraphon n (Gs n)) ∧ EdgesFrom P X0 B ξ Gs β

def Cond42 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (β : ℕ → ℝ) (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) : Prop :=
  Cond42ab P X0 B ξ Gs β ∧
  Tendsto (fun n => cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0)

/-- Condition 4.3 uses the fixed graphon `G` instead of step graphons. -/
def Cond43 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (β : ℕ → ℝ) (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) : Prop :=
  EdgesFrom P X0 B ξ (fun _ => G) β

/-- The time-`s` law of a path-valued continuum solution. -/
def marginal {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (u : GraphonMF.Stability.I) (s : ℝ≥0) : Measure (Vec d) :=
  P.map (fun ω => atTime (X u ω) s)

/-- Solution of the limiting graphon system (4.2), in the class M. -/
def IsGraphonSolution42 {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B) (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) : Prop :=
  (∀ u, Measurable (X u)) ∧
  InM (fun u => P.map (X u)) ∧
  (∀ u ω, atTime (X u ω) 0 = X0 u ω) ∧
  ∀ u, Peng1990.SMP.IsItoProcess (filtU hnoise u) P T (B u) 0
    (fun s ω => ∫ v : GraphonMF.Stability.I, ∫ x : Vec d,
      (G u v) • b (atTime (X u ω) s) x ∂(marginal P X v s))
    (fun j s ω i => (σ (atTime (X u ω) s)) i j)
    (fun s ω => atTime (X u ω) s - X0 u ω)

/-- The natural filtration generated by all n-particle driving data. -/
def filtN {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X0 : GraphonMF.Stability.I → Ω → Vec d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d}
    (hnoise : NoiseSetting P X0 B)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (hξ : ∀ n i j, Measurable (fun ω => ξ n ω i j)) (n : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) := by
  have h₁ : Measurable (ξ n) := measurable_pi_lambda _ (fun i =>
    measurable_pi_lambda _ (fun j => hξ n i j))
  have h₂ : Measurable (fun ω => fun j : Fin n => X0 (GraphonMF.Stability.lab n j) ω) :=
    measurable_pi_lambda _ (fun j => hnoise.initial_measurable (GraphonMF.Stability.lab n j))
  have h₃ (t : ℝ≥0) : Measurable (fun ω => fun j : Fin n => B (GraphonMF.Stability.lab n j) t ω) :=
    measurable_pi_lambda _ (fun j => (hnoise.brownian (GraphonMF.Stability.lab n j)).meas t)
  exact {
    seq := fun t =>
      MeasurableSpace.comap (ξ n) inferInstance ⊔
      MeasurableSpace.comap (fun ω => fun j : Fin n => X0 (GraphonMF.Stability.lab n j) ω) inferInstance ⊔
      (⨆ s ≤ t, MeasurableSpace.comap
        (fun ω => fun j : Fin n => B (GraphonMF.Stability.lab n j) s ω) inferInstance)
    mono' := by
      intro s t hst
      refine sup_le le_sup_left ?_
      refine iSup₂_le fun r hr => ?_
      have hrt : r ≤ t := hr.trans hst
      exact le_sup_of_le_right (show
        MeasurableSpace.comap (fun ω => fun j : Fin n => B (GraphonMF.Stability.lab n j) r ω) inferInstance ≤
          (⨆ q ≤ t, MeasurableSpace.comap
            (fun ω => fun j : Fin n => B (GraphonMF.Stability.lab n j) q ω) inferInstance)
        from le_iSup_of_le r (le_iSup_of_le hrt le_rfl))
    le' := by
      intro t
      exact sup_le (sup_le h₁.comap_le h₂.comap_le)
        (iSup₂_le fun s hs => (h₃ s).comap_le)
  }

/-- Solution of the percolated n-particle system (4.1). -/
def IsParticleSolution41 {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (hξ : ∀ n i j, Measurable (fun ω => ξ n ω i j))
    (β : ℕ → ℝ) (b : Vec d → Vec d → Vec d)
    (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (Xn : Fin n → Ω → GraphonMF.Stability.Cd T d) : Prop :=
  (∀ i, Measurable (Xn i)) ∧
  (∀ i ω, atTime (Xn i ω) 0 = X0 (GraphonMF.Stability.lab n i) ω) ∧
  ∀ i, Peng1990.SMP.IsItoProcess (filtN hnoise ξ hξ n) P T
    (B (GraphonMF.Stability.lab n i)) 0
    (fun s ω => (1 / ((n : ℝ) * β n)) •
      ∑ j : Fin n, (ξ n ω i j) • b (atTime (Xn i ω) s) (atTime (Xn j ω) s))
    (fun j s ω k => (σ (atTime (Xn i ω) s)) k j)
    (fun s ω => atTime (Xn i ω) s - X0 (GraphonMF.Stability.lab n i) ω)

/-- The empirical law of n ≥ 1 continuous particle paths. -/
def empirical {T : ℝ≥0} {d : ℕ} {Ω : Type*}
    (n : ℕ) (hn : 0 < n) (Xn : Fin n → Ω → GraphonMF.Stability.Cd T d) (ω : Ω) :
    ProbabilityMeasure (GraphonMF.Stability.Cd T d) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let m : Measure (Fin n) := (PMF.uniformOfFintype (Fin n)).toMeasure
  letI : IsProbabilityMeasure m := inferInstance
  exact ⟨m.map (fun i => Xn i ω), Measure.isProbabilityMeasure_map (by fun_prop)⟩

/-- The averaged law ∫_I Law(X_u) du, as a probability measure. -/
def mixture {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hM : InM (fun u => P.map (X u))) : ProbabilityMeasure (GraphonMF.Stability.Cd T d) :=
  ⟨(volume : Measure GraphonMF.Stability.I).bind (fun u => P.map (X u)),
    isProbabilityMeasure_bind hM.measurable.aemeasurable
      (ae_of_all _ hM.probability)⟩

/-- The averaged law of a solution of (4.2). -/
def solutionMixture {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X0 : GraphonMF.Stability.I → Ω → Vec d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d}
    {hnoise : NoiseSetting P X0 B} {G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ}
    {b : Vec d → Vec d → Vec d} {σ : Vec d → Matrix (Fin d) (Fin d) ℝ}
    {X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d} (hX : IsGraphonSolution42 P X0 B hnoise G b σ X) :
    ProbabilityMeasure (GraphonMF.Stability.Cd T d) :=
  mixture P X hX.2.1

/-- Convergence in probability in the weak topology on probability measures. -/
def ConvergesInProbability {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ProbabilityMeasure (GraphonMF.Stability.Cd T d))
    (ν : ProbabilityMeasure (GraphonMF.Stability.Cd T d)) : Prop :=
  ∀ U ∈ 𝓝 ν, Tendsto (fun n => P {ω | Y n ω ∉ U}) atTop (𝓝 (0 : ℝ≥0∞))

/-- Positive-size empirical laws, indexed by `n+1` to avoid division at zero. -/
def empiricalSeq {T : ℝ≥0} {d : ℕ} {Ω : Type*}
    (Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d) :
    ℕ → Ω → ProbabilityMeasure (GraphonMF.Stability.Cd T d) :=
  fun n => empirical (n + 1) (Nat.succ_pos n) (Xn (n + 1))

def continuumEmpiricalSeq {T : ℝ≥0} {d : ℕ} {Ω : Type*}
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) : ℕ → Ω → ProbabilityMeasure (GraphonMF.Stability.Cd T d) :=
  fun n => empirical (n + 1) (Nat.succ_pos n) (fun i => X (GraphonMF.Stability.lab (n + 1) i))

/-- Mean squared pathwise coupling error; `n = 0` has no particles. -/
def errorAvg {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (n : ℕ) (Xn : Fin n → Ω → GraphonMF.Stability.Cd T d) : ℝ≥0∞ :=
  (1 / (n : ℝ≥0∞)) * ∑ i : Fin n,
    ∫⁻ ω, ‖Xn i ω - X (GraphonMF.Stability.lab n i) ω‖ₑ ^ 2 ∂P

/-- The second term Rⁿ,²_s in the four-term decomposition (7.2). -/
def Rn2 {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (β : ℕ → ℝ) (b : Vec d → Vec d → Vec d)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (n : ℕ) (Xn : Fin n → Ω → GraphonMF.Stability.Cd T d) (s : ℝ≥0) : ℝ≥0∞ :=
  (1 / (n : ℝ≥0∞)) * ∑ i : Fin n,
    ∫⁻ ω, ‖(1 / (n : ℝ)) •
      ∑ j : Fin n, (ξ n ω i j / β n) •
        (b (atTime (X (GraphonMF.Stability.lab n i) ω) s) (atTime (Xn j ω) s) -
         b (atTime (X (GraphonMF.Stability.lab n i) ω) s) (atTime (X (GraphonMF.Stability.lab n j) ω) s))‖ₑ ^ 2 ∂P

end GraphonMF.SparseLLN


