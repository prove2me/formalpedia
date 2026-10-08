-- Prove2me | Definitions.Def_GraphonMF_Stability_Setting
-- name    : GraphonMF_Stability_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:26:43.044555+00:00
-- url     : https://prove2.me/theorems/2d73f30e-7a12-42e4-9588-d4033c719af2
-- title:
--   §§1.2, 2 and 5.1 — graphons, path laws, Wasserstein metrics and the graphon SDE
-- statement:
--   Let $I=[0,1]$, let $T>0$, and let $\mathcal C_d=C([0,T];\mathbb R^d)$ with its uniform norm. A **graphon** is a measurable symmetric function $G:I^2\to[0,1]$. The cut norm tests its integral over measurable rectangles; the operator norm tests its action from bounded functions on $I$ to integrable functions on $I$.
--
--   The file defines the Wasserstein distances $W_2$ on state laws, $W_{2,t}$ on path laws through time $t$, and $W^\mathcal M_{2,t}$ as the supremum over labels. The class $\mathcal M$ consists of measurable families of probability laws on $\mathcal C_d$ with uniformly bounded second moments. Condition 2.1 asks for measurable initial laws with a uniform $(2+\varepsilon)$ moment and globally Lipschitz drift and diffusion coefficients.
--
--   On one probability space, each label has an independent initial state and a standard $d$-dimensional Brownian motion. A **frozen-flow solution** solves (5.1) for a prescribed law family in $\mathcal M$; a **graphon solution** solves (2.1) when that prescribed family is the family of its own path laws.
--
--   These definitions give the shared objects used in the stability statement and its supporting estimates.
--
--   **Formalization Note** Paths are bundled as continuous maps, time is nonnegative real, and $\mathbb R^d$ uses the sup norm. The Brownian and Itô notions and the coupling definition of Wasserstein distance are referenced published definitions. Integrability of both nested interaction integrals is explicit in the solution predicate. The law family is required to belong to $\mathcal M$; this is the class in which the paper proves well-posedness. $W_{2,t}$ is the published coupling formula with the seminorm $\|\cdot\|_{*,t}$; since $\|x\|_{*,T}$ is the norm of the path space, $W_{2,T}$ coincides with the published distance on paths (checked in a sorry-free verification lemma).
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3590–3592 and 3598, §1.2, (2.1)–(2.5), Condition 2.1, (5.1)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.Stability

abbrev I := unitInterval
abbrev State (d : ℕ) := Fin d → ℝ
abbrev Cd (T : ℝ≥0) (d : ℕ) := C(Set.Icc (0 : ℝ≥0) T, State d)

/-- The paper's label `(i+1)/n` for a zero-based particle index. -/
noncomputable def lab (n : ℕ) (i : Fin n) : I :=
  Set.projIcc 0 1 zero_le_one (((i.val + 1 : ℕ) : ℝ) / n)

/-- The grid point `⌈nu⌉/n` used to define a step graphon. -/
noncomputable def stepPt (n : ℕ) (u : I) : I :=
  Set.projIcc 0 1 zero_le_one ((⌈(n : ℝ) * (u : ℝ)⌉ : ℤ) / (n : ℝ))

noncomputable instance pathMeasurable (T : ℝ≥0) (d : ℕ) : MeasurableSpace (Cd T d) :=
  borel _

instance pathBorelSpace (T : ℝ≥0) (d : ℕ) : BorelSpace (Cd T d) := ⟨rfl⟩

/-- A graphon is a symmetric measurable kernel taking values in [0,1]. -/
def IsGraphon (G : I → I → ℝ) : Prop :=
  Measurable (Function.uncurry G) ∧
    (∀ u v, G u v = G v u) ∧
    ∀ u v, G u v ∈ Set.Icc (0 : ℝ) 1

/-- A graphon constant on the grid cells of (3.2). -/
def IsStepGraphon (n : ℕ) (G : I → I → ℝ) : Prop :=
  IsGraphon G ∧ ∀ u v, G u v = G (stepPt n u) (stepPt n v)

/-- The cut norm in §2, with measurable sets as the test sets. -/
noncomputable def cutNorm (W : I → I → ℝ) : ℝ :=
  ⨆ (S : Set I) (U : Set I) (_ : MeasurableSet S ∧ MeasurableSet U),
    |∫ p in S ×ˢ U, W p.1 p.2|

/-- The operator norm from L-infinity to L-one in Remark 2.1. -/
noncomputable def opNorm (W : I → I → ℝ) : ℝ :=
  ⨆ (g : I → ℝ) (_ : Measurable g ∧ ∀ v, |g v| ≤ 1),
    ∫ u, |∫ v, W u v * g v|

/-- Evaluation of a path at `s`, clamped to the time horizon outside [0,T]. -/
noncomputable def evalAt {T : ℝ≥0} {d : ℕ} (s : ℝ≥0) (x : Cd T d) : State d :=
  x ⟨min s T, ⟨bot_le, min_le_right _ _⟩⟩

/-- The sup norm of a path up to time `t`. -/
noncomputable def supUpTo {T : ℝ≥0} {d : ℕ} (t : ℝ≥0) (x : Cd T d) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ≥0) T, if (s : ℝ≥0) ≤ t then ‖x s‖ else 0

/-- The Wasserstein-2 distance on the state space, using the published coupling definition. -/
noncomputable def W2 {d : ℕ} (μ ν : Measure (State d)) : ENNReal :=
  WassersteinDRO.Duality.wassersteinDistance 2 μ ν

/-- The Wasserstein-2 distance on paths with the uniform norm. -/
noncomputable def W2T {T : ℝ≥0} {d : ℕ} (μ ν : Measure (Cd T d)) : ENNReal :=
  WassersteinDRO.Duality.wassersteinDistance 2 μ ν

/-- The Wasserstein distance induced by the path seminorm on [0,t], equation (2.4): the body of
the published coupling definition with `‖x‖_{*,t}` in place of the norm of `Cd T d`. -/
noncomputable def W2t {T : ℝ≥0} {d : ℕ} (t : ℝ≥0)
    (μ ν : Measure (Cd T d)) : ENNReal :=
  (⨅ (π : Measure (Cd T d × Cd T d))
      (_ : π.map Prod.fst = μ ∧ π.map Prod.snd = ν),
      ∫⁻ p, ENNReal.ofReal ((supUpTo t (p.1 - p.2)) ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ))

/-- The uniform Wasserstein distance over labels, equation (2.5). -/
noncomputable def W2M {T : ℝ≥0} {d : ℕ} (t : ℝ≥0)
    (μ ν : I → Measure (Cd T d)) : ENNReal :=
  ⨆ u, W2t t (μ u) (ν u)

/-- The class M of measurable path-law families with uniformly bounded second moments. -/
def InM {T : ℝ≥0} {d : ℕ} (μ : I → Measure (Cd T d)) : Prop :=
  Measurable μ ∧
    (∀ u, IsProbabilityMeasure (μ u)) ∧
    (⨆ u, ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ u)) < ⊤

/-- Condition 2.1: measurable initial laws, a uniform (2+ε)-moment and Lipschitz coefficients. -/
def Cond21 {d : ℕ} (ε : ℝ) (μ0 : I → Measure (State d))
    (b : State d → State d → State d)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  0 < ε ∧ Measurable μ0 ∧ (∀ u, IsProbabilityMeasure (μ0 u)) ∧
    (⨆ u, ∫⁻ x, ‖x‖ₑ ^ (2 + ε) ∂(μ0 u)) < ⊤ ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x x' y y',
      ‖b x y - b x' y'‖ +
        ‖Peng1990.SMP.matEntries (σ x y - σ x' y')‖ ≤
        K * (‖x - x'‖ + ‖y - y'‖)

/-- Independent initial states and independent standard Brownian motions on one probability space. -/
structure NoiseSetting {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (μ0 : I → Measure (State d))
    (X0 : I → Ω → State d) (B : I → ℝ≥0 → Ω → State d) : Prop where
  probability : IsProbabilityMeasure P
  initial_meas : ∀ u, Measurable (X0 u)
  initial_law : ∀ u, P.map (X0 u) = μ0 u
  brownian : ∀ u, Peng1990.SMP.IsStdBrownian P (B u)
  independent : iIndep
    (fun z : I ⊕ I => match z with
      | Sum.inl u => MeasurableSpace.comap (X0 u) inferInstance
      | Sum.inr u => ⨆ t : ℝ≥0, MeasurableSpace.comap (B u t) inferInstance) P

/-- The natural filtration generated by a particle's initial state and its Brownian motion. -/
noncomputable def filtU {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {μ0 : I → Measure (State d)}
    {X0 : I → Ω → State d} {B : I → ℝ≥0 → Ω → State d}
    (h : NoiseSetting P μ0 X0 B) (u : I) : Filtration ℝ≥0 mΩ :=
  Filtration.natural (fun t ω => (X0 u ω, B u t ω))
    (fun t => ((h.initial_meas u).prodMk ((h.brownian u).meas t)).stronglyMeasurable)

/-- The path law of one labelled process. -/
noncomputable def law {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ}
    (P : Measure Ω) (X : I → Ω → Cd T d) (u : I) : Measure (Cd T d) :=
  P.map (X u)

/-- A time marginal of a path law. -/
noncomputable def marginal {T : ℝ≥0} {d : ℕ} (μ : Measure (Cd T d))
    (s : ℝ≥0) : Measure (State d) :=
  μ.map (evalAt s)

/-- The frozen-flow drift in equation (5.1). -/
noncomputable def frozenDrift {T : ℝ≥0} {d : ℕ}
    (G : I → I → ℝ) (b : State d → State d → State d)
    (μ : I → Measure (Cd T d)) (u : I) (s : ℝ≥0) (z : State d) : State d :=
  ∫ v, ∫ x, (G u v) • b z x ∂(marginal (μ v) s)

/-- The column `j` of the frozen-flow diffusion matrix in equation (5.1). -/
noncomputable def frozenDiffusion {T : ℝ≥0} {d : ℕ}
    (G : I → I → ℝ)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ)
    (μ : I → Measure (Cd T d)) (u : I) (j : Fin d)
    (s : ℝ≥0) (z : State d) : State d :=
  fun i => ∫ v, ∫ x, G u v * σ z x i j ∂(marginal (μ v) s)

/-- A path-valued solution of the frozen-flow SDE (5.1); integrability is explicit. -/
def IsFrozenSolution {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ}
    (P : Measure Ω) (μ0 : I → Measure (State d))
    (X0 : I → Ω → State d) (B : I → ℝ≥0 → Ω → State d)
    (noise : NoiseSetting P μ0 X0 B)
    (G : I → I → ℝ) (b : State d → State d → State d)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ)
    (μ : I → Measure (Cd T d)) (X : I → Ω → Cd T d) : Prop :=
  InM μ ∧
    (∀ u, AEMeasurable (X u) P) ∧
    (∀ u s ω v,
      Integrable (fun x => (G u v) • b (evalAt s (X u ω)) x)
        (marginal (μ v) s) ∧
      (∀ j i, Integrable (fun x => G u v * σ (evalAt s (X u ω)) x i j)
        (marginal (μ v) s))) ∧
    (∀ u s ω,
      Integrable (fun v => ∫ x, (G u v) • b (evalAt s (X u ω)) x
        ∂(marginal (μ v) s)) ∧
      ∀ j i, Integrable (fun v => ∫ x, G u v * σ (evalAt s (X u ω)) x i j
        ∂(marginal (μ v) s))) ∧
    ∀ u,
      (∀ ω, evalAt 0 (X u ω) = X0 u ω) ∧
      Peng1990.SMP.IsItoProcess (filtU noise u) P T (B u) 0
        (fun s ω => frozenDrift G b μ u s (evalAt s (X u ω)))
        (fun j s ω => frozenDiffusion G σ μ u j s (evalAt s (X u ω)))
        (fun s ω => evalAt s (X u ω) - X0 u ω)

/-- A solution of the nonlinear graphon particle system (2.1). -/
def IsGraphonSolution {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ}
    (P : Measure Ω) (μ0 : I → Measure (State d))
    (X0 : I → Ω → State d) (B : I → ℝ≥0 → Ω → State d)
    (noise : NoiseSetting P μ0 X0 B)
    (G : I → I → ℝ) (b : State d → State d → State d)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ)
    (X : I → Ω → Cd T d) : Prop :=
  InM (law P X) ∧
    IsFrozenSolution P μ0 X0 B noise G b σ (law P X) X

end GraphonMF.Stability


