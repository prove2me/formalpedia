-- Prove2me | Definitions.Def_MFGLimit_Conc_Model
-- name    : MFGLimit_Conc_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:32.388687+00:00
-- url     : https://prove2.me/theorems/a9aa25d7-9d07-4f15-b957-ee21eb1cdf8c
-- title:
--   §2.1–§2.3 — filtered particle data, mean-field game model, empirical and Wasserstein objects
-- statement:
--   Fix a positive state dimension $d$, a horizon $T>0$, a filtered probability space $(\Omega,\mathcal F,(\mathcal F_t),P)$, independent standard $\mathcal F$-Wiener processes $W,B^0,B^1,\ldots$, and i.i.d. $\mathcal F_0$-measurable initial states $X^i_0$ with common law $\mu_0$. The action space $A$ is Polish. The model carries Borel coefficients $b,f,g$, matrices $\sigma,\sigma_0$, an exponent $p_*\in[1,2]$, and a selected Hamiltonian minimizer $\hat\alpha$.
--
--   The Hamiltonian and selected coefficients are
--   $$H(x,m,y)=\inf_{a\in A}\{b(x,m,a)\cdot y+f(x,m,a)\},\qquad \hat b(x,m,y)=b(x,m,\hat\alpha(x,m,y)),\quad \hat f(x,m,y)=f(x,m,\hat\alpha(x,m,y)).$$
--   An empirical measure is $m_x^n=n^{-1}\sum_{i=1}^n\delta_{x_i}$. A measure belongs to $\mathcal P_p$ when it is a probability measure with finite $p$th moment. Path space is $C([0,T];\mathbb R^d)$ with the supremum norm, and product path spaces carry their $\ell^1$ or $\ell^2$ norm. Two transport predicates record $W_p(\theta,\nu)\le\sqrt{2\kappa R(\nu\mid\theta)}$: one for all absolutely continuous probability laws, and the explicit $\nu\in\mathcal P_p$ form of (3.7).
--
--   These objects provide the common vocabulary for the concentration statements and their SDEs.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$, players are indexed from zero, and measures are total Lean objects restricted by finite-moment predicates. The empirical-measure formula and Wasserstein distance are the published platform definitions; relative entropy is Mathlib's extended nonnegative KL divergence.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 4–6, §2.1–§2.3, (2.1), (2.4), and p. 11, (3.6)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution

namespace MFGLimit.Conc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Euclidean state space of dimension `k`. -/
abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Continuous paths on the closed time interval, equipped with the supremum norm. -/
abbrev Path (k : ℕ) (T : ℝ≥0) := C(Set.Icc (0 : ℝ≥0) T, E k)

noncomputable instance pathMeasurableSpace (k : ℕ) (T : ℝ≥0) :
    MeasurableSpace (Path k T) := borel _

instance pathBorelSpace (k : ℕ) (T : ℝ≥0) : BorelSpace (Path k T) := ⟨rfl⟩

/-- A probability measure with finite `p`th moment. -/
def IsPp {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α]
    (p : ℝ) (μ : Measure α) : Prop :=
  IsProbabilityMeasure μ ∧ ∫⁻ x, ‖x‖ₑ ^ p ∂μ < ⊤

/-- The empirical probability measure, for positive `n`. -/
noncomputable def empMeas {α : Type*} [MeasurableSpace α] (n : ℕ)
    (x : Fin n → α) : Measure α :=
  WassersteinDRO.Duality.empiricalDistribution x

/-- A general filtered Wiener process, including independence of future increments from the past. -/
def IsFWiener {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (Z : ℝ≥0 → Ω → Fin k → ℝ) : Prop :=
  Peng1990.SMP.IsStdBrownian P Z ∧
  (∀ t, StronglyMeasurable[𝔽 t] (Z t)) ∧
  ∀ s, ProbabilityTheory.Indep
    (MeasurableSpace.comap (fun ω : Ω => fun (u : ℝ≥0) (j : Fin k) =>
      if s ≤ u then Z u ω j - Z s ω j else 0) inferInstance) (𝔽 s) P

/-- General filtered noise and diffusion data, shared by the Nash and generic interacting
systems. The action and costs of the game do not enter this object. -/
structure ParticleBase (Ω : Type*) [mΩ : MeasurableSpace Ω] (d d₀ : ℕ) where
  hd : 0 < d
  T : ℝ≥0
  hT : 0 < T
  P : Measure Ω
  probP : IsProbabilityMeasure P
  𝔽 : Filtration ℝ≥0 mΩ
  W : ℝ≥0 → Ω → Fin d₀ → ℝ
  B : ℕ → ℝ≥0 → Ω → Fin d → ℝ
  hW : IsFWiener 𝔽 P W
  hB : ∀ i, IsFWiener 𝔽 P (B i)
  indepNoise : iIndepFun (fun z : Option ℕ => fun ω : Ω =>
    (match z with
    | none => Sum.inl (fun t => W t ω)
    | some i => Sum.inr (fun t => B i t ω) :
      (ℝ≥0 → Fin d₀ → ℝ) ⊕ (ℝ≥0 → Fin d → ℝ))) P
  σ : Matrix (Fin d) (Fin d) ℝ
  σ₀ : Matrix (Fin d) (Fin d₀) ℝ

/-- Section 2.3 game data extending the general filtered particle system. The initial
states have law `μ₀`, and the minimizing selector is part of the model data. -/
structure Model (Ω A : Type*) [mΩ : MeasurableSpace Ω] [TopologicalSpace A]
    [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
    (d d₀ : ℕ) extends ParticleBase Ω d d₀ where
  X₀ : ℕ → Ω → E d
  measX₀ : ∀ i, StronglyMeasurable[𝔽 0] (X₀ i)
  indepX₀ : iIndepFun X₀ P
  identX₀ : ∀ i, IdentDistrib (X₀ i) (X₀ 0) P P
  pStar : ℝ
  hpStar : 1 ≤ pStar ∧ pStar ≤ 2
  b : E d → Measure (E d) → A → E d
  f : E d → Measure (E d) → A → ℝ
  g : E d → Measure (E d) → ℝ
  meas_b : Measurable (fun q : E d × {m : Measure (E d) // IsPp pStar m} × A =>
    b q.1 q.2.1.val q.2.2)
  meas_f : Measurable (fun q : E d × {m : Measure (E d) // IsPp pStar m} × A =>
    f q.1 q.2.1.val q.2.2)
  meas_g : Measurable (fun q : E d × {m : Measure (E d) // IsPp pStar m} =>
    g q.1 q.2.val)
  αhat : E d → Measure (E d) → E d → A
  αhat_min : ∀ x m y, IsPp pStar m →
    IsMinOn (fun a => inner ℝ (b x m a) y + f x m a) Set.univ (αhat x m y)

namespace Model

variable {Ω A : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace A]
  [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  {d d₀ : ℕ} (M : Model Ω A d d₀)

/-- The law of each initial state. -/
noncomputable def μ₀ : Measure (E d) := M.P.map (M.X₀ 0)

/-- Hamiltonian (2.4): the action infimum. Assumption A(1) ensures attainment. -/
noncomputable def H (x : E d) (m : Measure (E d)) (y : E d) : ℝ :=
  ⨅ a : A, inner ℝ (M.b x m a) y + M.f x m a

/-- The selected drift in (2.4). -/
noncomputable def bhat (x : E d) (m : Measure (E d)) (y : E d) : E d :=
  M.b x m (M.αhat x m y)

/-- The selected running cost in (2.4). -/
noncomputable def fhat (x : E d) (m : Measure (E d)) (y : E d) : ℝ :=
  M.f x m (M.αhat x m y)

/-- The empirical measure of `n` state vectors. -/
noncomputable def empirical {n : ℕ} (x : Fin n → E d) : Measure (E d) :=
  empMeas n x

/-- The empirical measure of `n` trajectories. -/
noncomputable def empiricalPath {n : ℕ} (x : Fin n → Path d M.T) : Measure (Path d M.T) :=
  empMeas n x

/-- The time marginal of a path law. -/
noncomputable def marginal (m : Measure (Path d M.T)) (t : Set.Icc (0 : ℝ≥0) M.T) :
    Measure (E d) := m.map (fun x => x t)

end Model

/-- The two product path spaces used for the ℓ¹ and ℓ² Lipschitz classes. -/
abbrev Paths1 (n d : ℕ) (T : ℝ≥0) := PiLp 1 (fun _ : Fin n => Path d T)
abbrev Paths2 (n d : ℕ) (T : ℝ≥0) := PiLp 2 (fun _ : Fin n => Path d T)

/-- An `n`-tuple of paths as a point of the ℓ² product space. -/
noncomputable def toPaths2 {n d : ℕ} {T : ℝ≥0} (x : Fin n → Path d T) : Paths2 n d T :=
  WithLp.toLp 2 x

/-- A tuple of state vectors with its ℓ² norm. -/
noncomputable def stateNorm2 {n d : ℕ} (x : Fin n → E d) : ℝ :=
  ‖(WithLp.toLp 2 x : PiLp 2 (fun _ : Fin n => E d))‖

/-- Relative-entropy transport inequality `T_p(κ)` for all probability laws absolutely
continuous with respect to the reference law, including laws with infinite `p`th moment. -/
def TransportIneq {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α]
    (p κ : ℝ) (θ : Measure α) : Prop :=
  IsPp p θ ∧ 0 < κ ∧
  ∀ ν : Measure α, IsProbabilityMeasure ν → ν ≪ θ →
    WassersteinDRO.Duality.wassersteinDistance p θ ν ≤
      (ENNReal.ofReal (2 * κ) * InformationTheory.klDiv ν θ) ^ (1 / 2 : ℝ)

/-- The domain-restricted form explicitly printed in (3.7): `ν ∈ P_p`. -/
def TransportIneqPp {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α]
    (p κ : ℝ) (θ : Measure α) : Prop :=
  IsPp p θ ∧ 0 < κ ∧
  ∀ ν : Measure α, IsPp p ν → ν ≪ θ →
    WassersteinDRO.Duality.wassersteinDistance p θ ν ≤
      (ENNReal.ofReal (2 * κ) * InformationTheory.klDiv ν θ) ^ (1 / 2 : ℝ)

end MFGLimit.Conc


