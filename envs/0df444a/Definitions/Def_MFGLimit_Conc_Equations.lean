-- Prove2me | Definitions.Def_MFGLimit_Conc_Equations
-- name    : MFGLimit_Conc_Equations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:03.354119+00:00
-- url     : https://prove2.me/theorems/407d576c-cddd-4265-9ccb-79ac6e609d18
-- title:
--   §2.3–§2.5 and §4 — Nash and master PDEs, Assumptions A/B/B′, particle SDEs
-- statement:
--   The **Nash system** is the $n$-player Hamilton–Jacobi system (2.6), including both the $\sigma\sigma^\top$ and $\sigma_0\sigma_0^\top$ second-derivative sums and its terminal cost $g(x_i,m_x^n)$. The **master equation** is (2.8), with the first and second intrinsic measure derivatives, the spatial and mixed derivatives, all common-noise terms, and the same terminal cost. A classical solution carries the regularity and growth stipulated on pp. 8–9.
--
--   **Assumption A** records attainment of the Hamiltonian minimum, a uniform Lipschitz bound for $\hat b$, nondegenerate $\sigma$, a $p'>4$ moment for $\mu_0$, classical Nash solutions for every positive $n$, and existence of a classical master solution. **B** bounds the $y$-Lipschitz constant of $\hat f$; **B′** instead bounds $U$ and $v^{n,i}$ and gives $\hat f$ a locally Lipschitz quadratic-growth estimate.
--
--   The Nash state $X$, comparison state $\bar X$, and generic interacting state $\tilde X$ satisfy the integral forms of (2.7), (4.1), and (5.6), driven by the same specified Wiener coordinates. These predicates keep the SDE solution and its initial condition connected to the data.
--
--   **Formalization Note** Particle solutions are continuous-path-valued and their stochastic terms use the published $L^2$ Itô-integral relation. The functions $v$ and $U$ are solution inputs, not unconstrained derivative fields. The master equation is required on $\mathcal P_2$; its spatial gradient is defined and $W_{p_*}$-Lipschitz on $\mathcal P_{p_*}$, following A(5). Time is nonnegative real and player indexing begins at zero.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 6–9, 15, (2.6)–(2.8), Assumptions A, B, B′, (4.1), and p. 19, (5.6)

import Mathlib
import Definitions.Def_MFGLimit_Conc_Model
import Definitions.Def_MFGLimit_Conc_MeasureDeriv

namespace MFGLimit.Conc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω A : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace A]
  [PolishSpace A] [MeasurableSpace A] [BorelSpace A] {d d₀ : ℕ}

/-- The vector represented by one column of a diffusion matrix. -/
noncomputable def matrixCol {k l : ℕ} (σ : Matrix (Fin k) (Fin l) ℝ) (j : Fin l) : E k :=
  WithLp.toLp 2 (fun i => σ i j)

/-- `Tr(σσᵀD)` for a linear map `D`, expressed by its column action. -/
noncomputable def covarianceTrace {k l : ℕ} (σ : Matrix (Fin k) (Fin l) ℝ)
    (D : E k →L[ℝ] E k) : ℝ :=
  ∑ j : Fin l, inner ℝ (D (matrixCol σ j)) (matrixCol σ j)

/-- The genuine partial gradient `D_{x_j} v^{n,i}`. -/
noncomputable def nashGrad (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ)
    (n : ℕ) (i j : Fin n) (t : ℝ≥0) (x : Fin n → E d) : E d :=
  grad (fun z => v n i t (Function.update x j z)) (x j)

/-- The block Hessian `D²_{x_j,x_k} v^{n,i}`. -/
noncomputable def nashHess (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ)
    (n : ℕ) (i j k : Fin n) (t : ℝ≥0) (x : Fin n → E d) : E d →L[ℝ] E d :=
  fderiv ℝ (fun z => nashGrad v n i j t (Function.update x k z)) (x k)

/-- The time derivative inside `(0,T)`. -/
noncomputable def nashTimeDeriv (T : ℝ≥0)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ)
    (n : ℕ) (i : Fin n) (t : ℝ≥0) (x : Fin n → E d) : ℝ :=
  derivWithin (fun s : ℝ => v n i s.toNNReal x)
    (Set.Icc (0 : ℝ) T) (t : ℝ)

/-- Equation (2.6), with both idiosyncratic and common-noise diffusion terms. -/
noncomputable def nashResidual (M : Model Ω A d d₀)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ)
    (n : ℕ) (i : Fin n) (t : ℝ≥0) (x : Fin n → E d) : ℝ :=
  nashTimeDeriv M.T v n i t x + M.H (x i) (empMeas n x) (nashGrad v n i i t x) +
  (∑ j : Fin n, if j = i then 0 else
    inner ℝ (nashGrad v n i j t x)
      (M.bhat (x j) (empMeas n x) (nashGrad v n j j t x))) +
  (1 / 2 : ℝ) * (∑ j : Fin n, covarianceTrace M.σ (nashHess v n i j j t x)) +
  (1 / 2 : ℝ) * (∑ j : Fin n, ∑ k : Fin n,
    covarianceTrace M.σ₀ (nashHess v n i j k t x))

/-- A classical solution of (2.6), including the regularity and per-player growth of A(4). -/
def IsNashSystemSolution (M : Model Ω A d d₀)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → ∀ i : Fin n, ∀ t : ℝ≥0, t ≤ M.T →
    ContDiff ℝ 2 (v n i t)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ i : Fin n, ∀ x : Fin n → E d,
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) M.T →
      ∃ r : ℝ, HasDerivWithinAt (fun s : ℝ => v n i s.toNNReal x) r
        (Set.Icc (0 : ℝ) M.T) t) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ i : Fin n, ∀ x : Fin n → E d,
    ContinuousOn (fun t : ℝ => nashTimeDeriv M.T v n i t.toNNReal x)
      (Set.Icc (0 : ℝ) M.T)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ i j k : Fin n,
    ContinuousOn (fun q : ℝ≥0 × (Fin n → E d) => v n i q.1 q.2)
      {q | q.1 ≤ M.T} ∧
    ContinuousOn (fun q : ℝ≥0 × (Fin n → E d) => nashGrad v n i j q.1 q.2)
      {q | q.1 ≤ M.T} ∧
    ContinuousOn (fun q : ℝ≥0 × (Fin n → E d) => nashHess v n i j k q.1 q.2)
      {q | q.1 ≤ M.T}) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ i : Fin n, ∀ t : ℝ≥0,
    0 < t → t < M.T → ∀ x, nashResidual M v n i t x = 0) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ i : Fin n, ∀ x,
    v n i M.T x = M.g (x i) (empMeas n x)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ i : Fin n,
    ∃ L : ℝ, ∀ t ≤ M.T, ∀ x,
      |v n i t x| ≤ L * (1 + stateNorm2 x ^ 2)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ i j : Fin n,
    ∃ L : ℝ, ∀ t ≤ M.T, ∀ x,
      ‖nashGrad v n i j t x‖ ≤ L * (1 + stateNorm2 x))

/-- The genuine spatial gradient of the master field. -/
noncomputable def masterDx (U : ℝ≥0 → E d → Measure (E d) → ℝ)
    (t : ℝ≥0) (x : E d) (m : Measure (E d)) : E d :=
  grad (fun z => U t z m) x

noncomputable def masterDxx (U : ℝ≥0 → E d → Measure (E d) → ℝ)
    (t : ℝ≥0) (x : E d) (m : Measure (E d)) : E d →L[ℝ] E d :=
  fderiv ℝ (fun z => masterDx U t z m) x

noncomputable def masterDt (T : ℝ≥0)
    (U : ℝ≥0 → E d → Measure (E d) → ℝ)
    (t : ℝ≥0) (x : E d) (m : Measure (E d)) : ℝ :=
  derivWithin (fun s : ℝ => U s.toNNReal x m)
    (Set.Icc (0 : ℝ) T) (t : ℝ)

noncomputable def masterDm (D : ℝ≥0 → E d → Measure (E d) → E d → ℝ)
    (t : ℝ≥0) (x : E d) (m : Measure (E d)) (z : E d) : E d :=
  grad (D t x m) z

noncomputable def masterDvDm (D : ℝ≥0 → E d → Measure (E d) → E d → ℝ)
    (t : ℝ≥0) (x : E d) (m : Measure (E d)) (z : E d) : E d →L[ℝ] E d :=
  fderiv ℝ (masterDm D t x m) z

noncomputable def masterDxDm (D : ℝ≥0 → E d → Measure (E d) → E d → ℝ)
    (t : ℝ≥0) (x : E d) (m : Measure (E d)) (z : E d) : E d →L[ℝ] E d :=
  fderiv ℝ (fun y => masterDm D t y m z) x

/-- Joint continuity on `[0,T] × ℝᵈ × P₂ × ℝᵈ × ℝᵈ`, where the measure
coordinate carries `W₂`. Unused arguments permit the same predicate for each derivative. -/
def IsJointW2Continuous {β : Type*} [NormedAddCommGroup β]
    (T : ℝ≥0)
    (F : ℝ≥0 → E d → Measure (E d) → E d → E d → β) : Prop :=
  ∀ t ≤ T, ∀ x m z z', IsPp 2 m → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s ≤ T, ∀ y m' w w', IsPp 2 m' →
        dist t s + dist x y + Wp 2 m m' + dist z w + dist z' w' < δ →
          dist (F t x m z z') (F s y m' w w') < ε

/-- The full master equation (2.8). The double measure integral is iterated as printed. -/
noncomputable def masterResidual (M : Model Ω A d d₀)
    (U : ℝ≥0 → E d → Measure (E d) → ℝ)
    (D : ℝ≥0 → E d → Measure (E d) → E d → ℝ)
    (D₂ : ℝ≥0 → E d → Measure (E d) → E d → E d → ℝ)
    (t : ℝ≥0) (x : E d) (m : Measure (E d)) : ℝ :=
  masterDt M.T U t x m + M.H x m (masterDx U t x m) +
  (1 / 2 : ℝ) *
    (covarianceTrace M.σ (masterDxx U t x m) +
     covarianceTrace M.σ₀ (masterDxx U t x m)) +
  (∫ z, inner ℝ (M.bhat z m (masterDx U t z m)) (masterDm D t x m z) ∂m) +
  (1 / 2 : ℝ) * (∫ z,
    covarianceTrace M.σ (masterDvDm D t x m z) +
    covarianceTrace M.σ₀ (masterDvDm D t x m z) ∂m) +
  (1 / 2 : ℝ) * (∫ z, ∫ z',
    covarianceTrace M.σ₀ (intrinsicSecond (D₂ t x) m z z') ∂m ∂m) +
  (∫ z, covarianceTrace M.σ₀ (masterDxDm D t x m z) ∂m)

/-- A classical solution of (2.8). Flat derivatives are normalized witnesses, while all
spatial derivatives are Fréchet derivatives computed from those witnesses. -/
def IsMasterSolution (M : Model Ω A d d₀)
    (U : ℝ≥0 → E d → Measure (E d) → ℝ) : Prop :=
  ∃ D : ℝ≥0 → E d → Measure (E d) → E d → ℝ,
  ∃ D₂ : ℝ≥0 → E d → Measure (E d) → E d → E d → ℝ,
    (∀ t ≤ M.T, ∀ x, IsFlatDeriv 2 (U t x) (D t x)) ∧
    (∀ t ≤ M.T, ∀ x z, IsFlatDeriv 2 (fun m => D t x m z)
      (fun m z' => D₂ t x m z z')) ∧
    (∀ t ≤ M.T, ∀ x m, IsPp 2 m →
      ContDiffAt ℝ 2 (fun y => U t y m) x ∧
      ContDiff ℝ 1 (D t x m) ∧
      ContDiff ℝ 2 (fun q : E d × E d => D₂ t x m q.1 q.2) ∧
      DifferentiableAt ℝ (D t x m) (0 : E d) ∧
      (∀ z, DifferentiableAt ℝ (D t x m) z ∧
        DifferentiableAt ℝ (masterDm D t x m) z ∧
        DifferentiableAt ℝ (fun y => masterDm D t y m z) x ∧
        ∀ z', DifferentiableAt ℝ (fun w => D₂ t x m z w) z' ∧
          DifferentiableAt ℝ (fun w => grad (fun v => D₂ t x m w v) z') z)) ∧
    (∀ t ≤ M.T, ∀ x m, IsPp 2 m →
      ∃ r : ℝ, HasDerivWithinAt (fun s : ℝ => U s.toNNReal x m) r
        (Set.Icc (0 : ℝ) M.T) (t : ℝ)) ∧
    (∀ t ≤ M.T, ∀ x m, IsPp M.pStar m →
      DifferentiableAt ℝ (fun y => U t y m) x) ∧
    IsJointW2Continuous M.T (fun t x m _ _ => U t x m) ∧
    IsJointW2Continuous M.T (fun t x m _ _ => masterDt M.T U t x m) ∧
    IsJointW2Continuous M.T (fun t x m _ _ => masterDx U t x m) ∧
    IsJointW2Continuous M.T (fun t x m z _ => masterDm D t x m z) ∧
    IsJointW2Continuous M.T (fun t x m _ _ => masterDxx U t x m) ∧
    IsJointW2Continuous M.T (fun t x m z _ => masterDvDm D t x m z) ∧
    IsJointW2Continuous M.T (fun t x m z _ => masterDxDm D t x m z) ∧
    IsJointW2Continuous M.T (fun t x m z z' => D₂ t x m z z') ∧
    IsJointW2Continuous M.T (fun t x m z z' =>
      intrinsicSecond (D₂ t x) m z z') ∧
    (∀ t ≤ M.T, ∀ x m, IsPp 2 m →
      Integrable (fun z => inner ℝ (M.bhat z m (masterDx U t z m)) (masterDm D t x m z)) m ∧
      Integrable (fun z => covarianceTrace M.σ (masterDvDm D t x m z) +
        covarianceTrace M.σ₀ (masterDvDm D t x m z)) m ∧
      Integrable (fun z => ∫ z', covarianceTrace M.σ₀
        (intrinsicSecond (D₂ t x) m z z') ∂m) m ∧
      (∀ z, Integrable (fun z' => covarianceTrace M.σ₀
        (intrinsicSecond (D₂ t x) m z z')) m) ∧
      Integrable (fun z => covarianceTrace M.σ₀ (masterDxDm D t x m z)) m) ∧
    (∀ t, 0 < t → t < M.T → ∀ x m, IsPp 2 m →
      masterResidual M U D D₂ t x m = 0) ∧
    (∀ x m, IsPp 2 m → U M.T x m = M.g x m) ∧
    (∃ L : ℝ, ∀ t ≤ M.T, ∀ x y m m', IsPp M.pStar m → IsPp M.pStar m' →
      ‖masterDx U t x m - masterDx U t y m'‖ ≤
        L * (‖x - y‖ + Wp M.pStar m m')) ∧
    (∃ K : ℝ, ∀ t ≤ M.T, ∀ x m, IsPp 2 m →
      ‖masterDx U t x m‖ ≤ K ∧
      (∀ z, ‖masterDm D t x m z‖ ≤ K ∧
        ‖masterDxDm D t x m z‖ ≤ K ∧
        ∀ z', ‖intrinsicSecond (D₂ t x) m z z'‖ ≤ K))

/-- Assumption A(1)–A(5), with the master solution existential as in the paper. -/
structure AssumptionA (M : Model Ω A d d₀)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ) : Prop where
  selector : ∀ x m y, IsPp M.pStar m →
    IsMinOn (fun a => inner ℝ (M.b x m a) y + M.f x m a)
      Set.univ (M.αhat x m y)
  bhatLip : ∃ L : ℝ, ∀ x x' y y' m m', IsPp M.pStar m → IsPp M.pStar m' →
    ‖M.bhat x m y - M.bhat x' m' y'‖ ≤
      L * (‖x - x'‖ + Wp M.pStar m m' + ‖y - y'‖)
  sigmaNondegenerate : M.σ.det ≠ 0
  initialMoment : ∃ p' : ℝ, 4 < p' ∧ IsPp p' M.μ₀
  nashSolution : IsNashSystemSolution M v
  masterSolution : ∃ U, IsMasterSolution M U

/-- Assumption B: the selected running cost is uniformly Lipschitz in the adjoint variable. -/
def AssumptionB (M : Model Ω A d d₀) : Prop :=
  ∃ L : ℝ, ∀ x m y y', IsPp M.pStar m →
    |M.fhat x m y - M.fhat x m y'| ≤ L * ‖y - y'‖

/-- Assumption B′(1)–(3), for the same `U` and `v` that enter the equations. -/
def AssumptionB' (M : Model Ω A d d₀)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ)
    (U : ℝ≥0 → E d → Measure (E d) → ℝ) : Prop :=
  (∃ K : ℝ, ∀ t ≤ M.T, ∀ x m, IsPp 2 m → |U t x m| ≤ K) ∧
  (∃ K : ℝ, ∀ n, 1 ≤ n → ∀ i : Fin n, ∀ t ≤ M.T, ∀ x,
    |v n i t x| ≤ K) ∧
  (∃ L : ℝ, ∀ x m y y', IsPp M.pStar m →
    |M.fhat x m y - M.fhat x m y'| ≤
      L * (1 + ‖y‖ + ‖y'‖) * ‖y - y'‖)

/-- Evaluation of a path after clipping time to `[0,T]`; on the interval this is ordinary
evaluation. -/
noncomputable def pathAt {k : ℕ} {T : ℝ≥0} (x : Path k T) (t : ℝ≥0) : E k :=
  x ⟨min t T, ⟨zero_le, min_le_right _ _⟩⟩

/-- The state vector of the particle paths at time `t`. -/
noncomputable def statesAt {n k : ℕ} {T : ℝ≥0}
    (X : Fin n → Ω → Path k T) (t : ℝ≥0) (ω : Ω) : Fin n → E k :=
  fun i => pathAt (X i ω) t

/-- The integral formulation of an interacting system, with independent Brownian motions
`Bⁱ` and the optional common Brownian motion `W`. The Itô relations are those of Peng's
published definition. -/
def IsParticleSystem (M : ParticleBase Ω d d₀) {n : ℕ}
    (drift : ℝ≥0 → (Fin n → E d) → Fin n → E d)
    (ξ : Fin n → Ω → E d) (σcommon : Matrix (Fin d) (Fin d₀) ℝ)
    (X : Fin n → Ω → Path d M.T) : Prop :=
  (∀ i : Fin n, Measurable (X i) ∧
    StronglyAdapted M.𝔽 (fun t ω => pathAt (X i ω) t)) ∧
  ∃ JB : Fin n → Fin d → Fin d → ℝ≥0 → Ω → ℝ,
  ∃ JW : Fin n → Fin d → Fin d₀ → ℝ≥0 → Ω → ℝ,
    (∀ i j l, Peng1990.SMP.IsItoIntegral M.𝔽 M.P M.T
      (fun s ω => M.B i.val s ω l) (fun _ _ => M.σ j l) (JB i j l)) ∧
    (∀ i j l, Peng1990.SMP.IsItoIntegral M.𝔽 M.P M.T
      (fun s ω => M.W s ω l) (fun _ _ => σcommon j l) (JW i j l)) ∧
    ∀ t : ℝ≥0, t ≤ M.T → ∀ᵐ ω ∂M.P, ∀ i : Fin n, ∀ j : Fin d,
      IntegrableOn (fun s : ℝ => drift s.toNNReal (statesAt X s.toNNReal ω) i j)
        (Set.Icc (0 : ℝ) t) ∧
      (pathAt (X i ω) t) j = (ξ i ω) j +
        (∫ s in Set.Icc (0 : ℝ) t,
          drift s.toNNReal (statesAt X s.toNNReal ω) i j) +
        (∑ l : Fin d, JB i j l t ω) +
        (∑ l : Fin d₀, JW i j l t ω)

/-- Nash equilibrium state system (2.7). -/
def IsNashState (M : Model Ω A d d₀)
    (v : ∀ n, Fin n → ℝ≥0 → (Fin n → E d) → ℝ)
    {n : ℕ} (X : Fin n → Ω → Path d M.T) : Prop :=
  IsParticleSystem M.toParticleBase
    (fun t x i => M.bhat (x i) (empMeas n x) (nashGrad v n i i t x))
    (fun i => M.X₀ i.val) M.σ₀ X

/-- McKean–Vlasov particle system (4.1), driven by the same noises and initial states. -/
def IsMVParticle (M : Model Ω A d d₀)
    (U : ℝ≥0 → E d → Measure (E d) → ℝ)
    {n : ℕ} (Xbar : Fin n → Ω → Path d M.T) : Prop :=
  IsParticleSystem M.toParticleBase
    (fun t x i => M.bhat (x i) (empMeas n x)
      (masterDx U t (x i) (empMeas n x)))
    (fun i => M.X₀ i.val) M.σ₀ Xbar

/-- The generic interacting system (5.6), with no common noise and arbitrary initial states. -/
def IsInteractingSystem (M : ParticleBase Ω d d₀)
    (btil : ℝ≥0 → E d → Measure (E d) → E d)
    {n : ℕ} (ξ : Fin n → Ω → E d) (X : Fin n → Ω → Path d M.T) : Prop :=
  IsParticleSystem M (fun t x i => btil t (x i) (empMeas n x)) ξ 0 X

end MFGLimit.Conc


