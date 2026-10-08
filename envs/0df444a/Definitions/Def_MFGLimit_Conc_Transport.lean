-- Prove2me | Definitions.Def_MFGLimit_Conc_Transport
-- name    : MFGLimit_Conc_Transport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:05.325865+00:00
-- url     : https://prove2.me/theorems/b1bce74f-c566-43f9-a163-9312c16001a4
-- title:
--   §3.1 and §5.1–§5.2 — product norms, generic interacting drifts and path laws
-- statement:
--   For particle paths $x=(x^1,\ldots,x^n)$, the $\ell^p$ product norm is $\|x\|_{n,p}=(\sum_i\|x^i\|_\infty^p)^{1/p}$. The generic drift condition (5.4) bounds $\|\tilde b(t,x,m)-\tilde b(t,y,m')\|$ by $L(\|x-y\|+W_p(m,m'))$ for measures with finite $p$th moment; (5.5) bounds $\tilde b(t,0,\delta_0)$ on the time interval. The law of a particle system is the push-forward of $P$ to the product path space, and synchronous coupling is the joint push-forward of two systems driven by the same noises.
--
--   For Theorem 5.3, the $k$-coordinate path norm is the $\ell^2$ sum of the scalar coordinates' time-supremum norms. The single SDE solution predicate records $dX_t=b(t,X_t)dt+\sigma dW_t$ and $X_0=x$.
--
--   These reusable definitions make the dimension and norm in each transport or concentration claim explicit.
--
--   **Formalization Note** The product spaces carry their Borel sigma-algebras. The drift is evaluated at the same time on both sides of (5.4), the reading used in the paper's proof; its printed $t'$ has no corresponding term on the right.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 10, 18–20, §3.1, (5.1)–(5.7)

import Mathlib
import Definitions.Def_MFGLimit_Conc_Equations

namespace MFGLimit.Conc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω A : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace A]
  [PolishSpace A] [MeasurableSpace A] [BorelSpace A] {d d₀ : ℕ}

/-- The Borel ℓᵖ product space of particle trajectories. -/
noncomputable instance pathsMeasurableSpace (p : ℝ≥0∞) (n d : ℕ) (T : ℝ≥0) :
    MeasurableSpace (PiLp p (fun _ : Fin n => Path d T)) := borel _

instance pathsBorelSpace (p : ℝ≥0∞) (n d : ℕ) (T : ℝ≥0) :
    BorelSpace (PiLp p (fun _ : Fin n => Path d T)) := ⟨rfl⟩

/-- The ℓᵖ product norm on particle initial states. -/
noncomputable def stateLpNorm (p : ℝ≥0∞) {n d : ℕ} (x : Fin n → E d) : ℝ :=
  ‖(WithLp.toLp p x : PiLp p (fun _ : Fin n => E d))‖

/-- A tuple of particle paths as an element of its ℓᵖ product space. -/
noncomputable def toPaths (p : ℝ≥0∞) {n d : ℕ} {T : ℝ≥0}
    (x : Fin n → Path d T) : PiLp p (fun _ : Fin n => Path d T) :=
  WithLp.toLp p x

/-- The product-path law of an `n`-particle system. -/
noncomputable def particleLaw (M : ParticleBase Ω d d₀) (p : ℝ≥0∞) {n : ℕ}
    (X : Fin n → Ω → Path d M.T) : Measure (PiLp p (fun _ : Fin n => Path d M.T)) :=
  M.P.map (fun ω => toPaths p (fun i => X i ω))

/-- The joint law of two systems driven synchronously by the same noises. -/
noncomputable def synchronousLaw (M : ParticleBase Ω d d₀) (p : ℝ≥0∞) {n : ℕ}
    (X Y : Fin n → Ω → Path d M.T) :
    Measure ((PiLp p (fun _ : Fin n => Path d M.T)) ×
      (PiLp p (fun _ : Fin n => Path d M.T))) :=
  M.P.map (fun ω => (toPaths p (fun i => X i ω), toPaths p (fun i => Y i ω)))

/-- (5.4), with its time argument read at the same time on both sides. -/
def HasInteractingLipschitz (M : ParticleBase Ω d d₀) (p L : ℝ)
    (btil : ℝ≥0 → E d → Measure (E d) → E d) : Prop :=
  0 ≤ L ∧
  Measurable (fun q : {q : ℝ≥0 × E d × Measure (E d) //
      q.1 ≤ M.T ∧ IsPp p q.2.2} => btil q.1.1 q.1.2.1 q.1.2.2) ∧
  ∀ t ≤ M.T, ∀ x y m m', IsPp p m → IsPp p m' →
    ‖btil t x m - btil t y m'‖ ≤ L * (‖x - y‖ + Wp p m m')

/-- The drift conditions (5.4) and (5.5) with fixed Lipschitz constant. -/
def IsInteractingDriftWith (M : ParticleBase Ω d d₀) (p L : ℝ)
    (btil : ℝ≥0 → E d → Measure (E d) → E d) : Prop :=
  HasInteractingLipschitz M p L btil ∧
    ∃ K : ℝ, ∀ t ≤ M.T,
      ‖btil t (0 : E d) (Measure.dirac (0 : E d))‖ ≤ K

def IsInteractingDrift (M : ParticleBase Ω d d₀) (p : ℝ)
    (btil : ℝ≥0 → E d → Measure (E d) → E d) : Prop :=
  ∃ L : ℝ, IsInteractingDriftWith M p L btil

/-- The i.i.d. initial conditions and second moment used in (5.6). -/
def IsGenericInitial (M : ParticleBase Ω d d₀) (ξ : ℕ → Ω → E d)
    (μtil : Measure (E d)) : Prop :=
  (∀ i, StronglyMeasurable[M.𝔽 0] (ξ i)) ∧
  iIndepFun ξ M.P ∧
  (∀ i, IdentDistrib (ξ i) (ξ 0) M.P M.P) ∧
  μtil = M.P.map (ξ 0) ∧ IsPp 2 μtil

/-- Coordinatewise path space for the `k,2` norm of Theorem 5.3: the ℓ² sum of the
coordinatewise time-supremum norms. -/
abbrev CoordPaths (k : ℕ) (T : ℝ≥0) :=
  PiLp 2 (fun _ : Fin k => C(Set.Icc (0 : ℝ≥0) T, ℝ))

noncomputable instance coordPathsMeasurableSpace (k : ℕ) (T : ℝ≥0) :
    MeasurableSpace (CoordPaths k T) := borel _

instance coordPathsBorelSpace (k : ℕ) (T : ℝ≥0) :
    BorelSpace (CoordPaths k T) := ⟨rfl⟩

/-- Identify an `ℝᵏ`-valued continuous path with its `k` scalar coordinate paths. -/
noncomputable def toCoordPaths {k : ℕ} {T : ℝ≥0} (x : Path k T) : CoordPaths k T :=
  WithLp.toLp 2 (fun j =>
    (⟨fun t => (x t) j, by fun_prop⟩ : C(Set.Icc (0 : ℝ≥0) T, ℝ)))

/-- An SDE solution to `dX=b(t,X)dt+σdW`, encoded through Peng's coordinate Itô integral. -/
def IsSingleSDE {Ω : Type*} [mΩ : MeasurableSpace Ω] {k k' : ℕ}
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin k' → ℝ)
    (b : ℝ≥0 → E k → E k) (σ : Matrix (Fin k) (Fin k') ℝ)
    (x : E k) (X : Ω → Path k T) : Prop :=
  Measurable X ∧ StronglyAdapted 𝔽 (fun t ω => pathAt (X ω) t) ∧
  ∃ J : Fin k → Fin k' → ℝ≥0 → Ω → ℝ,
    (∀ j l, Peng1990.SMP.IsItoIntegral 𝔽 P T
      (fun s ω => W s ω l) (fun _ _ => σ j l) (J j l)) ∧
    ∀ t : ℝ≥0, t ≤ T → ∀ᵐ ω ∂P, ∀ j : Fin k,
      IntegrableOn (fun s : ℝ => b s.toNNReal (pathAt (X ω) s.toNNReal) j)
        (Set.Icc (0 : ℝ) t) ∧
      (pathAt (X ω) t) j = x j +
        (∫ s in Set.Icc (0 : ℝ) t,
          b s.toNNReal (pathAt (X ω) s.toNNReal) j) +
        ∑ l : Fin k', J j l t ω

/-- The operator norm of the Euclidean linear map represented by a matrix. -/
noncomputable def matrixOpNorm {k k' : ℕ}
    (σ : Matrix (Fin k) (Fin k') ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin σ).toContinuousLinearMap‖

end MFGLimit.Conc


