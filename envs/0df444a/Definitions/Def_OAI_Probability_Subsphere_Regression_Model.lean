-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Regression_Model
-- name    : OAI_Probability_Subsphere_Regression_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:34:25.914987+00:00
-- url     : https://prove2.me/theorems/6b598638-c90d-4077-991e-9475fef1ac1f
-- title:
--   Seeded deterministic finite-memory learners for recovering a unit vector from Gaussian linear measurements
-- statement:
--   Fix the dimension $d$, the memory size $M$ (in bits) and the number of samples $T$. Write $\mathbb{R}^d$ for Euclidean space, $S^{d-1}=\{u\in\mathbb{R}^d:\|u\|=1\}$ for its unit sphere, $Q_M=\{0,\dots,2^M-1\}$ for the set of memory states and $x=(x_0,\dots,x_{T-1})\in(\mathbb{R}^d)^T$ for a sample sequence.
--
--   1. **Reference laws.** The uniform law $\sigma_d$ on $S^{d-1}$ (surface measure divided by its total mass); the sample law $\gamma_d^{\otimes T}$ on $(\mathbb{R}^d)^T$, where $\gamma_d=N(0,I_d)$ is the standard Gaussian measure; and the observation reference measure $\gamma_d\otimes\mathrm{Leb}$ on $\mathbb{R}^d\times\mathbb{R}$.
--   2. **Learner.** For a seed space $\Omega$, a learner consists of an initial choice, a transition rule and an output rule,
--   $$c_0:\Omega\to\{0,1\}\times Q_M,\qquad \delta:\mathbb{N}\times\Omega\times Q_M\times(\mathbb{R}^d\times\mathbb{R})\to\{0,1\}\times Q_M,\qquad o:\mathbb{N}\times\Omega\times Q_M\to S^{d-1},$$
--   where a first coordinate $1$ means *stop*.
--   3. **Run.** Given a hidden vector $s\in S^{d-1}$, a seed $\omega$ and samples $x$, the run status is either *active in state $q$* or *stopped at time $t$ in state $q$*. At time $0$ it is "stopped at $0$ in $q$" if $c_0(\omega)=(1,q)$ and "active in $q$" if $c_0(\omega)=(0,q)$. Passing from time $n$ to $n+1$, a stopped status is kept; an active state $q$ with $n<T$ is updated by $(b,q')=\delta\bigl(n+1,\omega,q,(x_n,\langle x_n,s\rangle)\bigr)$ and becomes "stopped at $n+1$ in $q'$" if $b=1$ and "active in $q'$" if $b=0$; for $n\ge T$ an active status is kept.
--   4. **Terminal record and estimate.** The terminal record is $(t,q)$ if the status at time $T$ is "stopped at $t$ in $q$", and $(T,q)$ if it is "active in $q$". The estimate is $\hat s(s,\omega,x)=o(t,\omega,q)$ for the terminal record $(t,q)$.
--   5. **Admissibility.** For a measure $\rho$ on $\Omega$, the learner is admissible if: $c_0$ is $\rho$-a.e. measurable; for all $t\in\mathbb{N}$ and $q\in Q_M$ the map $(\omega,(x,y))\mapsto\delta(t,\omega,q,(x,y))$ is a.e. measurable for $\rho\otimes\gamma_d\otimes\mathrm{Leb}$; for all $t,q$ the map $\omega\mapsto o(t,\omega,q)$ is $\rho$-a.e. measurable; for every $s$ the map $(\omega,x)\mapsto\hat s(s,\omega,x)$ is $\rho\otimes\gamma_d^{\otimes T}$-a.e. measurable; and $(s,\omega,x)\mapsto\hat s(s,\omega,x)$ is $\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}$-a.e. measurable.
--   6. **Angular error and success.** The angular error of an estimate $\hat s$ for $s$ is $\arccos\langle\hat s,s\rangle\in[0,\pi]$. For $\varepsilon\in\mathbb{R}$, the success at $s$ and the uniform success are
--   $$\mathrm{succ}_\varepsilon(s)=\bigl(\rho\otimes\gamma_d^{\otimes T}\bigr)\bigl\{(\omega,x):\arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr\},$$
--   $$\mathrm{succ}^{\mathrm{unif}}_\varepsilon=\bigl(\sigma_d\otimes\rho\otimes\gamma_d^{\otimes T}\bigr)\bigl\{(s,\omega,x):\arccos\langle\hat s(s,\omega,x),s\rangle\le\varepsilon\bigr\}.$$
--
--   This is a one-pass streaming model: the learner sees the Gaussian rows $x_n$ with their noiseless labels $\langle x_n,s\rangle$ one at a time, keeps only $M$ bits of state between steps, may stop early, and all of its randomness lies in the seed $\omega$; stopping times and states are ordinary data of the run, not stored real numbers. Sample-complexity lower bounds for given success probabilities are proved for this deterministic seeded model and then transferred to the randomized kernel learners of the main theorem.
--
--   **Formalization Note** The namespace `SubsphereRegression` repeats the abbreviations `Vector d` (`EuclideanSpace ℝ (Fin d)`), `UnitSphere d`, `State M` (`Fin (2 ^ M)`), `Samples d T` and the measures `uniformSphere d` (`(σ univ)⁻¹ • σ` for `σ = volume.toSphere`), `sampleLaw d T` and `observationReference d`. The structure `Learner d M T Ω` (seed type `Ω : Type u`) has fields `initialChoice`, `transition` and `output`; `RunStatus M` is the sum type `State M ⊕ (ℕ × State M)`, and the remaining items are `start`, `run`, `terminal`, `estimate`, `Admissible`, `angularError`, `success` and `uniformSuccess`. The success quantities are the (outer) measures of the success events, valued in `ℝ≥0∞`; `ρ` is an arbitrary measure in these definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

universe u

namespace SubsphereRegression

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
abbrev State (M : ℕ) := Fin (2 ^ M)
abbrev Samples (d T : ℕ) := Fin T → Vector d

def uniformSphere (d : ℕ) : Measure (UnitSphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ

def sampleLaw (d T : ℕ) : Measure (Samples d T) :=
  Measure.pi fun _ => stdGaussian (Vector d)

def observationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

/-- A finite-state one-pass procedure. The Boolean `true` means stop.
All indices are prescribed ordinary sample indices, not stored real registers. -/
structure Learner (d M T : ℕ) (Ω : Type u) where
  initialChoice : Ω → Bool × State M
  transition : ℕ → Ω → State M → (Vector d × ℝ) → Bool × State M
  output : ℕ → Ω → State M → UnitSphere d

namespace Learner

/-- Active finite state, or stopped index and terminal finite state. -/
abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)

def start {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω) (ω : Ω) :
    RunStatus M :=
  let a := L.initialChoice ω
  if a.1 then .inr (0, a.2) else .inl a.2

def run {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → RunStatus M
  | 0 => L.start ω
  | n + 1 =>
    match L.run s ω x n with
    | .inr done => .inr done
    | .inl state =>
      if hn : n < T then
        let row := x ⟨n, hn⟩
        let a := L.transition (n + 1) ω state (row, ⟪row, s.val⟫)
        if a.1 then .inr (n + 1, a.2) else .inl a.2
      else .inl state

def terminal {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ × State M :=
  match L.run s ω x T with
  | .inl state => (T, state)
  | .inr done => done

def estimate {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : UnitSphere d :=
  let a := L.terminal s ω x
  L.output a.1 ω a.2

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) : Prop where
  initialChoice : AEMeasurable L.initialChoice ρ
  transition : ∀ t a, AEMeasurable (fun z : Ω × (Vector d × ℝ) =>
    L.transition t z.1 a z.2) (ρ.prod (observationReference d))
  output : ∀ t a, AEMeasurable (fun ω => L.output t ω a) ρ
  fixed_experiment : ∀ s, AEMeasurable (fun z : Ω × Samples d T =>
    L.estimate s z.1 z.2) (ρ.prod (sampleLaw d T))
  uniform_experiment : AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

def angularError {d : ℕ} (s ŝ : UnitSphere d) : ℝ :=
  Real.arccos ⟪ŝ.val, s.val⟫

def success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  (ρ.prod (sampleLaw d T))
    {z | angularError s (L.estimate s z.1 z.2) ≤ ε}

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}

end Learner

open scoped Topology

end SubsphereRegression
end
end

end OAI


