-- Prove2me | Definitions.Def_PeskirShiryaev_General_StoppingProblem
-- name    : PeskirShiryaev_General_StoppingProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:24:31.685397+00:00
-- url     : https://prove2.me/theorems/104240b4-92ac-4bf7-8a10-fb3bd3cbd194
-- title:
--   Equations (2.2.1)–(2.2.7) — value, contact time, and superharmonic majorants
-- statement:
--   Let $X$ be the strong Markov process above and let $G:E\to\mathbb R$ be measurable. The standing gain condition is
--   $$E_x\!\left[\sup_{t\ge0}|G(X_t)|\right]<\infty\qquad(x\in E).$$
--   At state $x$, admissible rules are all stopping times for the given filtration that are finite $P_x$-almost surely. Define the value independently of any candidate solution by
--   $$V(x)=\sup_{\tau\text{ admissible at }x}E_xG(X_\tau).$$
--   A rule is optimal when it is admissible at every initial state and attains this value there. A measurable real function $F$ is superharmonic when $F(X_\sigma)$ is integrable and $E_xF(X_\sigma)\le F(x)$ for every admissible stopping time $\sigma$ and initial state $x$. It is the smallest superharmonic majorant of $G$ when it dominates $G$ and lies below every other such majorant.
--
--   For any state set $D$, define $\tau_D=\inf\{t\ge0:X_t\in D\}$, with $\inf\varnothing=\infty$. The contact time of $F$ and $G$ uses $D=\{F=G\}$. The stopped value process is $F(X_{t\wedge\tau})$.
--
--   These definitions separate expected-reward optimization from the majorant characterization that the theorems establish.
--
--   **Formalization Note** The absolute-gain supremum and its integral take values in $[0,\infty]$; its almost-everywhere measurability is explicit. Values and finite expectations are real. The gain condition and adapted right-continuous process ensure integrability of every admissible stopped reward and boundedness of the nonempty reward set. A reward at infinity is assigned zero only to totalize the function on a null event. Optimality explicitly includes integrability, and no value or majorant identity is assumed in the definitions.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 35–37 (PDF 55–57), Eqs. (2.2.1)–(2.2.7), Definition 2.3.

import Definitions.Def_PeskirShiryaev_General_MarkovModel

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/- Imported Lean declarations, reproduced for self-contained code review:
namespace PeskirShiryaev.General

abbrev State (d : ℕ) := Fin d → ℝ


def RightContinuousPaths {Ω A : Type*} [TopologicalSpace A]
    (Y : ℝ≥0 → Ω → A) (ω : Ω) : Prop :=
  ∀ t, ContinuousWithinAt (fun s => Y s ω) (Ici t) t


structure MarkovModel (d : ℕ) (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  dimension_pos : 0 < d
  P : State d → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (P x)
  measurable_laws : ∀ A : Set Ω, MeasurableSet A → Measurable (fun x => P x A)
  filtration : Filtration ℝ≥0 mΩ
  filtration_rightContinuous : filtration.IsRightContinuous
  X : ℝ≥0 → Ω → State d
  adapted : Adapted filtration X
  starts : ∀ x, ∀ᵐ ω ∂P x, X 0 ω = x
  rightContinuous : ∀ ω, RightContinuousPaths X ω
  strongMarkov : ∀ (x : State d) (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime filtration τ),
    (∀ᵐ ω ∂P x, τ ω < ⊤) →
    ∀ (s : ℝ≥0) (f : State d → ℝ), Measurable f →
      Bornology.IsBounded (Set.range f) →
      (P x)[fun ω => f (X ((τ ω).toNNReal + s) ω) | hτ.measurableSpace]
        =ᵐ[P x] (fun ω => ∫ ω', f (X s ω') ∂P (X (τ ω).toNNReal ω))
  leftContinuous_stopping : ∀ (x : State d) (τ : Ω → ℝ≥0∞)
    (τn : ℕ → Ω → ℝ≥0∞),
    IsStoppingTime filtration τ →
    (∀ n, IsStoppingTime filtration (τn n)) →
    (∀ ω, Monotone (fun n => τn n ω)) →
    (∀ᵐ ω ∂P x, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) →
    ∀ᵐ ω ∂P x, τ ω < ⊤ →
      Tendsto (fun n => X (τn n ω).toNNReal ω) atTop (𝓝 (X (τ ω).toNNReal ω))

end PeskirShiryaev.General
-/

namespace PeskirShiryaev.General

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Admissibility at initial state x includes almost-sure finiteness. -/
def Admissible (M : MarkovModel d Ω) (x : State d) (τ : Ω → ℝ≥0∞) : Prop :=
  IsStoppingTime M.filtration τ ∧ ∀ᵐ ω ∂M.P x, τ ω < ⊤

/-- Equation (2.2.1), without taking a real supremum of an unbounded set. -/
noncomputable def gainSup (M : MarkovModel d Ω) (G : State d → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, ENNReal.ofReal |G (M.X t ω)|

def GainIntegrable (M : MarkovModel d Ω) (G : State d → ℝ) : Prop :=
  Measurable G ∧ ∀ x, AEMeasurable (gainSup M G) (M.P x) ∧
    (∫⁻ ω, gainSup M G ω ∂M.P x) < ⊤

/-- The arbitrary value on the null event τ = ∞ is never used for admissible τ. -/
noncomputable def reward (M : MarkovModel d Ω) (G : State d → ℝ)
    (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ :=
  if τ ω = ⊤ then 0 else G (M.X (τ ω).toNNReal ω)

/-- Equation (2.2.3). Stopping at zero makes the set nonempty; (2.2.1)
bounds it. No optimum or majorant is built into this definition. -/
noncomputable def value (M : MarkovModel d Ω) (G : State d → ℝ) (x : State d) : ℝ :=
  sSup {r : ℝ | ∃ τ : Ω → ℝ≥0∞, Admissible M x τ ∧ r = ∫ ω, reward M G τ ω ∂M.P x}

def Optimal (M : MarkovModel d Ω) (G : State d → ℝ) (τ : Ω → ℝ≥0∞) : Prop :=
  ∀ x, Admissible M x τ ∧ Integrable (reward M G τ) (M.P x) ∧
    (∫ ω, reward M G τ ω ∂M.P x) = value M G x

/-- Definition 2.3: every stopped expectation is finite, not a default integral. -/
def Superharmonic (M : MarkovModel d Ω) (F : State d → ℝ) : Prop :=
  Measurable F ∧ ∀ (x : State d) (σ : Ω → ℝ≥0∞), Admissible M x σ →
    Integrable (reward M F σ) (M.P x) ∧ (∫ ω, reward M F σ ω ∂M.P x) ≤ F x

def LeastMajorant (M : MarkovModel d Ω) (G F : State d → ℝ) : Prop :=
  Superharmonic M F ∧ (∀ x, G x ≤ F x) ∧
    ∀ H : State d → ℝ, Superharmonic M H → (∀ x, G x ≤ H x) → ∀ x, F x ≤ H x

/-- Equation (2.2.6). Infimum in [0,∞] makes no contact mean ∞. -/
noncomputable def entryTime (M : MarkovModel d Ω) (D : Set (State d)) (ω : Ω) : ℝ≥0∞ :=
  ⨅ t : {t : ℝ≥0 // M.X t ω ∈ D}, (t.val : ℝ≥0∞)

noncomputable def contactTime (M : MarkovModel d Ω) (G F : State d → ℝ) : Ω → ℝ≥0∞ :=
  entryTime M {x | F x = G x}

noncomputable def stoppedValue (M : MarkovModel d Ω) (F : State d → ℝ)
    (τ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ :=
  F (M.X (min (t : ℝ≥0∞) (τ ω)).toNNReal ω)

end PeskirShiryaev.General


