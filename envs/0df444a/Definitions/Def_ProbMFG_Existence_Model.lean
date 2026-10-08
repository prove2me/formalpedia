-- Prove2me | Definitions.Def_ProbMFG_Existence_Model
-- name    : ProbMFG_Existence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:03.497111+00:00
-- url     : https://prove2.me/theorems/452c379f-2bb9-48a9-887b-67ab5dad560b
-- title:
--   Mean-field game data, Hamiltonian and assumptions (A.1)–(A.7)
-- statement:
--   The state is Euclidean $\mathbb R^d$, the noise is $m$-dimensional, and the unrestricted control is Euclidean $\mathbb R^k$. A model fixes a horizon $T$, initial state $x_0$, constant volatility matrix $\sigma$, affine drift $b(t,x,\mu,a)=b_0(t,\mu)+b_1(t)x+b_2(t)a$, running cost $f$, and terminal cost $g$. Its Hamiltonian and minimizer are
--   $$H(t,x,\mu,y,a)=\langle b(t,x,\mu,a),y\rangle+f(t,x,\mu,a),\qquad \hat a(t,x,\mu,y)\in\operatorname*{argmin}_a H(t,x,\mu,y,a).$$
--   The file defines the gradients from $f$ and $g$, the moment $M_p$, the 2-Wasserstein distance $W_2$, probability measures of finite second moment, bounded measurable flows, and predicates for all seven assumptions (A.1)–(A.7). It also states the strengthened convexity condition (3.28).
--
--   These definitions are the common language for the paper's frozen-flow and self-consistent forward-backward systems.
--
--   **Formalization Note** The state and control use Euclidean norms; the joint norm is Euclidean too. Moments and $W_2$ take values in extended nonnegative reals. Gradients are computed from the costs. The minimizer's fallback value is used only outside the domain where Lemma 2.1 establishes existence. The Giry sigma algebra on measures represents the weak-convergence Borel sigma algebra on probability measures.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2707, §2.1–§3.1, pp. 2707–2713, (2.5), (2.7), (2.11), (A.1)–(A.7); https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

noncomputable section

open Classical

abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Action (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Data of the affine-drift mean-field control model in (2.5), (2.11). -/
structure Model (d m k : ℕ) where
  T : ℝ≥0
  x₀ : State d
  σ : Matrix (Fin d) (Fin m) ℝ
  b₀ : ℝ≥0 → Measure (State d) → State d
  b₁ : ℝ≥0 → State d →L[ℝ] State d
  b₂ : ℝ≥0 → Action k →L[ℝ] State d
  f : ℝ≥0 → State d → Measure (State d) → Action k → ℝ
  g : State d → Measure (State d) → ℝ

variable {d m k : ℕ}

def Model.b (M : Model d m k) (t : ℝ≥0) (x : State d)
    (μ : Measure (State d)) (a : Action k) : State d :=
  M.b₀ t μ + M.b₁ t x + M.b₂ t a

/-- Spatial gradient of the running cost. -/
def Model.dfx (M : Model d m k) (t : ℝ≥0) (x : State d)
    (μ : Measure (State d)) (a : Action k) : State d :=
  gradient (fun z => M.f t z μ a) x

def Model.dfa (M : Model d m k) (t : ℝ≥0) (x : State d)
    (μ : Measure (State d)) (a : Action k) : Action k :=
  gradient (fun z => M.f t x μ z) a

def Model.dgx (M : Model d m k) (x : State d)
    (μ : Measure (State d)) : State d :=
  gradient (fun z => M.g z μ) x

/-- The moment in (2.7), taking values in the extended nonnegative reals. -/
def moment (p : ℕ) (μ : Measure (State d)) : ℝ≥0∞ :=
  (∫⁻ x, ‖x‖ₑ ^ p ∂μ) ^ (1 / (p : ℝ))

def IsP2 (μ : Measure (State d)) : Prop :=
  IsProbabilityMeasure μ ∧ moment 2 μ < ⊤

def W2 (μ ν : Measure (State d)) : ℝ≥0∞ :=
  WassersteinDRO.Duality.wassersteinDistance 2 μ ν

/-- The Hamiltonian (2.5). -/
def Model.H (M : Model d m k) (t : ℝ≥0) (x : State d)
    (μ : Measure (State d)) (y : State d) (a : Action k) : ℝ :=
  inner ℝ (M.b t x μ a) (y) + M.f t x μ a

/-- Formula for the spatial derivative of (2.5) under affine drift. -/
def Model.dxH (M : Model d m k) (t : ℝ≥0) (x : State d)
    (μ : Measure (State d)) (y : State d) (a : Action k) : State d :=
  (M.b₁ t).adjoint y + M.dfx t x μ a

/-- The unique Hamiltonian minimizer where it exists; the otherwise branch is outside
all theorem domains and is never used under (A.1)–(A.2). -/
def Model.alphaHat (M : Model d m k) (t : ℝ≥0) (x : State d)
    (μ : Measure (State d)) (y : State d) : Action k :=
  if h : ∃ a, ∀ a', M.H t x μ y a ≤ M.H t x μ y a' then h.choose else 0

/-- Bounded flow of order two on the paper's time interval. -/
def Model.IsFlow (M : Model d m k) (μ : ℝ≥0 → Measure (State d)) : Prop :=
  Measurable (fun t : {t : ℝ≥0 // t ≤ M.T} => μ t.1) ∧
    (∀ t ≤ M.T, IsProbabilityMeasure (μ t)) ∧
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t ≤ M.T, moment 2 (μ t) ≤ C

/-- (A.1): measurability of the affine drift and boundedness on bounded sets. -/
def Model.A1 (M : Model d m k) : Prop :=
  Measurable (fun t : {t : ℝ≥0 // t ≤ M.T} => M.b₂ t.1) ∧
  (∃ B : ℝ, 0 ≤ B ∧ ∀ t ≤ M.T, ‖M.b₂ t‖ ≤ B) ∧
  Measurable (fun q : {q : ℝ≥0 × State d × Measure (State d) //
      q.1 ≤ M.T ∧ IsP2 q.2.2} => M.b q.1.1 q.1.2.1 q.1.2.2 0) ∧
  ∀ R : ℝ, 0 ≤ R → ∃ B : ℝ, 0 ≤ B ∧
    ∀ t ≤ M.T, ∀ x μ, IsP2 μ → ‖x‖ ≤ R → (moment 2 μ).toReal ≤ R →
      ‖M.b t x μ 0‖ ≤ B

/-- The Euclidean norm on the joint state-control space. -/
def jointNorm (x : State d) (a : Action k) : ℝ :=
  Real.sqrt (‖x‖ ^ 2 + ‖a‖ ^ 2)

/-- (A.2): joint C¹ regularity, uniform Lipschitz derivatives, (2.8), and local bounds. -/
def Model.A2 (M : Model d m k) (lam cL : ℝ) : Prop :=
  Measurable (fun q : {t : ℝ≥0 // t ≤ M.T} × State d ×
      {μ : Measure (State d) // IsP2 μ} × Action k =>
    M.f q.1.1 q.2.1 q.2.2.1.1 q.2.2.2) ∧
  (∀ t ≤ M.T, ∀ μ, IsP2 μ →
    ContDiff ℝ 1 (fun z : State d × Action k => M.f t z.1 μ z.2)) ∧
  (∀ t ≤ M.T, ∀ μ, IsP2 μ → ∀ x x' : State d, ∀ a a' : Action k,
    jointNorm (M.dfx t x' μ a' - M.dfx t x μ a)
      (M.dfa t x' μ a' - M.dfa t x μ a) ≤
        cL * jointNorm (x' - x) (a' - a)) ∧
  (∀ t ≤ M.T, ∀ μ, IsP2 μ → ∀ x x' : State d, ∀ a a' : Action k,
    lam * ‖a' - a‖ ^ 2 ≤
      M.f t x' μ a' - M.f t x μ a -
        (inner ℝ (x' - x) (M.dfx t x μ a) + inner ℝ (a' - a) (M.dfa t x μ a))) ∧
  (∀ R : ℝ, 0 ≤ R → ∃ B : ℝ, 0 ≤ B ∧
    ∀ t ≤ M.T, ∀ μ, IsP2 μ → (moment 2 μ).toReal ≤ R →
      ∀ x : State d, ‖x‖ ≤ R → ∀ a : Action k, ‖a‖ ≤ R →
        |M.f t x μ a| ≤ B ∧ ‖M.dfx t x μ a‖ ≤ B ∧ ‖M.dfa t x μ a‖ ≤ B)

/-- (A.3), including the affine form already fixed in `Model`. -/
def Model.A3 (M : Model d m k) : Prop :=
  (∀ R : ℝ, 0 ≤ R → ∃ B : ℝ, 0 ≤ B ∧
    ∀ t ≤ M.T, ∀ μ, IsP2 μ → (moment 2 μ).toReal ≤ R → ‖M.b₀ t μ‖ ≤ B) ∧
  ∃ B : ℝ, 0 ≤ B ∧ ∀ t ≤ M.T, ‖M.b₁ t‖ ≤ B

/-- (A.4): local boundedness, C¹ convexity, and cL-Lipschitz gradient of g. -/
def Model.A4 (M : Model d m k) (cL : ℝ) : Prop :=
  Measurable (fun q : State d × {μ : Measure (State d) // IsP2 μ} =>
    M.g q.1 q.2.1) ∧
  (∀ R : ℝ, 0 ≤ R → ∃ B : ℝ, 0 ≤ B ∧
    ∀ μ, IsP2 μ → (moment 2 μ).toReal ≤ R →
      ∀ x : State d, ‖x‖ ≤ R → |M.g x μ| ≤ B) ∧
  (∀ μ, IsP2 μ → ContDiff ℝ 1 (fun x => M.g x μ) ∧
    ConvexOn ℝ Set.univ (fun x => M.g x μ) ∧
    ∀ x x' : State d, ‖M.dgx x' μ - M.dgx x μ‖ ≤ cL * ‖x' - x‖)

/-- (A.5), read as separate inequalities for f and g. -/
def Model.A5 (M : Model d m k) (cL : ℝ) : Prop :=
  (∀ t ≤ M.T, |M.f t 0 (Measure.dirac 0) 0| ≤ cL ∧
    ‖M.dfx t 0 (Measure.dirac 0) 0‖ ≤ cL ∧
    ‖M.dfa t 0 (Measure.dirac 0) 0‖ ≤ cL) ∧
  (∀ t ≤ M.T, ∀ μ μ', IsP2 μ → IsP2 μ' →
    ∀ x x' : State d, ∀ a a' : Action k,
      |M.f t x' μ' a' - M.f t x μ a| ≤
        cL * (1 + jointNorm x' a' + jointNorm x a +
          (moment 2 μ).toReal + (moment 2 μ').toReal) *
          (jointNorm (x' - x) (a' - a) + (W2 μ' μ).toReal)) ∧
  (∀ μ μ', IsP2 μ → IsP2 μ' → ∀ x x' : State d,
      |M.g x' μ' - M.g x μ| ≤
        cL * (1 + ‖x'‖ + ‖x‖ + (moment 2 μ).toReal + (moment 2 μ').toReal) *
          (‖x' - x‖ + (W2 μ' μ).toReal)) ∧
  (∀ t ≤ M.T, ‖M.b₁ t‖ ≤ cL ∧ ‖M.b₂ t‖ ≤ cL ∧
    ∀ μ, IsP2 μ → ‖M.b₀ t μ‖ ≤ cL) ∧
  (∀ t ≤ M.T, ∀ μ μ', IsP2 μ → IsP2 μ' →
    ‖M.b₀ t μ' - M.b₀ t μ‖ ≤ cL * (W2 μ μ').toReal)

/-- (A.6). -/
def Model.A6 (M : Model d m k) (cL : ℝ) : Prop :=
  ∀ t ≤ M.T, ∀ x μ, IsP2 μ → ‖M.dfa t x μ 0‖ ≤ cL

/-- (A.7), with the Dirac mass at x. -/
def Model.A7 (M : Model d m k) (cL : ℝ) : Prop :=
  ∀ t ≤ M.T, ∀ x : State d,
    -cL * (1 + ‖x‖) ≤ inner ℝ (x) (M.dfx t 0 (Measure.dirac x) 0) ∧
    -cL * (1 + ‖x‖) ≤ inner ℝ (x) (M.dgx 0 (Measure.dirac x))

def Model.Assumptions (M : Model d m k) (lam cL : ℝ) : Prop :=
  0 < lam ∧ 0 < cL ∧ M.A1 ∧ M.A2 lam cL ∧ M.A3 ∧ M.A4 cL ∧
    M.A5 cL ∧ M.A6 cL ∧ M.A7 cL

/-- The strengthened convexity condition (3.28). -/
def Model.StronglyConvexX (M : Model d m k) (lam γ : ℝ) : Prop :=
  0 < γ ∧
  (∀ t ≤ M.T, ∀ μ, IsP2 μ → ∀ x x' : State d, ∀ a a' : Action k,
    γ * ‖x' - x‖ ^ 2 + lam * ‖a' - a‖ ^ 2 ≤
      M.f t x' μ a' - M.f t x μ a -
        (inner ℝ (x' - x) (M.dfx t x μ a) + inner ℝ (a' - a) (M.dfa t x μ a))) ∧
  (∀ μ, IsP2 μ → ∀ x x' : State d,
    γ * ‖x' - x‖ ^ 2 ≤
      M.g x' μ - M.g x μ - inner ℝ (x' - x) (M.dgx x μ))

end
end ProbMFG.Existence


