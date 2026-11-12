-- Prove2me | Definitions.Def_FreeProbAMP_StateEvolution_Iteration
-- name    : FreeProbAMP_StateEvolution_Iteration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:24:51.439455+00:00
-- url     : https://prove2.me/theorems/1f6fdc94-ee56-4fff-b534-5cc582c3cdcc
-- title:
--   The actual vector–matrix AMP recursion and its input data
-- statement:
--   Fix deterministic coefficients $a_{t,s}$ and scalar maps $g_t:\mathbb R^{t+1}\to\mathbb R$. Starting at $u^0$, compute in order
--
--   $$m_i^t=g_t(u_i^0,\ldots,u_i^t),\quad d_{t,r}=\frac1n\sum_i\partial_r g_t(u_i^0,\ldots,u_i^t),$$
--   $$V^t=A(m^t)-\alpha_d\sum_{r=0}^t d_{t,r}M^{r-1},\quad
--   M^t=\sum_{s=0}^t a_{t,s}V^s,\quad
--   u^{t+1}=A^*M^t-\sum_{r=0}^t a_{t,r}m^r.$$
--
--   In the last display $u^{t+1}$ is the next vector iterate. The boundary is $M^{-1}=V^{-1}=0$. The term with derivative index zero multiplies the separately specified zero boundary.
--
--   Coefficient admissibility means that some $0<a_*<a^*<\infty$ satisfy $|a_{t,t}|\ge a_*$ and $|a_{t,s}|<a^*$ through the fixed horizon. Regular maps are $C^1$ with each map and all its first derivatives pseudo-Lipschitz of a finite order, allowed to depend on time. Last-coordinate linearity requires $g_0$ nowhere zero and $g_t(x_{<t},x_t)=r_t(x_{<t})+c_t(x_{<t})x_t$ with measurable $r_t,c_t$ and $c_t>0$. The slope need not have a uniform positive lower bound.
--
--   Finite input data include a probability measure, arbitrary positive sample sizes $n(d)$, the Gaussian input array, initialization and scalar parameters. The trajectory is computed by recursion, and a terminal map is evaluated without feeding its value back. No state-evolution conclusion is part of these data.
--
--   **Formalization Note** The iteration state retains histories for a direct finite recursion. Unused future coefficients and maps are unrestricted total extensions. The dimension index $d$ represents every positive physical dimension $d+1$.
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), pp. 2–3, (1.4)–(1.8), Assumptions 2.1–2.5

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_Matrices

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

abbrev ScalarMaps := (t : ℕ) → (Fin (t+1) → ℝ) → ℝ

/-- Finite-horizon assumptions 2.3 and 2.4. -/
def Coefficients (T : ℕ) (a : ℕ → ℕ → ℝ) : Prop :=
  ∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ ∀ t, t ≤ T →
    lo ≤ |a t t| ∧ ∀ s, s ≤ t → |a t s| < hi

def RegularMaps (T : ℕ) (g : ScalarMaps) : Prop := ∀ t, t ≤ T → SmoothPL (g t)

/-- Assumption 2.5; the slope need not be uniformly bounded away from zero. -/
def LastLinear (T : ℕ) (g : ScalarMaps) : Prop :=
  (∀ x, g 0 x ≠ 0) ∧ ∀ t, 1 ≤ t → t ≤ T →
    ∃ r c : (Fin t → ℝ) → ℝ, Measurable r ∧ Measurable c ∧
      (∀ x, 0 < c x) ∧ ∀ x, g t x = r (fun j => x j.castSucc) +
        c (fun j => x j.castSucc) * x (Fin.last t)

structure IterationState (n d : ℕ) where
  u : ℕ → Fin n → ℝ
  m : ℕ → Fin n → ℝ
  V : ℕ → RMat d
  M : ℕ → RMat d

def initialState {n d : ℕ} (u₀ : Fin n → ℝ) : IterationState n d :=
  ⟨fun t => if t=0 then u₀ else 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- One actual step of (1.4)–(1.6), with M^{-1}=0 as a genuine separate case. -/
def advance {n d : ℕ} (A : Fin n → RMat d) (a : ℕ → ℕ → ℝ)
    (g : ScalarMaps) (t : ℕ) (s : IterationState n d) : IterationState n d :=
  let inputs := fun i (r : Fin (t+1)) => s.u r i
  let msg := fun i => g t (inputs i)
  let deriv := fun (r : Fin (t+1)) => avg n (fun i => derivCoord (g t) r (inputs i))
  let v := applyA A msg - aspect n d • ∑ r : Fin (t+1),
    deriv r • (if r.val=0 then 0 else s.M (r.val-1))
  let mat := ∑ r : Fin (t+1), a t r • (if r.val=t then v else s.V r)
  let next := applyAdj A mat - ∑ r : Fin (t+1), a t r •
    (if r.val=t then msg else s.m r)
  ⟨Function.update s.u (t+1) next, Function.update s.m t msg,
    Function.update s.V t v, Function.update s.M t mat⟩

def run {n d : ℕ} (A : Fin n → RMat d) (a : ℕ → ℕ → ℝ)
    (g : ScalarMaps) (u₀ : Fin n → ℝ) : ℕ → IterationState n d
  | 0 => initialState u₀
  | t+1 => advance A a g t (run A a g u₀ t)

def uIter {n d : ℕ} (A : Fin n → RMat d) (a : ℕ → ℕ → ℝ)
    (g : ScalarMaps) (u₀ : Fin n → ℝ) (t : ℕ) : Fin n → ℝ := (run A a g u₀ t).u t

def mIter {n d : ℕ} (A : Fin n → RMat d) (a : ℕ → ℕ → ℝ)
    (g : ScalarMaps) (u₀ : Fin n → ℝ) (t : ℕ) : Fin n → ℝ := (run A a g u₀ (t+1)).m t

def vIter {n d : ℕ} (A : Fin n → RMat d) (a : ℕ → ℕ → ℝ)
    (g : ScalarMaps) (u₀ : Fin n → ℝ) (t : ℕ) : RMat d := (run A a g u₀ (t+1)).V t

def matIter {n d : ℕ} (A : Fin n → RMat d) (a : ℕ → ℕ → ℝ)
    (g : ScalarMaps) (u₀ : Fin n → ℝ) (t : ℕ) : RMat d := (run A a g u₀ (t+1)).M t

/-- All finite-size data. The dimension index d denotes physical dimension d+1. -/
structure FiniteData (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  n : ℕ → ℕ
  n_pos : ∀ d, 0 < n d
  A : (d : ℕ) → Ω → Fin (n d) → RMat (d+1)
  u₀ : (d : ℕ) → Ω → Fin (n d) → ℝ
  a : ℕ → ℕ → ℝ
  g : ScalarMaps

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FiniteData

def u (D : FiniteData Ω) (t d : ℕ) (ω : Ω) := uIter (D.A d ω) D.a D.g (D.u₀ d ω) t
def m (D : FiniteData Ω) (t d : ℕ) (ω : Ω) := mIter (D.A d ω) D.a D.g (D.u₀ d ω) t
def V (D : FiniteData Ω) (t d : ℕ) (ω : Ω) := vIter (D.A d ω) D.a D.g (D.u₀ d ω) t
def M (D : FiniteData Ω) (t d : ℕ) (ω : Ω) := matIter (D.A d ω) D.a D.g (D.u₀ d ω) t
def α (D : FiniteData Ω) (d : ℕ) := aspect (D.n d) (d+1)
def inputs (D : FiniteData Ω) (t d : ℕ) (ω : Ω) (i : Fin (D.n d)) : Fin (t+1) → ℝ :=
  fun r => D.u r d ω i

def terminal (D : FiniteData Ω) {T : ℕ} (h : (Fin (T+1) → ℝ) → ℝ) (d : ℕ) (ω : Ω) :=
  fun i => h (D.inputs T d ω i)

end FiniteData

end FreeProbAMP.StateEvolution


