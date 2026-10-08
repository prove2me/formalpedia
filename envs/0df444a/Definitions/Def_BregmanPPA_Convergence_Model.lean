-- Prove2me | Definitions.Def_BregmanPPA_Convergence_Model
-- name    : BregmanPPA_Convergence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:58:29.443977+00:00
-- url     : https://prove2.me/theorems/e69076f8-06c2-4311-bba4-8d4a59ee25a1
-- title:
--   Definition 1 — Bregman functions and the proximal-point recursion
-- statement:
--   Let $H$ be a finite-dimensional real inner-product space and let $S\subseteq H$ be open. For a real function $h$, its **Bregman distance** (1) is
--
--   $$D_h(x,y)=h(x)-h(y)-\langle\nabla h(y),x-y\rangle,\qquad x\in\overline S,\ y\in S.$$
--
--   **Definition 1** calls $h$ a Bregman function with zone $S$ when it is continuously differentiable on $S$, strictly convex and continuous on $\overline S$, and satisfies the following conditions: both partial sublevel sets $\{x\in\overline S:D_h(x,y)\le\alpha\}$ and $\{y\in S:D_h(x,y)\le\alpha\}$ are bounded for the indicated fixed arguments; if $y^k\in S$ converges to $y^*$, then $D_h(y^*,y^k)\to0$; and if $y^k\in S$ converges to $y^*\in\overline S$, $x^k\in\overline S$ is bounded, and $D_h(x^k,y^k)\to0$, then $x^k\to y^*$.
--
--   For a set-valued operator $T$, this file also defines its subdifferential realization $\partial f$ and a **Bregman proximal-point run**: a sequence $(x^k)$ in $S$ satisfying
--
--   $$\frac{\nabla h(x^k)-\nabla h(x^{k+1})}{c_k}\in T(x^{k+1})\qquad(k\ge0).$$
--
--   These definitions are the shared setting for Lemma 1 and Theorem 1.
--
--   **Formalization Note** The total Lean function $h$ is constrained only on $\overline S$, and its gradient is used only on $S$. Recursion (3) is represented by its equivalent inclusion (4), as stated on p. 207. In condition (vi), $x^k\in\overline S$ is explicit because $D_h$ has natural domain $\overline S\times S$.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 202, 205–207, display (1), Definition 1, displays (3)–(4), https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InertialFB_IFB_ConvexAnalysis

open ThreeOpSplitting.Convergence InertialFB.IFB Filter Topology

namespace BregmanPPA.Convergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The D-function (1), evaluated with its second argument in the zone of h. -/
noncomputable def bregmanD (h : H → ℝ) (x y : H) : ℝ :=
  h x - h y - inner ℝ (gradient h y) (x - y)

/-- Definition 1: a Bregman function with open zone S. -/
structure IsBregmanFunction (S : Set H) (h : H → ℝ) : Prop where
  isOpen : IsOpen S
  contDiffOn : ContDiffOn ℝ 1 h S
  strictConvexOn : StrictConvexOn ℝ (closure S) h
  continuousOn : ContinuousOn h (closure S)
  bounded_L₁ : ∀ (α : ℝ) (y : H), y ∈ S →
    Bornology.IsBounded {x | x ∈ closure S ∧ bregmanD h x y ≤ α}
  bounded_L₂ : ∀ (α : ℝ) (x : H), x ∈ closure S →
    Bornology.IsBounded {y | y ∈ S ∧ bregmanD h x y ≤ α}
  tendsto_zero : ∀ (y : ℕ → H) (y' : H), (∀ k, y k ∈ S) → Tendsto y atTop (𝓝 y') →
    Tendsto (fun k => bregmanD h y' (y k)) atTop (𝓝 0)
  tendsto_of_zero : ∀ (x y : ℕ → H) (y' : H), (∀ k, x k ∈ closure S) →
    (∀ k, y k ∈ S) → Tendsto y atTop (𝓝 y') → y' ∈ closure S →
    Bornology.IsBounded (Set.range x) →
    Tendsto (fun k => bregmanD h (x k) (y k)) atTop (𝓝 0) → Tendsto x atTop (𝓝 y')

/-- The subdifferential operator of an extended-real convex function. -/
def subdiffOp (f : H → EReal) : H → Set H := fun x => {g | IsSubgradient f x g}

/-- Recursion (3), stated through equivalent inclusion (4), for all k ≥ 0. -/
noncomputable def IsBregmanPPARun (S : Set H) (h : H → ℝ) (T : H → Set H)
    (c : ℕ → ℝ) (x : ℕ → H) : Prop :=
  ∀ k, x k ∈ S ∧ (c k)⁻¹ • (gradient h (x k) - gradient h (x (k + 1))) ∈ T (x (k + 1))

end BregmanPPA.Convergence


