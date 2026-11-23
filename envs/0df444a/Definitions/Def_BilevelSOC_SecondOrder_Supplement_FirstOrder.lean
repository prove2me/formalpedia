-- Prove2me | Definitions.Def_BilevelSOC_SecondOrder_Supplement_FirstOrder
-- name    : BilevelSOC_SecondOrder_Supplement_FirstOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:34:06.64013+00:00
-- url     : https://prove2.me/theorems/d7f62239-7666-4f55-b496-80f0db005766
-- title:
--   §2.3–2.4 — extended-real directional limits, local Lipschitzness, growth and strict minima
-- statement:
--   Let $V,W$ be real normed spaces. Upper and lower Dini derivatives of an extended-real function $h$ are the positive-step limit superior and limit inferior of its directional quotient. The ordinary and Hadamard derivatives are specified by their actual limits, permitting extended-real derivative values. For real functions, Clarke's derivative varies both the base point and positive step, and Clarke regularity requires existence of the ordinary derivative and equality to the Clarke derivative in every direction:
--
--   $$h^\circ(x;d)=\limsup_{a\to x,\ t\downarrow0}\frac{h(a+td)-h(a)}t,\qquad h'(x;d)=h^\circ(x;d).$$
--
--   The Clarke subdifferential is the set of continuous covectors bounded by this derivative in every direction. The polar of a covector set consists of directions on which every covector is nonpositive. Vector directional derivatives use positive steps. Local Lipschitzness means Lipschitzness on a neighborhood; for extended-real functions this includes a locally equal finite real representative. First-order extended-real growth uses an existential $C>0$ and neighborhood, with $h(x)+C\|a-x\|\le h(a)$ at every nearby feasible $a$. Strict local minimality compares every distinct nearby feasible point. These general definitions support all the new criteria.
--
--   **Formalization Note** The limit superior and inferior take values in the complete lattice `EReal`. No arbitrary default limit is used. Real Clarke objects are applied only to locally finite real representatives. Continuous covectors stand for Euclidean vectors through the Riesz identification. The abstract normed-space definitions specialize to the paper's finite-dimensional spaces.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, pp. 3–4, 6–10, 12–17, §2.3–2.4

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
open Filter
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
/-- Lipschitz on some neighborhood, with no prescribed modulus. -/
def LocallyLipschitzAt (h : V → W) (x : V) : Prop :=
  ∃ U ∈ 𝓝 x, ∃ K : NNReal, LipschitzOnWith K h U
/-- Extended-real local Lipschitzness includes local finiteness. -/
def ELocallyLipschitzAt (h : V → EReal) (x : V) : Prop :=
  ∃ r : V → ℝ, ∃ U ∈ 𝓝 x, (∀ a ∈ U, h a = (r a : EReal)) ∧
    ∃ K : NNReal, LipschitzOnWith K r U
noncomputable def dirQuot (h : V → EReal) (x d : V) (t : ℝ) : EReal :=
  ((t⁻¹ : ℝ) : EReal) * (h (x + t • d) - h x)
noncomputable def upperDini (h : V → EReal) (x d : V) : EReal :=
  Filter.limsup (dirQuot h x d) (𝓝[>] (0 : ℝ))
noncomputable def lowerDini (h : V → EReal) (x d : V) : EReal :=
  Filter.liminf (dirQuot h x d) (𝓝[>] (0 : ℝ))
def HasEDirDerivAt (h : V → EReal) (x d : V) (v : EReal) : Prop :=
  Tendsto (dirQuot h x d) (𝓝[>] (0 : ℝ)) (𝓝 v)
def HasEHadamardDirDerivAt (h : V → EReal) (x d : V) (v : EReal) : Prop :=
  Tendsto (fun r : ℝ × V => dirQuot h x r.2 r.1)
    ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 d) (𝓝 v)
def EGrowthCondition (h : V → EReal) (X : Set V) (x : V) : Prop :=
  x ∈ X ∧ ∃ U ∈ 𝓝 x, ∃ C : ℝ, 0 < C ∧
    ∀ a ∈ X ∩ U, h x + ((C * ‖a - x‖ : ℝ) : EReal) ≤ h a
def StrictLocalMin (h : V → ℝ) (X : Set V) (x : V) : Prop :=
  x ∈ X ∧ ∃ U ∈ 𝓝 x, ∀ a ∈ X ∩ U, a ≠ x → h x < h a
noncomputable def clarkeDeriv (h : V → ℝ) (x d : V) : EReal :=
  Filter.limsup
    (fun r : V × ℝ => (((h (r.1 + r.2 • d) - h r.1) / r.2 : ℝ) : EReal))
    ((𝓝 x) ×ˢ (𝓝[>] (0 : ℝ)))
def ClarkeRegularAt (h : V → ℝ) (x : V) : Prop :=
  ∀ d, ∃ v : ℝ, HasDirDerivAt h x d v ∧ clarkeDeriv h x d = (v : EReal)
def clarkeSubdiff (h : V → ℝ) (x : V) : Set (V →L[ℝ] ℝ) :=
  {ξ | ∀ d, (ξ d : EReal) ≤ clarkeDeriv h x d}
def dualPolar (Q : Set (V →L[ℝ] ℝ)) : Set V :=
  {d | ∀ ξ ∈ Q, ξ d ≤ 0}
def HasVectorDirDerivAt (s : V → W) (x d : V) (v : W) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (s (x + t • d) - s x))
    (𝓝[>] (0 : ℝ)) (𝓝 v)
end BilevelSOC.SecondOrder.Supplement


