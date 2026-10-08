-- Prove2me | Definitions.Def_ConservativeAD_AutoDiff_ConservativeMap
-- name    : ConservativeAD_AutoDiff_ConservativeMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:37:46.312984+00:00
-- url     : https://prove2.me/theorems/14706803-5f3f-4c4a-9128-7c516d354855
-- title:
--   Definition 4: conservative mappings $J_F:\mathbb R^n\rightrightarrows\mathbb R^{m\times n}$ and the chain-rule property (5)
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^m$ (in the paper, a locally Lipschitz function). A set-valued map $J_F:\mathbb R^n\rightrightarrows\mathbb R^{m\times n}$ is a **conservative mapping** for $F$ if for every absolutely continuous curve $\gamma:[0,1]\to\mathbb R^n$, for almost every $t\in[0,1]$, the curve $t\mapsto F(\gamma(t))$ is differentiable at $t$ and
--
--   $$
--   \frac{d}{dt}F(\gamma(t))=V\dot\gamma(t)\qquad\text{for all } V\in J_F(\gamma(t)).
--   $$
--
--   For a scalar function $f:\mathbb R^n\to\mathbb R$ and $D:\mathbb R^n\rightrightarrows\mathbb R^n$, the **chain-rule property (5)** says: for every absolutely continuous curve $x:[0,1]\to\mathbb R^n$, for almost every $t\in[0,1]$, $t\mapsto f(x(t))$ is differentiable at $t$ and
--
--   $$
--   \frac{d}{dt}f(x(t))=\langle v,\dot x(t)\rangle\qquad\text{for all } v\in D(x(t)).
--   $$
--
--   Conservative mappings are the vector-valued counterpart of conservative fields, defined through the chain rule; they are the generalized Jacobians composed by automatic differentiation.
--
--   **Formalization Note** Differentiability is asserted with `HasDerivAt`, not with an equation for `deriv`: Lean's `deriv` is $0$ at points of non-differentiability, so an equation `deriv (F ∘ γ) t = …` would hold vacuously there. Definition 4 imposes neither closed graph nor nonempty values on $J_F$, and neither does the Lean definition. Local Lipschitz continuity of $F$, a standing assumption of Definition 4, is carried as a hypothesis by the theorems that use the definition. Matrices act on `EuclideanSpace` vectors through `WithLp.ofLp`/`WithLp.toLp`.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 12, Definition 4; p. 8, Lemma 2, eq. (5)

import Mathlib
open MeasureTheory

namespace ConservativeAD.AutoDiff

/-- Definition 4 (conservative mapping). For `F : ℝ^n → ℝ^m` (the definition is used for locally
Lipschitz `F`), a set-valued map `J : ℝ^n ⇒ ℝ^{m×n}` is a conservative mapping for `F` if for
every absolutely continuous curve `γ : [0, 1] → ℝ^n`, for almost every `t ∈ [0, 1]`, the curve
`F ∘ γ` is differentiable at `t` with derivative `V γ̇(t)` for every `V ∈ J (γ t)`. -/
def IsConservativeMap {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (J : EuclideanSpace ℝ (Fin n) → Set (Matrix (Fin m) (Fin n) ℝ)) : Prop :=
  ∀ γ : ℝ → EuclideanSpace ℝ (Fin n), AbsolutelyContinuousOnInterval γ 0 1 →
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)), ∀ V ∈ J (γ t),
      HasDerivAt (fun s => F (γ s)) (WithLp.toLp 2 (V.mulVec (WithLp.ofLp (deriv γ t)))) t

/-- The chain-rule property (5) of Lemma 2 for a set-valued map `D : ℝ^n ⇒ ℝ^n` and a function
`f : ℝ^n → ℝ`: for every absolutely continuous curve `x : [0, 1] → ℝ^n`, for almost every
`t ∈ [0, 1]`, `t ↦ f(x(t))` is differentiable at `t` with derivative `⟨v, ẋ(t)⟩` for every
`v ∈ D(x(t))`. -/
def HasChainRule {n : ℕ} (D : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ γ : ℝ → EuclideanSpace ℝ (Fin n), AbsolutelyContinuousOnInterval γ 0 1 →
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) 1)), ∀ v ∈ D (γ t),
      HasDerivAt (fun s => f (γ s)) (inner ℝ v (deriv γ t)) t

end ConservativeAD.AutoDiff


