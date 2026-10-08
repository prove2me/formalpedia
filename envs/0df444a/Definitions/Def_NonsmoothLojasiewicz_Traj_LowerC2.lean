-- Prove2me | Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
-- name    : NonsmoothLojasiewicz_Traj_LowerC2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:10:32.602854+00:00
-- url     : https://prove2.me/theorems/329b5806-a23e-420e-8848-f32127a82dc4
-- title:
--   Lower-$C^2$ functions
-- statement:
--   A function $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ is **lower-$C^2$** if for every $x_0\in\operatorname{dom} f$ there exist an open neighbourhood $U$ of $x_0$, a compact topological space $S$ and a jointly continuous function $F:U\times S\to\mathbb R$ such that
--   $$f(x)=\max_{s\in S}F(x,s)\qquad\text{for all }x\in U,$$
--   and such that the partial derivatives $\nabla_xF(\cdot,\cdot)$ and $\nabla_x^2F(\cdot,\cdot)$ exist and are jointly continuous on $U\times S$.
--
--   Lower-$C^2$ functions with full domain form one of the two branches of the standing assumption $(\mathcal H1)$ of Section 4; the other branch is lower semicontinuous convex functions.
--
--   **Formalization Note** The maximum is required to be attained at every $x\in U$ (which forces $S\neq\emptyset$). The first and second partial derivatives are Fréchet derivatives of $F(\cdot,s)$ at each $x\in U$, given as functions $DF$, $D^2F$ on $U\times S$ that are required to be jointly continuous. The neighbourhood is taken open, which loses nothing, and $S$ ranges over topological spaces in the lowest universe, a harmless restriction.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, p. 1217, Section 4, definition of lower-C2 (recalled from Rockafellar–Wets, Variational Analysis, Definition 10.29)

import Mathlib

namespace NonsmoothLojasiewicz.Traj

/-- Lower-`C²` functions (p. 1217, recalling Rockafellar–Wets, Definition 10.29): for every
`x₀ ∈ dom f` there are an open neighbourhood `U` of `x₀`, a compact topological space `S` and a
jointly continuous `F : U × S → ℝ` with `f(x) = max_{s ∈ S} F(x, s)` for all `x ∈ U`, such that the
partial derivatives `∇ₓF(·,·)` and `∇²ₓF(·,·)` exist and are jointly continuous on `U × S`.
Here `DF x s` and `D2F x s` are the first and second Fréchet derivatives of `F (·) s` at `x`. -/
def IsLowerC2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  ∀ x₀, f x₀ ≠ ⊤ →
    ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x₀ ∈ U ∧
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : CompactSpace S)
      (F : EuclideanSpace ℝ (Fin n) → S → ℝ)
      (DF : EuclideanSpace ℝ (Fin n) → S → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      (D2F : EuclideanSpace ℝ (Fin n) → S →
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)),
      ContinuousOn (Function.uncurry F) (U ×ˢ Set.univ) ∧
      (∀ x ∈ U, ∃ s, f x = ((F x s : ℝ) : EReal) ∧ ∀ s', F x s' ≤ F x s) ∧
      (∀ x ∈ U, ∀ s, HasFDerivAt (fun y => F y s) (DF x s) x ∧
        HasFDerivAt (fun y => DF y s) (D2F x s) x) ∧
      ContinuousOn (Function.uncurry DF) (U ×ˢ Set.univ) ∧
      ContinuousOn (Function.uncurry D2F) (U ×ˢ Set.univ)

end NonsmoothLojasiewicz.Traj


