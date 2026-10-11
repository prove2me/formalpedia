-- Prove2me | Definitions.Def_SmoothSchoenflies_basic
-- name    : SmoothSchoenflies_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T10:24:54.638176+00:00
-- url     : https://prove2.me/theorems/13b00304-8e0e-47cd-9e3c-9e77cef65f38
-- title:
--   Spheres, smooth embeddings $S^n\hookrightarrow S^{n+1}$, and embedded closed balls
-- statement:
--   Basic objects for the smooth Schoenflies problem.
--
--   1. $S^n=\{x\in\mathbb R^{n+1}:\|x\|=1\}$ (`Sph n`), the unit sphere with its standard smooth manifold structure modelled on $\mathbb R^n$.
--   2. A map $f:S^n\to S^{n+1}$ is a **smooth embedding** (`IsSmoothEmbeddingSph n f`) if it is $C^\infty$, injective, and its differential $df_x:T_xS^n\to T_{f(x)}S^{n+1}$ is injective at every $x$. Since $S^n$ is compact, this is equivalent to being a smooth embedding; the image is a smooth $n$-dimensional submanifold diffeomorphic to $S^n$.
--   3. A set $K\subseteq S^{n+1}$ is a **smoothly embedded closed ball** (`IsSmoothClosedBallIn n K`) if there is a $C^\infty$ map $e:\mathbb R^{n+1}\to S^{n+1}$ that is injective on $D^{n+1}=\{\|x\|\le1\}$, has injective differential at every point of $D^{n+1}$ (boundary included), and satisfies $e(D^{n+1})=K$. This says exactly that $K$, with the smooth structure inherited from $S^{n+1}$, is diffeomorphic to $D^{n+1}$.
--   4. $K\subseteq S^{n+1}$ is a **topological closed ball** (`IsTopClosedBallIn n K`) if $K$ is homeomorphic to $D^{n+1}$.
--
--   These definitions are shared by the goal theorem and all milestones of the mission.
--
--   **Formalization Note** Smoothness is $C^\infty$ (`ContMDiff … ∞`), not analytic. Requiring $e$ to be smooth on all of $\mathbb R^{n+1}$ instead of on a neighbourhood of $D^{n+1}$ is no restriction, since one may precompose with a smooth radial map that is the identity on $D^{n+1}$.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Schoenflies problem' (posted by rybu, Nov 6 2009), https://www.openproblemgarden.org/op/smooth_4_dimensional_schoenflies_problem

import Mathlib

/-!
# Smooth Schoenflies problem: basic definitions

Spheres, smooth embeddings of `Sⁿ` into `Sⁿ⁺¹`, and smoothly / topologically embedded
closed balls inside `Sⁿ⁺¹`.
-/

open Manifold Metric
open scoped ContDiff

namespace SmoothSchoenflies

/-- The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, with its standard smooth manifold structure modelled on `ℝⁿ`. -/
abbrev Sph (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- `f : Sⁿ → Sⁿ⁺¹` is a smooth embedding: a `C^∞` injective immersion (since `Sⁿ` is
compact, this is the same as a smooth embedding). Its image is a smooth `n`-dimensional
submanifold of `Sⁿ⁺¹` diffeomorphic to `Sⁿ`. -/
def IsSmoothEmbeddingSph (n : ℕ) (f : Sph n → Sph (n + 1)) : Prop :=
  ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ f ∧ Function.Injective f ∧
    ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) f x)

/-- `K ⊆ Sⁿ⁺¹` is a smoothly embedded closed `(n+1)`-ball, i.e. `K` (with the smooth structure
inherited from `Sⁿ⁺¹`) is diffeomorphic to the closed unit ball `Dⁿ⁺¹ ⊆ ℝⁿ⁺¹`: `K` is the
image of `Dⁿ⁺¹` under a `C^∞` map `ℝⁿ⁺¹ → Sⁿ⁺¹` that is injective on `Dⁿ⁺¹` and has
injective differential at every point of `Dⁿ⁺¹` (boundary points included). -/
def IsSmoothClosedBallIn (n : ℕ) (K : Set (Sph (n + 1))) : Prop :=
  ∃ e : EuclideanSpace ℝ (Fin (n + 1)) → Sph (n + 1),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡 (n + 1)) ∞ e ∧
    Set.InjOn e (closedBall 0 1) ∧
    (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡 (n + 1)) e x)) ∧
    e '' closedBall 0 1 = K

/-- `K ⊆ Sⁿ⁺¹` is homeomorphic to the closed unit ball `Dⁿ⁺¹ ⊆ ℝⁿ⁺¹`. -/
def IsTopClosedBallIn (n : ℕ) (K : Set (Sph (n + 1))) : Prop :=
  Nonempty (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₜ K)

end SmoothSchoenflies


