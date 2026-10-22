-- Prove2me | Definitions.Def_SteenrodSmoothing_Sections_Setting
-- name    : SteenrodSmoothing_Sections_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:23.172634+00:00
-- url     : https://prove2.me/theorems/380719ea-d26b-47dd-b5c4-636cf426cd7c
-- title:
--   Definition 0.3, Theorem 0.11, pp. 2–5 — smooth locally trivial bundles, smoothness on a neighbourhood of a set, convex chart domains
-- statement:
--   This file fixes the objects of Wockel's generalised Steenrod approximation theorem. Throughout, $M$ is a manifold with corners modelled by a model with corners $I$ on a real normed space $E_M$, $N$ is a manifold modelled on a real normed space $F$ (without boundary), and $E$ is a manifold with corners modelled by $I_E$ on a real normed space; smoothness means $C^\infty$.
--
--   1. **Smoothness on a neighbourhood of a set.** A map $f : X \to Y$ between such manifolds is *smooth on a neighbourhood of* $s \subseteq X$ if there is an open set $A \subseteq X$ with $s \subseteq A$ such that $f$ is $C^\infty$ on $A$:
--   $$\exists A \text{ open},\quad s \subseteq A,\quad f|_A \in C^\infty .$$
--   2. **Smooth local trivialisations.** For a map $\pi : E \to M$, a local trivialisation with typical fibre $N$ over an open set $S \subseteq M$ is a homeomorphism $\varphi : \pi^{-1}(S) \to S \times N$ with $\mathrm{pr}_1(\varphi(p)) = \pi(p)$ for all $p \in \pi^{-1}(S)$. It is *smooth* if $\varphi$ is $C^\infty$ on $\pi^{-1}(S)$ and $\varphi^{-1}$ is $C^\infty$ on $S \times N$, i.e. $\varphi$ is a diffeomorphism.
--   3. **Locally trivial smooth bundles.** $\pi : E \to M$ is a *locally trivial smooth bundle with typical fibre $N$* if every point of $M$ lies in the base set $S$ of some smooth local trivialisation $\varphi : \pi^{-1}(S) \to S \times N$.
--   4. **Convex chart domains.** A subset $W \subseteq N$ is *diffeomorphic to an open convex subset of the modelling space* $F$ of $N$ if there is a $C^\infty$ diffeomorphism $\varphi$ from $W$ onto an open convex subset $\varphi(W) \subseteq F$ (a partial diffeomorphism $N \to F$ with source $W$ and convex open target; in particular $W$ is open).
--
--   These notions are shared by every statement of the mission: the hypothesis "σ is smooth on a neighbourhood of $L \setminus U$" and the conclusion "τ is smooth on a neighbourhood of $L$" of the goal theorem, the bundle hypothesis, and the convex chart domains of Lemma 0.10.
--
--   **Formalization Note** The paper works with manifolds modelled on arbitrary locally convex spaces; Mathlib's manifolds require normed model spaces, so here the models of $N$ and $E$ are real normed spaces (not necessarily complete or finite-dimensional). On normed spaces the paper's smoothness (Definition 0.1) coincides with Fréchet $C^\infty$ (Remark 0.2 and Keller), which is Mathlib's `ContMDiff … ∞`; `∞` is $C^\infty$, not the analytic `ω`. "Smooth on a neighbourhood of $s$" requires an **open** set containing $s$, not smoothness on $s$ itself. A local trivialisation is Mathlib's `Bundle.Trivialization N π` (source $\pi^{-1}(S)$, target $S \times N$, first component $\pi$); $M \times N$ carries the product model `I.prod 𝓘(ℝ, F)`.
-- source:
--   Wockel, A Generalisation of Steenrod's Approximation Theorem, arXiv:math/0610252v1, pp. 2–5, Definitions 0.1, 0.3, Theorem 0.11, Lemma 0.10 and proof of Theorem 0.11 (p. 4, local trivialisations)

import Mathlib

open scoped ContDiff Manifold Topology

namespace SteenrodSmoothing.Sections

/-- A map `f : X → Y` between manifolds (with corners) is smooth (`C^∞`) on a neighbourhood of
the set `s ⊆ X`: there is an open set `A ⊇ s` on which `f` is `C^∞`. -/
def SmoothNear {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    {HX : Type*} [TopologicalSpace HX] (IX : ModelWithCorners ℝ EX HX)
    {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
    {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY]
    {HY : Type*} [TopologicalSpace HY] (IY : ModelWithCorners ℝ EY HY)
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace HY Y]
    (f : X → Y) (s : Set X) : Prop :=
  ∃ A : Set X, IsOpen A ∧ s ⊆ A ∧ ContMDiffOn IX IY ∞ f A

/-- A local trivialisation `e : π⁻¹(S) ≅ S × N` of `π : E → M` (with `pr₁ ∘ e = π`) is smooth:
`e` is `C^∞` on `π⁻¹(S)` and its inverse is `C^∞` on `S × N`, i.e. `e` is a diffeomorphism. -/
def IsSmoothTrivialization
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
    {HE : Type*} [TopologicalSpace HE] (IE : ModelWithCorners ℝ EE HE)
    {E : Type*} [TopologicalSpace E] [ChartedSpace HE E]
    {π : E → M} (e : Bundle.Trivialization N π) : Prop :=
  ContMDiffOn IE (I.prod 𝓘(ℝ, F)) ∞ e e.source ∧
    ContMDiffOn (I.prod 𝓘(ℝ, F)) IE ∞ e.toOpenPartialHomeomorph.symm e.target

/-- `π : E → M` is a locally trivial smooth bundle with typical fibre `N`: every point of `M`
lies in the base set of a smooth local trivialisation `π⁻¹(S) ≅ S × N` over `π`. -/
def IsSmoothLocallyTrivialBundle
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : Type*) [TopologicalSpace N] [ChartedSpace F N]
    {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
    {HE : Type*} [TopologicalSpace HE] (IE : ModelWithCorners ℝ EE HE)
    {E : Type*} [TopologicalSpace E] [ChartedSpace HE E]
    (π : E → M) : Prop :=
  ∀ x : M, ∃ e : Bundle.Trivialization N π, x ∈ e.baseSet ∧ IsSmoothTrivialization I F IE e

/-- `W ⊆ N` is diffeomorphic to an open convex subset of the model space `F` of `N`: there is a
`C^∞` partial diffeomorphism `φ : N → F` with source `W` and convex (open) target `φ(W)`. -/
def IsConvexChartDomain
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    (W : Set N) : Prop :=
  ∃ φ : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) N F ∞, φ.source = W ∧ Convex ℝ φ.target

end SteenrodSmoothing.Sections


