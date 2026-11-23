-- Prove2me | Definitions.Def_TwoStageSRO_AsymOpt_Supplement_PolyGeometry
-- name    : TwoStageSRO_AsymOpt_Supplement_PolyGeometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:35:27.244806+00:00
-- url     : https://prove2.me/theorems/c12702b5-b09a-4ad5-95eb-bdbb807df9d7
-- title:
--   App. A.1, A.3–A.4, pp. 33–38 — faces, facets, dim and dim̲ of a polyhedron T, distances, radius ∆_Ξ(T) (Definition 3), θ^T_Ξ (Definition 4)
-- statement:
--   Let $\Xi=\{\zeta\in\mathbb R^d : g_i^\top\zeta\ge g^0_i,\ i\in[\tilde m]\}$ be the polyhedron of the two-stage model, and $\mathcal H_i=\{\zeta : g_i^\top\zeta=g^0_i\}$ the hyperplane of its $i$-th constraint. All norms are a fixed $\ell_p$-norm, $p\in[1,\infty]$. For a polyhedron $T\subseteq\mathbb R^d$:
--
--   1. **Faces.** $\mathrm{Faces}(T)$ is the set of nonempty faces of $T$: $T$ itself and the nonempty sets $T\cap\{x : w^\top x=t\}$ with $w\neq 0$ and $w^\top x\le t$ valid on $T$.
--   2. **Dimension.** $\dim(F)$ is the dimension of the affine hull of $F$. $\mathrm{Facets}(T)$ is the set of faces $F$ of $T$ with $\dim(F)=\dim(T)-1$. $\underline{\dim}(T)$ is the dimension of the minimal faces of $T$ (faces of $T$ containing no other face of $T$).
--   3. **Distances.** $\mathrm{dist}(\zeta,S)=\inf_{z\in S}\|\zeta-z\|$ and $\mathrm{dist}(S,S')=\inf_{z\in S,\,z'\in S'}\|z-z'\|$, both $+\infty$ for an empty set.
--   4. **Radius of a polyhedron (Definition 3).** For $T\subseteq\Xi$,
--   $$\Delta_\Xi(T)=\min\{\rho_1(T),\rho_2(T)\},\qquad \rho_1(T)=\min_{i\in[\tilde m]:\,\mathcal H_i\cap T=\emptyset}\mathrm{dist}(T,\mathcal H_i),\qquad \rho_2(T)=\min_{F\in\mathrm{Facets}(T)}\Delta_\Xi(F),$$
--   a minimum over an empty set being $+\infty$.
--   5. **Sine of the angle (Definition 4).** For $F\in\mathrm{Faces}(T)$ and $i\in[\tilde m]$,
--   $$\theta_i(F)=\inf\{\theta\ge0 : \mathrm{dist}(\zeta,F\cap\mathcal H_i)\le\theta\,\mathrm{dist}(\zeta,\mathcal H_i)\ \ \forall\zeta\in F\},\qquad \theta^T_\Xi=\max\Big\{1,\max_{F\in\mathrm{Faces}(T),\,i:\,F\cap\mathcal H_i\neq\emptyset}\theta_i(F)\Big\},$$
--   and $1/\theta^T_\Xi$ is the sine of the angle between $T$ and $\Xi$.
--   6. **The radii of Theorem 3 and its Claim.** For $\bar\epsilon>0$ and $\lambda\in(0,1)$,
--   $$\epsilon=\Big(\frac{\lambda}{2\theta^T_\Xi}\Big)^{\dim(T)-\underline{\dim}(T)}\lambda\min\{\bar\epsilon,\Delta_\Xi(T)\},\qquad \alpha_k=\Big(\frac{2\theta^T_\Xi}{\lambda}\Big)^{\dim(T)-k}\quad(k\le\dim(T)).$$
--
--   These quantities measure how far the faces of a polyhedron $T\subseteq\Xi$ stay from the constraint hyperplanes of $\Xi$ and how sharply they meet them; they determine the explicit uniform radius of Theorem 3.
--
--   **Formalization Note** A polyhedron is a set $\{x : Ax\le b\}$ and faces are those of the published definitions `CombOpt.MatchingPolytope.IsPolyhedron` and `CombOpt.MatchingPolytope.IsFace`, with the empty face excluded explicitly. $\dim$ is the rank of the span of differences of points (Mathlib's `vectorSpan`), and $\mathrm{Facets}$ is written $\dim(F)+1=\dim(T)$, so a point has no facets. $\underline{\dim}(T)$ is the least dimension of a minimal face (all minimal faces of a nonempty polyhedron have the same dimension). Distances, $\Delta_\Xi$, $\theta_i$ and $\theta^T_\Xi$ are computed in `EReal`: $\theta_i(F)=+\infty$ when no real $\theta$ works, and an empty maximum is $-\infty$, so $\theta^T_\Xi=\max\{1,-\infty\}=1$ then. The recursion of Definition 3 descends one dimension per step and is computed by an auxiliary function indexed by $\dim(T)$. In $\epsilon$ and $\alpha_k$, $\theta^T_\Xi$ is converted to a real number; it is finite for every nonempty polyhedron $T\subseteq\Xi$ by Lemma 8.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, pp. 33–34 (App. A.1, (14)–(15)), p. 37 (Definition 3), p. 38 (Definition 4), p. 48 (Theorem 3), p. 49 (Claim)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_CombOpt_MatchingPolytope_IsFace
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry

open Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt.Supplement

variable {n d r m mt : ℕ}

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 34, App. A.1:
`dim(F)`, the dimension of (the affine hull of) a set `F ⊆ ℝᵈ`.

**Formalization Note** The dimension of the linear space spanned by the differences of points of `F`
(Mathlib's `vectorSpan`). For a nonempty set it is the dimension of its affine hull; every use below
is on a nonempty face. -/
noncomputable def polyDim (F : Set (Fin d → ℝ)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ F)

/-- arXiv:1907.07142v4, p. 34, App. A.1 (Faces(T); Conforti et al. 2014, §3.8): `F ∈ Faces(T)`, i.e. `F` is
a nonempty face of `T`: `T` itself or the intersection of `T` with a supporting hyperplane of `T`.

**Formalization Note** Faces are those of the published definition `CombOpt.MatchingPolytope.IsFace`
(`∅`, `T`, and `T ∩ {x : wᵀx = t}` for a supporting hyperplane `wᵀx = t`, `w ≠ 0`); the empty face
is excluded explicitly, as every face the paper uses is nonempty (pp. 37–38, 49–51). -/
def IsFaceOf (T F : Set (Fin d → ℝ)) : Prop :=
  F.Nonempty ∧ CombOpt.MatchingPolytope.IsFace T F

/-- arXiv:1907.07142v4, p. 34, App. A.1: `F ∈ Facets(T)`, a nonempty face of `T` of dimension
`dim(T) − 1`.

**Formalization Note** Written `dim(F) + 1 = dim(T)` so that no natural-number subtraction occurs: a
`0`-dimensional `T` has no facets (as used on p. 38: a minimal face has `Facets(F) = ∅`). -/
def IsFacetOf (T F : Set (Fin d → ℝ)) : Prop :=
  IsFaceOf T F ∧ polyDim F + 1 = polyDim T

/-- arXiv:1907.07142v4, pp. 34, 38: a minimal face of `T`, i.e. a face of `T` containing no other face
of `T`. -/
def IsMinimalFaceOf (T F : Set (Fin d → ℝ)) : Prop :=
  IsFaceOf T F ∧ ∀ F', IsFaceOf T F' → F' ⊆ F → F' = F

/-- arXiv:1907.07142v4, p. 34, App. A.1: `dim̲(T)`, the dimension of the minimal faces of `T` (underlined
`dim` in the PDF).

**Formalization Note** The least dimension of a minimal face of `T`. All minimal faces of a nonempty
polyhedron are translates of its lineality space and so have one common dimension; a nonempty
polyhedron has finitely many faces and therefore a minimal one, so the infimum is over a nonempty set. -/
noncomputable def minFaceDim (T : Set (Fin d → ℝ)) : ℕ :=
  sInf {k : ℕ | ∃ F, IsMinimalFaceOf T F ∧ polyDim F = k}

/-- arXiv:1907.07142v4, p. 34, (15): the distance `dist(S, S') = inf_{z ∈ S, z' ∈ S'} ‖z − z'‖` between two
sets in the `ℓp`-norm.

**Formalization Note** Computed in `EReal`; it is `+∞` when either set is empty. -/
noncomputable def setDist (p : ℝ≥0∞) [Fact (1 ≤ p)] (S S' : Set (Fin d → ℝ)) : EReal :=
  ⨅ z ∈ S, ⨅ z' ∈ S', ((‖WithLp.toLp p (z - z')‖ : ℝ) : EReal)

/-- arXiv:1907.07142v4, p. 33, (14): the distance `dist(ζ, S) = inf_{z ∈ S} ‖ζ − z‖` from a point to a set in
the `ℓp`-norm, in `EReal` (`+∞` for an empty set). -/
noncomputable def ptDist (p : ℝ≥0∞) [Fact (1 ≤ p)] (ζ : Fin d → ℝ) (S : Set (Fin d → ℝ)) : EReal :=
  ⨅ z ∈ S, ((‖WithLp.toLp p (ζ - z)‖ : ℝ) : EReal)

/-- arXiv:1907.07142v4, p. 37, Definition 3: `ρ₁(T) = min_{i ∈ [m̃] : Hᵢ ∩ T = ∅} dist(T, Hᵢ)`.

**Formalization Note** An infimum in `EReal`, `+∞` when every hyperplane `Hᵢ` meets `T` (the convention
of the proof of Lemma 6, p. 37). -/
noncomputable def rho1 (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : Set (Fin d → ℝ)) : EReal :=
  ⨅ k ∈ {k : Fin mt | hyperplane M k ∩ T = ∅}, setDist p T (hyperplane M k)

/-- Auxiliary recursion for Definition 3 (arXiv:1907.07142v4, p. 37), indexed by the dimension:
`radiusAux 0 T = ρ₁(T)` and `radiusAux (k+1) T = min{ρ₁(T), min_{F ∈ Facets(T)} radiusAux k F}`. -/
noncomputable def radiusAux (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ℕ → Set (Fin d → ℝ) → EReal
  | 0, T => rho1 M p T
  | k + 1, T => min (rho1 M p T) (⨅ F ∈ {F | IsFacetOf T F}, radiusAux M p k F)

/-- arXiv:1907.07142v4, p. 37, Definition 3: the radius of a polyhedron `T ⊆ Ξ` with respect to `Ξ`,
`∆_Ξ(T) = min{ρ₁(T), ρ₂(T)}`, `ρ₂(T) = min_{F ∈ Facets(T)} ∆_Ξ(F)`.

**Formalization Note** The recursion of Definition 3 runs down the dimension (a facet has dimension one
less), so it is computed by `radiusAux` started at `dim(T)`; a minimum over an empty set is `+∞`, so
`ρ₂ = +∞` for a `T` without facets (p. 38). Values in `EReal`. -/
noncomputable def polyRadius (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : Set (Fin d → ℝ)) : EReal :=
  radiusAux M p (polyDim T) T

/-- arXiv:1907.07142v4, p. 38, Definition 4:
`θᵢ(F) = inf{θ ≥ 0 : dist(ζ, F ∩ Hᵢ) ≤ θ dist(ζ, Hᵢ) for all ζ ∈ F}`.

**Formalization Note** An infimum in `EReal` over real `θ ≥ 0`; it is `+∞` when no real `θ` works
(never `0` by a junk convention). -/
noncomputable def thetaFace (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (F : Set (Fin d → ℝ)) (i : Fin mt) : EReal :=
  sInf {θ : EReal | ∃ t : ℝ, 0 ≤ t ∧ θ = (t : EReal) ∧
    ∀ ζ ∈ F, ptDist p ζ (F ∩ hyperplane M i) ≤ (t : EReal) * ptDist p ζ (hyperplane M i)}

/-- arXiv:1907.07142v4, p. 38, Definition 4: `θ^T_Ξ = max{1, max_{F ∈ Faces(T), i ∈ [m̃] : F ∩ Hᵢ ≠ ∅} θᵢ(F)}`;
`1/θ^T_Ξ` is the sine of the angle between `T` and `Ξ`.

**Formalization Note** In `EReal`; the inner maximum over an empty index set is `⊥ = −∞`, so that
`θ^T_Ξ = max{1, −∞} = 1` then, as in the proof of Lemma 8 (p. 39). -/
noncomputable def thetaPoly (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : Set (Fin d → ℝ)) : EReal :=
  max 1 (⨆ F ∈ {F | IsFaceOf T F}, ⨆ i ∈ {i : Fin mt | (F ∩ hyperplane M i).Nonempty}, thetaFace M p F i)

/-- arXiv:1907.07142v4, p. 48, Theorem 3: the radius
`ϵ = (λ / (2θ^T_Ξ))^{dim(T) − dim̲(T)} · λ · min{ϵ̄, ∆_Ξ(T)}`.

**Formalization Note** `θ^T_Ξ` enters through `EReal.toReal`; it is a real number `≥ 1` for every
nonempty polyhedron `T ⊆ Ξ` (Lemma 8), so the conversion is exact there. `min{ϵ̄, ∆_Ξ(T)}` is taken in
`EReal` and lies in `[0, ϵ̄]` (`∆_Ξ(T) ≥ 0` is an infimum of norms or `+∞`), so its `toReal` is exact.
`dim̲(T) ≤ dim(T)`, so the natural-number exponent involves no truncation. -/
noncomputable def epsThm3 (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : Set (Fin d → ℝ)) (εbar lam : ℝ) : ℝ :=
  (lam / (2 * (thetaPoly M p T).toReal)) ^ (polyDim T - minFaceDim T) * lam *
    (min (εbar : EReal) (polyRadius M p T)).toReal

/-- arXiv:1907.07142v4, p. 49, Claim in the proof of Theorem 3: `α_k = (2θ^T_Ξ / λ)^{dim(T) − k}` for
`k ∈ {dim̲(T), …, dim(T)}`.

**Formalization Note** `θ^T_Ξ` enters through `EReal.toReal`, exact by Lemma 8; the Claim uses `α_k`
only for `k ≤ dim(T)`, so the exponent involves no truncation. -/
noncomputable def alphaClaim (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : Set (Fin d → ℝ)) (lam : ℝ) (k : ℕ) : ℝ :=
  (2 * (thetaPoly M p T).toReal / lam) ^ (polyDim T - k)

end TwoStageSRO.AsymOpt.Supplement


