-- Prove2me | Definitions.Def_SliceRibbon_basic
-- name    : SliceRibbon_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T11:53:21.235616+00:00
-- url     : https://prove2.me/theorems/4b65069f-769f-49af-bd16-4e231fafec89
-- title:
--   Knots, slice discs, ribbon discs and minimal discs in $S^3\subset B^4$
-- statement:
--   Basic objects for the slice–ribbon problem. Throughout, $\mathbb R^4$ is Euclidean $4$-space, $S^3=\{\|x\|=1\}$, $B^4=\{\|x\|\le1\}$, and $D^2=\{z\in\mathbb R^2:\|z\|\le1\}$ is the closed unit disc of the parameter plane. A disc is a $C^\infty$ map $\mathbb R^2\to\mathbb R^4$ considered on $D^2$.
--
--   1. **Knot** (`IsKnot γ`): $\gamma:\mathbb R\to\mathbb R^4$ is $C^\infty$, $1$-periodic, $\|\gamma(t)\|=1$ for all $t$, injective on $[0,1)$, and $\gamma'(t)\neq0$ for all $t$. The knot is $K=\gamma(\mathbb R)\subset S^3$.
--   2. **Slice disc** (`IsSliceDisk γ F`): $F$ is $C^\infty$, injective on $D^2$, with injective differential $dF_z$ at every $z\in D^2$; $\|F(z)\|<1$ whenever $\|z\|<1$; $F$ maps the unit circle onto $K$; and $F$ is transverse to $S^3$ along the boundary: $\langle F(z),dF_z(z)\rangle>0$ for $\|z\|=1$. $K$ is **slice** (`IsSlice γ`) if a slice disc exists.
--   3. **Ribbon slice disc** (`IsRibbonSliceDisk γ F`): a slice disc such that at every critical point $z$ with $\|z\|<1$ of $r_F(z)=\|F(z)\|^2$ the Hessian of $r_F$ is non-degenerate and $z$ is not a local maximum of $r_F$ (the radial function is Morse in the interior with no local maxima).
--   4. **Ribbon disc** (`IsRibbonImmersedDisk γ f`, Fox): $f$ is $C^\infty$, maps $D^2$ into $S^3$, has injective differential on $D^2$, maps the unit circle injectively onto $K$, has no triple points on $D^2$, and at each double point $f(z)=f(w)$, $z\neq w$, the images of $df_z$ and $df_w$ span the tangent space $f(z)^{\perp}$ of $S^3$. Moreover there are arcs $a_1,b_1,\dots,a_n,b_n:[0,1]\to D^2$, continuous and injective, pairwise disjoint, with $f\circ a_i=f\circ b_i$, each $a_i$ inside the open disc, each $b_i$ having both endpoints on the unit circle and all other points in the open disc, such that the set of $z\in D^2$ sharing their image with another point of $D^2$ is exactly the union of these arcs (ribbon singularities). $K$ is **ribbon** (`IsRibbon γ`) if a ribbon disc exists.
--   5. **Minimal disc** (`IsMinimalOnDisk F`): with $E=\langle\partial_0F,\partial_0F\rangle$, $G'=\langle\partial_0F,\partial_1F\rangle$, $G=\langle\partial_1F,\partial_1F\rangle$, for every $\|z\|<1$
--   $$G\,\partial_0\partial_0F-2G'\,\partial_0\partial_1F+E\,\partial_1\partial_1F\in\operatorname{im}dF_z,$$
--   i.e. the mean curvature vector of $F$ vanishes on the open disc.
--
--   These definitions are shared by the goal theorem and all milestones of the mission.
--
--   **Formalization Note** Smoothness is $C^\infty$ (`ContDiff ℝ ∞`) on all of $\mathbb R^2$ (resp. $\mathbb R$); only the restriction to $D^2$ matters. Knots enter only through their image, so slice and ribbon do not depend on orientation or parametrization. The ribbon arcs are only required to be continuous; transversality of the double points makes the double-point set a $1$-manifold. `radialSq F` is $z\mapsto\|F(z)\|^2$, and `firstPartial`/`secondPartial` are partial derivatives along the standard basis of $\mathbb R^2$.
-- source:
--   Open Problem Garden, 'Slice-ribbon problem' (posted by rybu, Nov 7 2009), http://www.openproblemgarden.org/op/slice_ribbon_problem; definitions of slice knot and ribbon knot linked from the problem statement; [F] Fox, Some problems in knot theory (1962); [H] Hass, The geometry of the slice-ribbon problem (1983).

import Mathlib

/-!
# Basic objects for the slice–ribbon problem

Knots in `S³ ⊂ ℝ⁴`, smooth slice discs in `B⁴`, ribbon discs (Fox's immersed-disc
definition in `S³`), ribbon slice discs (Morse-theoretic definition in `B⁴`) and minimal
discs in `B⁴`.
-/

open Real Metric
open scoped ContDiff

namespace SliceRibbon

/-- The Euclidean plane `ℝ²`, parameter space of discs. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- Euclidean `ℝ⁴`; `S³` is its unit sphere and `B⁴` its closed unit ball. -/
abbrev R4 := EuclideanSpace ℝ (Fin 4)

/-- `γ : ℝ → ℝ⁴` parametrises a (smooth, tame) knot in `S³`: it is `C^∞`, `1`-periodic,
takes values in the unit sphere `S³`, is injective on one period `[0,1)`, and has
nowhere-vanishing velocity. The knot itself is the image `Set.range γ`. -/
def IsKnot (γ : ℝ → R4) : Prop :=
  ContDiff ℝ ∞ γ ∧ Function.Periodic γ 1 ∧ (∀ t, ‖γ t‖ = 1) ∧
    Set.InjOn γ (Set.Ico 0 1) ∧ ∀ t, deriv γ t ≠ 0

/-- `F : ℝ² → ℝ⁴` restricted to the closed unit disc `D² = closedBall 0 1` is a smooth
slice disc for the knot `Set.range γ`: a `C^∞` map which is injective on `D²`, has injective
differential at every point of `D²` (so `F(D²)` is a smoothly embedded disc), sends the open
disc into the open ball `‖x‖ < 1`, sends the boundary circle onto the knot, and meets `S³`
transversally along the boundary (the radial component of the outward normal derivative is
positive). -/
def IsSliceDisk (γ : ℝ → R4) (F : R2 → R4) : Prop :=
  ContDiff ℝ ∞ F ∧ Set.InjOn F (closedBall 0 1) ∧
    (∀ z ∈ closedBall (0 : R2) 1, Function.Injective (fderiv ℝ F z)) ∧
    (∀ z : R2, ‖z‖ < 1 → ‖F z‖ < 1) ∧
    F '' sphere 0 1 = Set.range γ ∧
    ∀ z : R2, ‖z‖ = 1 → 0 < inner ℝ (F z) (fderiv ℝ F z z)

/-- A knot is (smoothly) **slice** if it bounds a smooth slice disc in `B⁴`. -/
def IsSlice (γ : ℝ → R4) : Prop :=
  ∃ F : R2 → R4, IsSliceDisk γ F

/-- The squared radial function `z ↦ ‖F z‖²` of a disc `F` in `ℝ⁴`. -/
noncomputable def radialSq (F : R2 → R4) (z : R2) : ℝ := ‖F z‖ ^ 2

/-- A slice disc `F` for `γ` is a **ribbon slice disc** if the radial function restricted to
the disc is Morse in the interior with no local maxima: at every interior critical point `z`
of `‖F ·‖²` (i.e. `‖z‖ < 1` and the differential vanishes) the Hessian is non-degenerate and
`z` is not a local maximum. -/
def IsRibbonSliceDisk (γ : ℝ → R4) (F : R2 → R4) : Prop :=
  IsSliceDisk γ F ∧
    ∀ z : R2, ‖z‖ < 1 → fderiv ℝ (radialSq F) z = 0 →
      (∀ v : R2, v ≠ 0 → ∃ w : R2, iteratedFDeriv ℝ 2 (radialSq F) z ![v, w] ≠ 0) ∧
        ¬ IsLocalMax (radialSq F) z

/-- `f : ℝ² → ℝ⁴` restricted to the closed unit disc `D²` is a **ribbon disc** in `S³` for the
knot `Set.range γ` (Fox): a `C^∞` immersion of `D²` into `S³` whose boundary circle is mapped
injectively onto the knot and whose only singularities are ribbon singularities. Concretely
there are finitely many pairs of arcs `aᵢ, bᵢ : [0,1] → D²` such that
1. each `aᵢ` is a continuous injective arc lying in the open disc;
2. each `bᵢ` is a continuous injective arc whose endpoints lie on the boundary circle and whose
   other points lie in the open disc;
3. `f ∘ aᵢ = f ∘ bᵢ` on `[0,1]`;
4. the `2n` arcs are pairwise disjoint;
5. the set of points of `D²` sharing their image with another point of `D²` is exactly the
   union of the arcs;
6. `f` has no triple points on `D²`;
7. the two sheets through every double point meet transversally in `S³`, i.e. the images of the
   two differentials span the tangent space `(ℝ · f z)ᗮ` of `S³`. -/
def IsRibbonImmersedDisk (γ : ℝ → R4) (f : R2 → R4) : Prop :=
  ContDiff ℝ ∞ f ∧
    (∀ z ∈ closedBall (0 : R2) 1, ‖f z‖ = 1) ∧
    (∀ z ∈ closedBall (0 : R2) 1, Function.Injective (fderiv ℝ f z)) ∧
    Set.InjOn f (sphere 0 1) ∧ f '' sphere 0 1 = Set.range γ ∧
    (∀ z₁ ∈ closedBall (0 : R2) 1, ∀ z₂ ∈ closedBall (0 : R2) 1, ∀ z₃ ∈ closedBall (0 : R2) 1,
      f z₁ = f z₂ → f z₂ = f z₃ → z₁ = z₂ ∨ z₂ = z₃ ∨ z₁ = z₃) ∧
    (∀ z ∈ closedBall (0 : R2) 1, ∀ w ∈ closedBall (0 : R2) 1, z ≠ w → f z = f w →
      LinearMap.range (fderiv ℝ f z : R2 →ₗ[ℝ] R4) ⊔ LinearMap.range (fderiv ℝ f w : R2 →ₗ[ℝ] R4) =
        (Submodule.span ℝ {f z})ᗮ) ∧
    ∃ (n : ℕ) (a b : Fin n → ℝ → R2),
      (∀ i, ContinuousOn (a i) (Set.Icc 0 1) ∧ Set.InjOn (a i) (Set.Icc 0 1) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖a i t‖ < 1) ∧
      (∀ i, ContinuousOn (b i) (Set.Icc 0 1) ∧ Set.InjOn (b i) (Set.Icc 0 1) ∧
        ‖b i 0‖ = 1 ∧ ‖b i 1‖ = 1 ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖b i t‖ < 1) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, f (a i t) = f (b i t)) ∧
      (∀ i j, Disjoint (a i '' Set.Icc 0 1) (b j '' Set.Icc 0 1)) ∧
      (∀ i j, i ≠ j → Disjoint (a i '' Set.Icc 0 1) (a j '' Set.Icc 0 1) ∧
        Disjoint (b i '' Set.Icc 0 1) (b j '' Set.Icc 0 1)) ∧
      {z ∈ closedBall (0 : R2) 1 | ∃ w ∈ closedBall (0 : R2) 1, w ≠ z ∧ f w = f z} =
        ⋃ i, (a i '' Set.Icc 0 1 ∪ b i '' Set.Icc 0 1)

/-- A knot is **ribbon** if it bounds a ribbon disc in `S³` (Fox's definition). -/
def IsRibbon (γ : ℝ → R4) : Prop :=
  ∃ f : R2 → R4, IsRibbonImmersedDisk γ f

/-- The `(i,j)` second partial derivative `∂ᵢ∂ⱼF(z)` of `F : ℝ² → ℝ⁴`. -/
noncomputable def secondPartial (F : R2 → R4) (z : R2) (i j : Fin 2) : R4 :=
  iteratedFDeriv ℝ 2 F z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]

/-- The first partial derivative `∂ᵢF(z)` of `F : ℝ² → ℝ⁴`. -/
noncomputable def firstPartial (F : R2 → R4) (z : R2) (i : Fin 2) : R4 :=
  fderiv ℝ F z (EuclideanSpace.single i 1)

/-- `F` is a **minimal surface** on the open unit disc (for the Euclidean metric of `ℝ⁴`): at
every `z` with `‖z‖ < 1` the mean curvature vector vanishes. With `E = ⟨∂₀F,∂₀F⟩`,
`G' = ⟨∂₀F,∂₁F⟩`, `G = ⟨∂₁F,∂₁F⟩` (first fundamental form), this says that the vector
`G ∂₀∂₀F − 2G' ∂₀∂₁F + E ∂₁∂₁F` is tangent to the surface, i.e. lies in the image of `dF_z`
(its normal component, a positive multiple of the mean curvature vector, is zero). -/
def IsMinimalOnDisk (F : R2 → R4) : Prop :=
  ∀ z : R2, ‖z‖ < 1 →
    (inner ℝ (firstPartial F z 1) (firstPartial F z 1)) • secondPartial F z 0 0
      - (2 * inner ℝ (firstPartial F z 0) (firstPartial F z 1)) • secondPartial F z 0 1
      + (inner ℝ (firstPartial F z 0) (firstPartial F z 0)) • secondPartial F z 1 1
      ∈ LinearMap.range (fderiv ℝ F z : R2 →ₗ[ℝ] R4)

end SliceRibbon


