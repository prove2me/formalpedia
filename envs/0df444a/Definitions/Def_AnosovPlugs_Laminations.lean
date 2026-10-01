-- Prove2me | Definitions.Def_AnosovPlugs_Laminations
-- name    : AnosovPlugs_Laminations
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-01T01:40:31.846121+00:00
-- url     : https://prove2.me/theorems/7ce3558e-34ad-467c-a330-4b088cad4eca
-- title:
--   Anosov plugs IV: strips, filling MS laminations, strong transversality, gluing maps
-- statement:
--   Let $(V,X)$ be as in the previous definitions.
--
--   1. **Accessible boundary** of $C\subset V$: points $p\notin C$ which are the endpoint of an arc whose other points lie in $C$.
--   2. **Asymptotic lines.** $L_1,L_2$ are asymptotic at both ends if they have continuous injective parametrisations $c_1,c_2:\mathbb R\to V$ with $(c_1(t),c_2(t))\to$ diagonal as $t\to\pm\infty$.
--   3. **Strip** (Definition 3.11). A complementary component $C$ of a lamination $L$ is a strip if $C\cong\mathbb R^2$ and its accessible boundary consists of exactly two distinct leaves of $L$, asymptotic to each other at both ends.
--   4. **Filling MS laminations** (Definition 3.18, Lemma 3.21). A hyperbolic plug has filling MS laminations if every component of $\partial^{in}V\setminus L^s$ is a strip for $L^s$ and every component of $\partial^{out}V\setminus L^u$ is a strip for $L^u$.
--   5. **Transversality of leaves** at $p$: the two leaves contain C¹ curves through $p$ with linearly independent velocities.
--   6. **Strong transversality** (Definition 3.25). $L_1,L_2$ on a surface $S$ are strongly transverse if they are transverse at every point of $L_1\cap L_2$ and every component of $S\setminus(L_1\cup L_2)$ is a disc whose closure is the image of $[0,1]^2$ by a C¹ immersion, injective on $(0,1)^2$, with $[0,1]\times\{0,1\}$ mapped into leaves of $L_1$ and $\{0,1\}\times[0,1]$ into leaves of $L_2$.
--   7. **Boundary diffeomorphism**: $\varphi$ maps $S$ bijectively onto $T$, is C¹ along $S$ and has a C¹ inverse along $T$.
--   8. **Strongly transverse gluing map** (§1.3): a boundary diffeomorphism $\varphi:\partial^{out}V\to\partial^{in}V$ such that $\varphi_*(L^u_X)$ and $L^s_X$ are strongly transverse.
--
--   **Formalization Note** The MS properties (finitely many compact leaves, asymptotic half-leaves, contracting holonomy) hold automatically for the laminations of hyperbolic plugs (Proposition 3.8), so by Lemma 3.21 only the strip condition is imposed.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, Definitions 3.11 (p. 1855), 3.18 and Lemma 3.21 (pp. 1858–1859), Definition 3.25 (pp. 1861–1862), §1.3

import Mathlib
import Definitions.Def_AnosovPlugs_Plugs

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017).
Strips and hyperbolic plugs with filling MS laminations (Definitions 3.11, 3.18, Lemma 3.21),
transversality and strong transversality of laminations (Definition 3.25), boundary
diffeomorphisms and strongly transverse gluing maps (§1.3).
-/

open scoped Manifold ContDiff Topology
open Set Filter Function

namespace AnosovPlugs

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold I3 ∞ M]

/-- The accessible boundary of `C ⊆ M`: the points `p ∉ C` which are an endpoint of an arc
(a continuous injective image of `[0,1]`) whose other points all lie in `C`. -/
def accessibleBoundary (C : Set M) : Set M :=
  {p | p ∉ C ∧ ∃ γ : ℝ → M, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ γ 0 = p ∧
    γ '' Ioc 0 1 ⊆ C}

/-- `L₁` and `L₂` are (non-compact) lines asymptotic to each other at both ends: they admit
continuous injective parametrisations `c₁, c₂ : ℝ → M` with `(c₁ t, c₂ t)` tending to the
diagonal both as `t → +∞` and as `t → -∞`. -/
def AsymptoticLines (L₁ L₂ : Set M) : Prop :=
  ∃ c₁ c₂ : ℝ → M, Continuous c₁ ∧ Continuous c₂ ∧ Injective c₁ ∧ Injective c₂ ∧
    range c₁ = L₁ ∧ range c₂ = L₂ ∧
    Tendsto (fun t => (c₁ t, c₂ t)) atTop (𝓝ˢ (diagonal M)) ∧
    Tendsto (fun t => (c₁ t, c₂ t)) atBot (𝓝ˢ (diagonal M))

/-- Definition 3.11: a complementary component `C` of a lamination `L` (whose leaf through a
point `p ∈ L` is `leaf p`) is a strip if `C` is homeomorphic to `ℝ²` and its accessible
boundary consists of exactly two distinct leaves of `L`, which are non-compact lines asymptotic
to each other at both ends. -/
def IsStrip (L : Set M) (leaf : M → Set M) (C : Set M) : Prop :=
  Nonempty (C ≃ₜ ℝ × ℝ) ∧ ∃ p₁ ∈ L, ∃ p₂ ∈ L, leaf p₁ ≠ leaf p₂ ∧
    accessibleBoundary C = leaf p₁ ∪ leaf p₂ ∧ AsymptoticLines (leaf p₁) (leaf p₂)

/-- The entrance and exit laminations of `X` are filling (Definition 3.18, Lemma 3.21): every
connected component of `∂^{in} M ∖ L^s` is a strip for the entrance lamination `L^s`, and every
connected component of `∂^{out} M ∖ L^u` is a strip for the exit lamination `L^u`. -/
def HasFillingLaminations (X : (x : M) → TangentSpace I3 x) : Prop :=
  (∀ p ∈ inBoundary X \ entranceLamination X,
      IsStrip (entranceLamination X) (entranceLeaf X)
        (connectedComponentIn (inBoundary X \ entranceLamination X) p)) ∧
    (∀ p ∈ outBoundary X \ exitLamination X,
      IsStrip (exitLamination X) (exitLeaf X)
        (connectedComponentIn (outBoundary X \ exitLamination X) p))

/-- A hyperbolic plug with filling MS laminations (Definition 3.18, Lemma 3.21). (For hyperbolic
plugs the MS-lamination properties of `L^s`, `L^u` hold automatically, Proposition 3.8, so only
the strip condition on complementary components is imposed.) -/
def IsFillingHyperbolicPlug (X : (x : M) → TangentSpace I3 x) : Prop :=
  IsHyperbolicPlug X ∧ HasFillingLaminations X

/-- Two leaves `ℓ₁, ℓ₂` through `p` are transverse at `p`: they contain C¹ curves through `p`
(at time `0`) whose velocity vectors at `p` are linearly independent. -/
def CurvesTransverseAt (ℓ₁ ℓ₂ : Set M) (p : M) : Prop :=
  ∃ c₁ c₂ : ℝ → M, c₁ 0 = p ∧ c₂ 0 = p ∧ range c₁ ⊆ ℓ₁ ∧ range c₂ ⊆ ℓ₂ ∧
    ContMDiff 𝓘(ℝ, ℝ) I3 1 c₁ ∧ ContMDiff 𝓘(ℝ, ℝ) I3 1 c₂ ∧
    LinearIndependent ℝ ![(mfderiv 𝓘(ℝ, ℝ) I3 c₁ 0 1 : EuclideanSpace ℝ (Fin 3)),
      (mfderiv 𝓘(ℝ, ℝ) I3 c₂ 0 1 : EuclideanSpace ℝ (Fin 3))]

/-- Second item of Definition 3.25: `C` is a disc whose closure is the image of the square
`[0,1]²` by a C¹ immersion `F` which is injective on `(0,1)²` with `F((0,1)²) = C`, such that
`[0,1] × {0}` and `[0,1] × {1}` are mapped into leaves of `L₁` and `{0} × [0,1]`,
`{1} × [0,1]` into leaves of `L₂`. -/
def IsSquareComponent (L₁ L₂ : Set M) (leaf₁ leaf₂ : M → Set M) (C : Set M) : Prop :=
  ∃ F : ℝ × ℝ → M,
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I3 1 F (Icc 0 1 ×ˢ Icc 0 1) ∧
    (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      Injective (mfderivWithin 𝓘(ℝ, ℝ × ℝ) I3 F (Icc 0 1 ×ˢ Icc 0 1) z)) ∧
    InjOn F (Ioo 0 1 ×ˢ Ioo 0 1) ∧ F '' (Ioo 0 1 ×ˢ Ioo 0 1) = C ∧
    F '' (Icc 0 1 ×ˢ Icc 0 1) = closure C ∧
    (∃ p ∈ L₁, F '' (Icc 0 1 ×ˢ {0}) ⊆ leaf₁ p) ∧ (∃ p ∈ L₁, F '' (Icc 0 1 ×ˢ {1}) ⊆ leaf₁ p) ∧
    (∃ p ∈ L₂, F '' ({0} ×ˢ Icc 0 1) ⊆ leaf₂ p) ∧ (∃ p ∈ L₂, F '' ({1} ×ˢ Icc 0 1) ⊆ leaf₂ p)

/-- Definition 3.25: the laminations `L₁, L₂` of the surface `S` (with leaf maps `leaf₁`,
`leaf₂`) are strongly transverse: their leaves are transverse at every point of `L₁ ∩ L₂`, and
every connected component of `S ∖ (L₁ ∪ L₂)` is a square component. -/
def StronglyTransverse (S L₁ L₂ : Set M) (leaf₁ leaf₂ : M → Set M) : Prop :=
  (∀ p ∈ L₁ ∩ L₂, CurvesTransverseAt (leaf₁ p) (leaf₂ p) p) ∧
    ∀ p ∈ S \ (L₁ ∪ L₂),
      IsSquareComponent L₁ L₂ leaf₁ leaf₂ (connectedComponentIn (S \ (L₁ ∪ L₂)) p)

/-- `T` is a union of connected components of `S`. -/
def IsUnionOfComponents (T S : Set M) : Prop :=
  T ⊆ S ∧ ∀ p ∈ T, connectedComponentIn S p ⊆ T

variable {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
  [IsManifold I3 ∞ N]

/-- `φ` restricts to a C¹ diffeomorphism from `S ⊆ M` onto `T ⊆ N`: it maps `S` bijectively
onto `T`, is C¹ along `S`, and has an inverse `T → S` which is C¹ along `T`. -/
def IsBoundaryDiffeo (φ : M → N) (S : Set M) (T : Set N) : Prop :=
  BijOn φ S T ∧ ContMDiffOn I3 I3 1 φ S ∧
    ∃ ψ : N → M, ContMDiffOn I3 I3 1 ψ T ∧ (∀ x ∈ S, ψ (φ x) = x) ∧ ∀ y ∈ T, φ (ψ y) = y

/-- Leaves of the image lamination `φ_*(L)`: the leaf through `p` is the image under `φ` of the
leaf through the (unique, when `φ` is injective on `S`) preimage `q ∈ S` of `p`. -/
def pushLeaf (φ : M → N) (S : Set M) (leaf : M → Set M) (p : N) : Set N :=
  ⋃ q ∈ {q | q ∈ S ∧ φ q = p}, φ '' leaf q

/-- `φ : ∂^{out} M → ∂^{in} M` is a strongly transverse gluing diffeomorphism for `(M, X)`: a
C¹ diffeomorphism from the exit boundary onto the entrance boundary such that `φ_*(L^u_X)` and
`L^s_X` are strongly transverse on `∂^{in} M`. -/
def IsStronglyTransverseGluing (X : (x : M) → TangentSpace I3 x) (φ : M → M) : Prop :=
  IsBoundaryDiffeo φ (outBoundary X) (inBoundary X) ∧
    StronglyTransverse (inBoundary X) (φ '' exitLamination X) (entranceLamination X)
      (pushLeaf φ (outBoundary X) (exitLeaf X)) (entranceLeaf X)

end AnosovPlugs


