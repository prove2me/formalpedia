-- Prove2me | Definitions.Def_Geometrization_Basic
-- name    : Geometrization_Basic
-- status  : Definition
-- author  : @korbonits
-- created : 2026-11-20T02:08:35.235076+00:00
-- url     : https://prove2.me/theorems/ff526789-074a-4559-bda0-5314b60265d6
-- title:
--   Closed orientable prime 3-manifolds, embedded tori and Klein bottles, locally homogeneous metrics of finite volume
-- statement:
--   Vocabulary for the Geometrization Conjecture in the smooth category, with charts in $\mathbb{R}^3$.
--
--   - **Orientable**: $M$ has an atlas of smooth charts whose transition maps have positive Jacobian determinant.
--   - **Prime**: $M \not\cong S^3$, and $M$ is not a connected sum $M_1 \# M_2$ with neither $M_i \cong S^3$. This is stated in the standard equivalent form: every smoothly embedded 2-sphere that separates $M$ has a complementary component diffeomorphic to $\mathbb{R}^3$, i.e. it bounds a ball.
--   - **Torus/Klein-bottle system**: finitely many smooth immersions $f_i : T^2 = S^1\times S^1 \to M$ with pairwise disjoint images. Each $f_i$ is either injective (an embedded torus) or identifies exactly the pairs $\{p, \tau p\}$ for the free involution $\tau(z,w) = (-z,\bar w)$ (an embedded Klein bottle $T^2/\tau$).
--   - **Riemannian 3-manifold**: a smooth 3-manifold with a smooth Riemannian metric whose extended distance is the Riemannian path-length distance.
--   - **Homogeneous**: connected, with an isometry group that acts transitively.
--   - **Locally homogeneous**: $N = \Gamma\backslash X$ with $X$ homogeneous and $\Gamma$ a discrete group of isometries acting freely. This is encoded as the existence of a smooth surjective covering map $X \to N$ that is a local isometry.
--   - **Finite volume**: $\mathcal{H}^3(N) < \infty$ for the 3-dimensional Hausdorff measure of the Riemannian distance, which is comparable to the Riemannian volume.
-- source:
--   J. Morgan, G. Tian, The Geometrization Conjecture, Clay Mathematics Monographs 5, AMS 2014 (https://www.claymath.org/library/monographs/cmim05c.pdf); statement transcribed from its arXiv precursor, Morgan–Tian, Completion of the proof of the Geometrization Conjecture, https://arxiv.org/abs/0809.4040, p. 1 (statement of the Geometrization Conjecture, the definitions of locally homogeneous metric and of prime 3-manifold).

import Mathlib

/-!
# Closed orientable prime 3-manifolds, embedded tori and Klein bottles, locally homogeneous metrics

Source: J. Morgan and G. Tian, *The Geometrization Conjecture*, Clay Mathematics Monographs 5
(AMS, 2014); statement as in the introduction of its arXiv precursor
*Completion of the proof of the Geometrization Conjecture*, arXiv:0809.4040, p. 1.
-/

open scoped Manifold ContDiff
open Set Metric Bundle

namespace Geometrization

/-- Euclidean 3-space, the model space of a 3-manifold. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The unit 2-sphere in `ℝ³`. -/
abbrev S2 := ↥(sphere (0 : E3) 1)

/-- The unit 3-sphere in `ℝ⁴`. -/
abbrev S3 := ↥(sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

/-- The 2-torus `S¹ × S¹`, with its product smooth structure. -/
abbrev T2 := Circle × Circle

/-- The model with corners of `T2`. -/
noncomputable abbrev 𝓘T2 := (𝓡 1).prod (𝓡 1)

/-- The fixed-point-free involution `(z, w) ↦ (-z, w̄)` of the torus; the quotient `T2 / τ`
is the Klein bottle. -/
noncomputable def kleinInvolution (p : T2) : T2 :=
  (Circle.exp Real.pi * p.1, p.2⁻¹)

variable (M : Type) [TopologicalSpace M] [ChartedSpace E3 M]

/-- A smooth 3-manifold is orientable if it has an atlas of charts from its maximal smooth atlas
whose transition maps all have positive Jacobian determinant. -/
def IsOrientable : Prop :=
  ∃ A : Set (OpenPartialHomeomorph M E3),
    A ⊆ IsManifold.maximalAtlas (𝓡 3) ∞ M ∧
    (∀ x : M, ∃ e ∈ A, x ∈ e.source) ∧
    ∀ e ∈ A, ∀ e' ∈ A, ∀ y ∈ (e.symm.trans e').source,
      0 < (fderiv ℝ (e.symm.trans e') y).det

/-- A smooth embedding of the 2-sphere: a smooth injective immersion `S² → M`
(an embedding, since `S²` is compact). -/
structure SphereEmbedding where
  toFun : S2 → M
  smooth : ContMDiff (𝓡 2) (𝓡 3) ∞ toFun
  immersion : ∀ p, Function.Injective (mfderiv (𝓡 2) (𝓡 3) toFun p)
  injective : Function.Injective toFun

variable [IsManifold (𝓡 3) ∞ M]

/-- `M` is prime: it is not diffeomorphic to `S³`, and it is not a connected sum `M₁ # M₂` with
neither summand diffeomorphic to `S³`. The second clause is stated in its standard equivalent
form: every smoothly embedded 2-sphere that separates `M` bounds a ball, i.e. some component of
its complement is diffeomorphic to `ℝ³`. -/
def IsPrime : Prop :=
  IsEmpty (M ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ S3) ∧
  ∀ φ : SphereEmbedding M, ¬ IsConnected (range φ.toFun)ᶜ →
    ∃ U : TopologicalSpace.Opens M, ∃ x ∉ range φ.toFun,
      (U : Set M) = connectedComponentIn (range φ.toFun)ᶜ x ∧
      Nonempty (U ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ E3)

/-- A finite disjoint union of smoothly embedded 2-tori and Klein bottles in `M`. Component `i` is
parametrized by a smooth immersion `map i : T² → M` that is injective (a torus), or, when
`klein i`, identifies exactly the pairs `p, τ p` (so it embeds the Klein bottle `T² / τ`). -/
structure TorusKleinSystem where
  n : ℕ
  map : Fin n → T2 → M
  klein : Fin n → Bool
  smooth : ∀ i, ContMDiff 𝓘T2 (𝓡 3) ∞ (map i)
  immersion : ∀ i p, Function.Injective (mfderiv 𝓘T2 (𝓡 3) (map i) p)
  fibres : ∀ i p q, map i p = map i q ↔ (q = p ∨ (klein i = true ∧ q = kleinInvolution p))
  disjoint : ∀ i j, i ≠ j → Disjoint (range (map i)) (range (map j))

/-- The union of the surfaces of a `TorusKleinSystem`. -/
def TorusKleinSystem.carrier {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    (S : TorusKleinSystem M) : Set M :=
  ⋃ i, range (S.map i)

end Geometrization

namespace Geometrization

/-- A smooth Riemannian 3-manifold: a smooth 3-manifold with a smooth Riemannian metric on its
tangent bundle, whose (extended) distance is the Riemannian distance. It carries its Borel
σ-algebra so that its 3-dimensional Hausdorff measure (= Riemannian volume) is available. -/
structure RiemannianThreeManifold where
  carrier : Type
  [emetric : EMetricSpace carrier]
  [charted : ChartedSpace E3 carrier]
  [manifold : IsManifold (𝓡 3) ∞ carrier]
  [bundle : Bundle.RiemannianBundle (fun x : carrier ↦ TangentSpace (𝓡 3) x)]
  [smoothMetric : IsContMDiffRiemannianBundle (𝓡 3) ∞ E3 (fun x : carrier ↦ TangentSpace (𝓡 3) x)]
  [riemannian : IsRiemannianManifold (𝓡 3) carrier]
  [measurable : MeasurableSpace carrier]
  [borel : BorelSpace carrier]

attribute [instance] RiemannianThreeManifold.emetric RiemannianThreeManifold.charted
  RiemannianThreeManifold.manifold RiemannianThreeManifold.bundle
  RiemannianThreeManifold.smoothMetric RiemannianThreeManifold.riemannian
  RiemannianThreeManifold.measurable RiemannianThreeManifold.borel

instance : CoeSort RiemannianThreeManifold Type := ⟨RiemannianThreeManifold.carrier⟩

/-- Homogeneous: connected, and the isometry group acts transitively. -/
def RiemannianThreeManifold.IsHomogeneous (X : RiemannianThreeManifold) : Prop :=
  ConnectedSpace X ∧ ∀ x y : X, ∃ f : X ≃ᵢ X, f x = y

/-- Locally homogeneous in the source's sense: `N` is the quotient of a homogeneous Riemannian
manifold `X` by a discrete group of isometries acting freely, encoded as: there is a smooth
surjective covering map `X → N` that is a local isometry. (Such an `N` is complete and locally
homogeneous, hence the quotient of its homogeneous universal cover by `π₁(N)`; conversely
`X → Γ \ X` is such a covering.) -/
def RiemannianThreeManifold.IsLocallyHomogeneous (N : RiemannianThreeManifold) : Prop :=
  ∃ X : RiemannianThreeManifold, X.IsHomogeneous ∧
    ∃ p : X → N, IsCoveringMap p ∧ Function.Surjective p ∧ ContMDiff (𝓡 3) (𝓡 3) ∞ p ∧
      ∀ x : X, ∃ U ∈ nhds x, ∀ y ∈ U, ∀ z ∈ U, edist (p y) (p z) = edist y z

/-- Finite Riemannian volume, measured by the 3-dimensional Hausdorff measure of the Riemannian
distance; on a Riemannian 3-manifold this is a constant multiple of the Riemannian volume, so
the two have the same finiteness. -/
def RiemannianThreeManifold.HasFiniteVolume (N : RiemannianThreeManifold) : Prop :=
  MeasureTheory.Measure.hausdorffMeasure 3 (univ : Set N) < ⊤

/-- An open subset `U` of a smooth 3-manifold admits a locally homogeneous Riemannian metric of
finite volume: `U` is diffeomorphic to a locally homogeneous Riemannian 3-manifold of finite
volume. -/
def AdmitsFiniteVolumeLocallyHomogeneousMetric {M : Type} [TopologicalSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M] (U : TopologicalSpace.Opens M) : Prop :=
  ∃ N : RiemannianThreeManifold, N.IsLocallyHomogeneous ∧ N.HasFiniteVolume ∧
    Nonempty (U ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ N)

end Geometrization


