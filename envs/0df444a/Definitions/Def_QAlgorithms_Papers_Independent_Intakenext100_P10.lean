-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P10
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P10
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T23:37:51.269418+00:00
-- url     : https://prove2.me/theorems/3ab95326-10b0-41fc-ab5d-1753477a05df
-- title:
--   Definitions for Non-integral central extensions of loop groups
-- statement:
--   The objects the formalized statements of *Non-integral central extensions of loop groups* (arXiv:0910.1937) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SmoothOn`: PDF pp. 1–2: smoothness on an open subset, in the actual source and target atlases. The body is the real part of accepted Renew46.P29.ManifoldSmoothOn.
--   - `SequentiallyComplete`: PDF p. 1: sequential completeness, expressed in the additive group uniformity using differences and zero neighborhoods. It is not completeness of all nets.
--   - `SmoothAtlas`: PDF p. 1: compatibility of the supplied locally convex smooth atlas.
--   - `IsLieGroup`: PDF p. 1: the given group and atlas form a Hausdorff locally convex Lie group. Multiplication is jointly smooth.
--   - `IsAddLieGroup`: PDF pp. 1–2: the given coefficient group and atlas form an additive Lie group.
--   - `QuotientCoefficientAtlas`: PDF pp. 1–2: the canonical smooth structure on the actual quotient F/Gamma. The quotient topology and group are Mathlib's. The quotient projection is a local smooth isomorphism, which pins its smooth structure; this is standing coefficient geometry, not the extension or Cech conclusion.
--   - `translatedOpen`: PDF p. 4: gV, written as an inverse image so its overlap domain is explicit.
--   - `translatedTau`: PDF p. 4, Lemma 2.2: the source's transition sign convention.
--   - `translatedComparison`: PDF p. 4, proof of Lemma 2.2: the actual comparison zero-cochain.
--   - `OpenCover`: PDF p. 4: genuine open covers, including the covering condition.
--   - `IsSmoothCechCocycle`: PDF p. 4: a smooth Cech one-cocycle on its actual overlaps; empty overlaps impose no constraints. Values outside the domain do not enter the definition.
--   - `CechRepresentative`: PDF p. 4: cocycle representatives with their covers retained.
--   - `CechRelated`: PDF p. 4: equality of smooth Cech classes through a common open refinement and a smooth zero-cochain. This uses all open covers, without good-cover or paracompactness restrictions.
--   - `SmoothCechH1`: PDF p. 4: the first smooth Cech cohomology as actual classes of cocycles under open-cover refinement and coboundary. Quot generates the equivalence relation; no theorem is encoded as a definition or an assumed class map.
--   - `cechClass`: The actual class projection, PDF p. 4. Only its carrier is needed here.
--   - `translatedCover`: PDF p. 4: all translates of an open identity neighborhood cover G. No compactness, local finiteness or countable index assumption is imposed.
--   - `TwistedCarrier`: PDF pp. 3–4: the actual set-theoretic product, with no preinstalled product topology on the extension. Its topology is part of the conclusion.
--   - `twistedCarrierMul`: PDF p. 3: transport the accepted central twisted multiplication through the actual coefficient/base coordinates of the carrier. No topology is imposed.
--   - `twistedInv`: PDF p. 3: the specified inverse in the central twisted extension.
--   - `coefficientAction`: PDF p. 4: the right principal coefficient action, in additive notation.
--   - `twistedBundleChart`: PDF p. 4: translated local trivializations with base coordinate first, computed from the source section sigma_g(x)=(f(g,g^-1*x),x).
--   - `twistedBundleChartInverse`: PDF p. 4: the inverse of the actual translated local trivialization.
-- source:
--   Non-integral central extensions of loop groups, arXiv:0910.1937v1, https://arxiv.org/abs/0910.1937v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P18

/-!
Statements from Christoph Wockel, Non-integral central extensions of loop groups,
arXiv:0910.1937v1. All new definitions are confined to this paper.
The real directional calculus, locally convex models and normalized cocycles
reuse pinned accepted Next46.P35 and Renew46.P29 definitions. Central twisted
multiplication reuses pinned Renew46.P18 through the carrier coordinate adapter.
Compilation and independent moderation are pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P10

open Set Filter Topology

universe u

open QAlgorithms.Papers.Independent.Next46.P35 (DirectionalSmoothOn)
open QAlgorithms.Papers.Independent.Renew46.P29 (LocallyConvexModel NormalizedTwoCocycle)

/-- PDF p. 2: central coefficients have the trivial group action. This local
 instance specializes the accepted general normalized cocycle definition. -/
local instance centralCoefficientAction (G A : Type u) [Group G] [AddCommGroup A] :
    DistribMulAction G A where
  smul := fun _ a => a
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

/-- PDF pp. 1–2: smoothness on an open subset, in the actual source and target
 atlases. The body is the real part of accepted Renew46.P29.ManifoldSmoothOn. -/
def SmoothOn {E F M N : Type u}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N] (U : Set M) (f : M → N) : Prop :=
  ContinuousOn f U ∧
    ∀ c ∈ atlas E M, ∀ e ∈ atlas F N,
      DirectionalSmoothOn
        (c.target ∩ (fun x => c.symm x) ⁻¹' U ∩
          (fun x => f (c.symm x)) ⁻¹' e.source)
        (fun x => e (f (c.symm x)))

/-- PDF p. 1: sequential completeness, expressed in the additive group
 uniformity using differences and zero neighborhoods. It is not completeness of all nets. -/
def SequentiallyComplete (F : Type u) [AddCommGroup F] [TopologicalSpace F] : Prop :=
  ∀ s : ℕ → F,
    (∀ U ∈ 𝓝 (0 : F), ∃ n : ℕ, ∀ i ≥ n, ∀ j ≥ n, s i - s j ∈ U) →
    ∃ x : F, Tendsto s atTop (𝓝 x)

/-- PDF p. 1: compatibility of the supplied locally convex smooth atlas. -/
def SmoothAtlas (E M : Type u) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [TopologicalSpace M] [ChartedSpace E M] : Prop :=
  ∀ c ∈ atlas E M, ∀ e ∈ atlas E M,
    DirectionalSmoothOn (c.symm.trans e).source (c.symm.trans e)

/-- The ordinary product atlas, used for joint smoothness rather than slices. -/
local instance productCharts
    (E F M N : Type u) [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N] : ChartedSpace (E × F) (M × N) :=
  prodChartedSpace E M F N

/-- PDF p. 1: the given group and atlas form a Hausdorff locally convex Lie
 group. Multiplication is jointly smooth. -/
def IsLieGroup (E G : Type u) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [Group G] [TopologicalSpace G] [ChartedSpace E G] : Prop :=
  LocallyConvexModel ℝ E ∧ T2Space G ∧ SmoothAtlas E G ∧
    SmoothOn (E := E × E) (F := E) Set.univ (fun p : G × G => p.1 * p.2) ∧
    SmoothOn (E := E) (F := E) Set.univ (fun g : G => g⁻¹)

/-- PDF pp. 1–2: the given coefficient group and atlas form an additive Lie group. -/
def IsAddLieGroup (F A : Type u) [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [AddCommGroup A] [TopologicalSpace A]
    [ChartedSpace F A] : Prop :=
  LocallyConvexModel ℝ F ∧ T2Space A ∧ SmoothAtlas F A ∧
    SmoothOn (E := F × F) (F := F) Set.univ (fun p : A × A => p.1 + p.2) ∧
    SmoothOn (E := F) (F := F) Set.univ (fun a : A => -a)

/-- PDF pp. 1–2: the canonical smooth structure on the actual quotient F/Gamma.
 The quotient topology and group are Mathlib's. The quotient projection is a
 local smooth isomorphism, which pins its smooth structure; this is standing
 coefficient geometry, not the extension or Cech conclusion. -/
def QuotientCoefficientAtlas (F : Type u) [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] (Gamma : AddSubgroup F)
    [ChartedSpace F (F ⧸ Gamma)] : Prop :=
  IsAddLieGroup F (F ⧸ Gamma) ∧
    ∀ x : F, ∃ e : OpenPartialHomeomorph F (F ⧸ Gamma),
      x ∈ e.source ∧
      (∀ y ∈ e.source, e y = (QuotientAddGroup.mk y : F ⧸ Gamma)) ∧
      SmoothOn (E := F) (F := F) e.source e ∧
      SmoothOn (E := F) (F := F) e.target e.symm

/-- PDF p. 4: gV, written as an inverse image so its overlap domain is explicit. -/
def translatedOpen {G : Type u} [Group G] (V : Set G) (g : G) : Set G :=
  {x | g⁻¹ * x ∈ V}

/-- PDF p. 4, Lemma 2.2: the source's transition sign convention. -/
def translatedTau {G A : Type u} [Group G] [AddCommGroup A]
    (f : G → G → A) (g h x : G) : A :=
  f g (g⁻¹ * x) - f h (h⁻¹ * x)

/-- PDF p. 4, proof of Lemma 2.2: the actual comparison zero-cochain. -/
def translatedComparison {G A : Type u} [Group G] [AddCommGroup A]
    (b : G → A) (g x : G) : A :=
  b g + b (g⁻¹ * x)

section Cech

variable {E F X A : Type u}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [TopologicalSpace X] [ChartedSpace E X]
variable [AddCommGroup A] [TopologicalSpace A] [ChartedSpace F A]

/-- PDF p. 4: genuine open covers, including the covering condition. -/
structure OpenCover (X : Type u) [TopologicalSpace X] where
  Index : Type u
  domain : Index → Set X
  isOpen : ∀ i, IsOpen (domain i)
  covers : ∀ x, ∃ i, x ∈ domain i

/-- PDF p. 4: a smooth Cech one-cocycle on its actual overlaps; empty overlaps
 impose no constraints. Values outside the domain do not enter the definition. -/
def IsSmoothCechCocycle (C : OpenCover X) (t : C.Index → C.Index → X → A) : Prop :=
  (∀ i j, SmoothOn (E := E) (F := F) (C.domain i ∩ C.domain j) (t i j)) ∧
    ∀ i j k x, x ∈ C.domain i → x ∈ C.domain j → x ∈ C.domain k →
      t i j x - t i k x + t j k x = 0

/-- PDF p. 4: cocycle representatives with their covers retained. -/
structure CechRepresentative where
  cover : OpenCover X
  value : cover.Index → cover.Index → X → A
  cocycle : IsSmoothCechCocycle (E := E) (F := F) cover value

/-- PDF p. 4: equality of smooth Cech classes through a common open refinement
 and a smooth zero-cochain. This uses all open covers, without good-cover or
 paracompactness restrictions. -/
def CechRelated
    (c d : CechRepresentative (E := E) (F := F) (X := X) (A := A)) : Prop :=
  ∃ (R : OpenCover X) (r : R.Index → c.cover.Index) (s : R.Index → d.cover.Index),
    (∀ i, R.domain i ⊆ c.cover.domain (r i)) ∧
    (∀ i, R.domain i ⊆ d.cover.domain (s i)) ∧
    ∃ b : R.Index → X → A,
      (∀ i, SmoothOn (E := E) (F := F) (R.domain i) (b i)) ∧
      ∀ i j x, x ∈ R.domain i → x ∈ R.domain j →
        c.value (r i) (r j) x - d.value (s i) (s j) x = b i x - b j x

/-- PDF p. 4: the first smooth Cech cohomology as actual classes of cocycles
 under open-cover refinement and coboundary. Quot generates the equivalence
 relation; no theorem is encoded as a definition or an assumed class map. -/
def SmoothCechH1 :=
  Quot (CechRelated (E := E) (F := F) (X := X) (A := A))

/-- The actual class projection, PDF p. 4. Only its carrier is needed here. -/
def cechClass (c : CechRepresentative (E := E) (F := F) (X := X) (A := A)) :
    SmoothCechH1 (E := E) (F := F) (X := X) (A := A) := Quot.mk _ c

end Cech

/-- PDF p. 4: all translates of an open identity neighborhood cover G.
 No compactness, local finiteness or countable index assumption is imposed. -/
def translatedCover {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (V : Set G) (hOpen : IsOpen V) (hOne : (1 : G) ∈ V) :
    OpenCover G where
  Index := G
  domain := translatedOpen V
  isOpen := fun g => hOpen.preimage (continuous_const.mul continuous_id)
  covers := by
    intro x
    refine ⟨x, ?_⟩
    simpa [translatedOpen] using hOne

/-- Sanity: zero cocycles are normalized, and zero comparison cochains
 give zero transitions, including the singleton group and empty overlaps. -/
example {G A : Type u} [Group G] [AddCommGroup A] (g h x : G) :
    NormalizedTwoCocycle (fun _ _ : G => (0 : A)) ∧
    translatedTau (fun _ _ : G => (0 : A)) g h x = 0 ∧
    translatedComparison (fun _ : G => (0 : A)) g x = 0 := by
  simp [NormalizedTwoCocycle, centralCoefficientAction, translatedTau, translatedComparison]

/-- Sanity: the directional smoothness definition supplies the actual zero
 derivative tower. -/
example {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] (U : Set E) :
    DirectionalSmoothOn U (fun _ : E => (0 : F)) := by
  refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
  · intro x hx
    rfl
  · intro n
    exact continuousOn_const
  · intro n x hx a h
    simpa only [sub_self, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

/-- Sanity: the Cech relation on a singleton coefficient is witnessed by
 the original cover and the actual smooth zero-cochain, rather than by
 postulating an equivalence relation or ignoring regularity. -/
example {E X : Type u}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [TopologicalSpace X] [ChartedSpace E X]
    (c : CechRepresentative (E := E) (F := PUnit.{u + 1}) (X := X) (A := PUnit.{u + 1})) :
    CechRelated c c := by
  have hz (U : Set X) :
      SmoothOn (E := E) (F := PUnit.{u + 1}) U (fun _ : X => (0 : PUnit.{u + 1})) := by
    refine ⟨continuousOn_const, ?_⟩
    intro a ha b hb
    refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro x hx
      exact Subsingleton.elim _ _
    · intro n
      exact continuousOn_const
    · intro n x hx v h
      simpa only [sub_self, smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : PUnit.{u + 1}))
          (𝓝[≠] (0 : ℝ)) (𝓝 (0 : PUnit.{u + 1})))
  refine ⟨c.cover, id, id, ?_, ?_, (fun _ _ => 0), ?_, ?_⟩
  · intro i
    exact Set.Subset.rfl
  · intro i
    exact Set.Subset.rfl
  · intro i
    exact hz _
  · intro i j x hi hj
    exact Subsingleton.elim _ _

/-- Sanity: the zero-dimensional singleton has the actual locally convex
 Lie and additive Lie geometry, a compatible atlas and sequential completeness.
 Thus the geometric standing assumptions do not exclude the trivial group. -/
example :
    LocallyConvexModel ℝ PUnit.{1} ∧
    SmoothAtlas PUnit.{1} PUnit.{1} ∧
    IsLieGroup PUnit.{1} PUnit.{1} ∧
    IsAddLieGroup PUnit.{1} PUnit.{1} ∧
    SequentiallyComplete PUnit.{1} := by
  have hs : ∀ {D : Type} [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
      (U : Set D) (f : D → PUnit.{1}), DirectionalSmoothOn U f := by
    intro D _ _ _ U f
    refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro x hx
      exact Subsingleton.elim _ _
    · intro n
      exact continuousOn_const
    · intro n x hx a h
      simpa only [sub_self, smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : PUnit.{1}))
          (𝓝[≠] (0 : ℝ)) (𝓝 (0 : PUnit.{1})))
  have hm : ∀ {D X : Type} [AddCommGroup D] [Module ℝ D]
      [TopologicalSpace D] [TopologicalSpace X] [ChartedSpace D X]
      (U : Set X) (f : X → PUnit.{1}),
      SmoothOn (E := D) (F := PUnit.{1}) U f := by
    intro D X _ _ _ _ _ U f
    refine ⟨?_, ?_⟩
    · have hf : f = fun _ => PUnit.unit := funext (fun _ => Subsingleton.elim _ _)
      rw [hf]
      exact continuousOn_const
    · intro c hc e he
      exact hs _ _
  have hModel : LocallyConvexModel ℝ PUnit.{1} := by
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    exact ⟨inferInstance, inferInstance⟩
  have hAtlas : SmoothAtlas PUnit.{1} PUnit.{1} := by
    intro c hc e he
    exact hs _ _
  refine ⟨hModel, hAtlas, ?_, ?_, ?_⟩
  · exact ⟨hModel, inferInstance, hAtlas, hm Set.univ _, hm Set.univ _⟩
  · exact ⟨hModel, inferInstance, hAtlas, hm Set.univ _, hm Set.univ _⟩
  · intro sequence hCauchy
    refine ⟨0, ?_⟩
    have h : sequence = fun _ => (0 : PUnit.{1}) :=
      funext (fun _ => Subsingleton.elim _ _)
    rw [h]
    exact tendsto_const_nhds

/-- PDF pp. 3–4: the actual set-theoretic product, with no preinstalled
 product topology on the extension. Its topology is part of the conclusion. -/
structure TwistedCarrier (G A : Type u) where
  coeff : A
  base : G

/-- PDF p. 3: transport the accepted central twisted multiplication through
 the actual coefficient/base coordinates of the carrier. No topology is imposed. -/
def twistedCarrierMul {G A : Type u} [Group G] [AddCommGroup A]
    (f : G → G → A) (x y : TwistedCarrier G A) : TwistedCarrier G A :=
  let p := QAlgorithms.Papers.Independent.Renew46.P18.twistedMul f
    (x.coeff, x.base) (y.coeff, y.base)
  ⟨p.1, p.2⟩

/-- PDF p. 3: the specified inverse in the central twisted extension. -/
def twistedInv {G A : Type u} [Group G] [AddCommGroup A]
    (f : G → G → A) (x : TwistedCarrier G A) : TwistedCarrier G A :=
  ⟨-x.coeff - f x.base x.base⁻¹, x.base⁻¹⟩

/-- PDF p. 4: the right principal coefficient action, in additive notation. -/
def coefficientAction {G A : Type u} [AddCommGroup A]
    (x : TwistedCarrier G A) (a : A) : TwistedCarrier G A :=
  ⟨x.coeff + a, x.base⟩

/-- PDF p. 4: translated local trivializations with base coordinate first,
 computed from the source section sigma_g(x)=(f(g,g^-1*x),x). -/
def twistedBundleChart {G A : Type u} [Group G] [AddCommGroup A]
    (f : G → G → A) (g : G) (x : TwistedCarrier G A) : G × A :=
  (x.base, x.coeff - f g (g⁻¹ * x.base))

/-- PDF p. 4: the inverse of the actual translated local trivialization. -/
def twistedBundleChartInverse {G A : Type u} [Group G] [AddCommGroup A]
    (f : G → G → A) (g : G) (p : G × A) : TwistedCarrier G A :=
  ⟨p.2 + f g (g⁻¹ * p.1), p.1⟩

/-- Sanity: zero twisting yields the direct-product multiplication and inverse,
 while the local trivialization retains both coordinates and the right action. -/
example {G A : Type u} [Group G] [AddCommGroup A]
    (x y : TwistedCarrier G A) (g : G) (a : A) :
    twistedCarrierMul (fun _ _ => (0 : A)) x y =
      ⟨x.coeff + y.coeff, x.base * y.base⟩ ∧
    twistedInv (fun _ _ => (0 : A)) x = ⟨-x.coeff, x.base⁻¹⟩ ∧
    twistedBundleChart (fun _ _ => (0 : A)) g x = (x.base, x.coeff) ∧
    twistedBundleChartInverse (fun _ _ => (0 : A)) g (x.base, x.coeff) = x ∧
    coefficientAction x a = ⟨x.coeff + a, x.base⟩ := by
  cases x
  simp [twistedCarrierMul, QAlgorithms.Papers.Independent.Renew46.P18.twistedMul, twistedInv, twistedBundleChart,
    twistedBundleChartInverse, coefficientAction]

section Statement

variable {E F G : Type u}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [ChartedSpace E G]
variable (Gamma : AddSubgroup F)
variable [ChartedSpace F (F ⧸ Gamma)]

end Statement

end QAlgorithms.Papers.Independent.Intakenext100.P10


