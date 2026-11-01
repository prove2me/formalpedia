-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P07
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:21:14.417633+00:00
-- url     : https://prove2.me/theorems/e1a7d151-fe3d-4958-806d-47d1e0540180
-- title:
--   Definitions for Cohomology of Local Cochains
-- statement:
--   The objects the formalized statements of *Cohomology of Local Cochains* (arXiv:1110.2661) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `UnitTime`: The closed real unit interval used in Definition 5.1, PDF p. 20.
--   - `timeZero`: The initial parameter of the unit interval.
--   - `timeOne`: The final parameter of the unit interval.
--   - `IsLoopContraction`: A homotopy through group endomorphisms, Definition 5.1, PDF p. 20. The parameter runs from the identity element to the identity map, as in Examples 5.2–5.4. Reversing this parameter gives a contraction to the identity.
--   - `LoopContractible`: Existence of the endomorphism homotopy of Definition 5.1, PDF p. 20.
--   - `IsAddLoopContraction`: Additive notation for Definition 5.1, with the same parameter convention.
--   - `scalarHomotopy`: The scalar homotopy in Example 5.2, PDF p. 20.
--   - `BasedPaths`: Based continuous paths, with the subspace topology of the compact-open mapping space, Example 5.3, PDF p. 20.
--   - `basedPathMul`: Pointwise path multiplication, also for noncommutative groups.
--   - `basedPathOne`: The constant based path.
--   - `scaledTime`: Multiplication of two parameters in the closed unit interval.
--   - `pathRescale`: The actual rescaling gamma(t) ↦ gamma(st), Example 5.3, PDF p. 20.
--   - `basedPathEndpoint`: Evaluation at the endpoint; its kernel is the based loop group.
--   - `BasedLoops`: The based loop subgroup as the endpoint kernel, Remark 5.4, PDF p. 20. It inherits the compact-open subspace topology from the based path space.
--   - `KSpace`: The underlying set with the final topology of compact Hausdorff probes, Definitions B.1–B.2, PDF p. 36. Probe and space universes are both u.
--   - `kProbe`: A probe, regarded as a continuous map into the final probe topology.
--   - `kToOriginal`: The canonical map kX→Y induced by a continuous map X→Y.
--   - `kMap`: The identity-on-points lift k(f), PDF p. 36.
--   - `kCoreflector`: The concrete coreflector: final probe topology on objects, same functions on morphisms. Definition B.4 and the following paragraph, PDF p. 36.
--   - `IsKAddLoopContraction`: Additive loop contraction in kTop. Continuity uses the kified product, not the ordinary product, as required in Section 6, PDF pp. 25–26.
--   - `kProductCone`: The candidate product in kTop: k applied to the ordinary product, with the actual ordinary-product projections, Proposition B.8, PDF p. 36.
--   - `IsKOmega`: Definition C.1, PDF p. 38: a countable covering family of images of compact Hausdorff spaces determines exactly the topology of X. The target need not be Hausdorff; finite and empty index types are permitted.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, https://arxiv.org/abs/1110.2661v2

import Mathlib

/-!
Statements from M. Fuchssteiner, Cohomology of Local Cochains,
arXiv:1110.2661v2. The cohomological comparisons deferred in HARD.md are
not represented by abstract predicates or by unrelated group isomorphisms.
All new definitions are local to this paper. Compilation is pending.
-/

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- The closed real unit interval used in Definition 5.1, PDF p. 20. -/
abbrev UnitTime := Set.Icc (0 : ℝ) 1

/-- The initial parameter of the unit interval. -/
def timeZero : UnitTime := ⟨0, by constructor <;> norm_num⟩

/-- The final parameter of the unit interval. -/
def timeOne : UnitTime := ⟨1, by constructor <;> norm_num⟩

/-- A homotopy through group endomorphisms, Definition 5.1, PDF p. 20.
The parameter runs from the identity element to the identity map, as in
Examples 5.2–5.4. Reversing this parameter gives a contraction to the identity. -/
def IsLoopContraction {G : Type u} [TopologicalSpace G] [Group G]
    (phi : G × UnitTime → G) : Prop :=
  Continuous phi ∧
  (∀ g, phi (g, timeZero) = 1) ∧
  (∀ g, phi (g, timeOne) = g) ∧
  ∀ t g h, phi (g * h, t) = phi (g, t) * phi (h, t)

/-- Existence of the endomorphism homotopy of Definition 5.1, PDF p. 20. -/
def LoopContractible (G : Type u) [TopologicalSpace G] [Group G] : Prop :=
  ∃ phi : G × UnitTime → G, IsLoopContraction phi

/-- Additive notation for Definition 5.1, with the same parameter convention. -/
def IsAddLoopContraction {V : Type u} [TopologicalSpace V] [AddGroup V]
    (phi : V × UnitTime → V) : Prop :=
  Continuous phi ∧
  (∀ x, phi (x, timeZero) = 0) ∧
  (∀ x, phi (x, timeOne) = x) ∧
  ∀ t x y, phi (x + y, t) = phi (x, t) + phi (y, t)

/-- The scalar homotopy in Example 5.2, PDF p. 20. -/
def scalarHomotopy {V : Type u} [SMul ℝ V] (p : V × UnitTime) : V :=
  (p.2 : ℝ) • p.1

example : scalarHomotopy ((3 : ℝ), timeZero) = 0 := by
  simp [scalarHomotopy, timeZero]

example : scalarHomotopy ((3 : ℝ), timeOne) = 3 := by
  simp [scalarHomotopy, timeOne]

/-- Based continuous paths, with the subspace topology of the compact-open
mapping space, Example 5.3, PDF p. 20. -/
def BasedPaths (G : Type u) [TopologicalSpace G] [Group G] :=
  {gamma : C(UnitTime, G) // gamma timeZero = 1}

instance basedPathsTopology (G : Type u) [TopologicalSpace G] [Group G] :
    TopologicalSpace (BasedPaths G) :=
  inferInstanceAs (TopologicalSpace {gamma : C(UnitTime, G) // gamma timeZero = 1})

/-- Pointwise path multiplication, also for noncommutative groups. -/
def basedPathMul {G : Type u} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (gamma eta : BasedPaths G) : BasedPaths G :=
  ⟨gamma.val * eta.val, by
    change gamma.val timeZero * eta.val timeZero = 1
    rw [gamma.property, eta.property, one_mul]⟩

/-- The constant based path. -/
def basedPathOne {G : Type u} [TopologicalSpace G] [Group G] : BasedPaths G :=
  ⟨ContinuousMap.const UnitTime 1, rfl⟩

/-- Multiplication of two parameters in the closed unit interval. -/
def scaledTime (s t : UnitTime) : UnitTime :=
  ⟨(s : ℝ) * (t : ℝ), mul_nonneg s.property.1 t.property.1,
    (mul_le_mul_of_nonneg_right s.property.2 t.property.1).trans
      (by simpa using t.property.2)⟩

/-- The actual rescaling gamma(t) ↦ gamma(st), Example 5.3, PDF p. 20. -/
def pathRescale {G : Type u} [TopologicalSpace G] [Group G]
    (gamma : BasedPaths G) (s : UnitTime) : BasedPaths G :=
  ⟨⟨fun t => gamma.val (scaledTime s t),
      gamma.val.continuous.comp
        ((continuous_const.mul continuous_subtype_val).subtype_mk
          (fun t => (scaledTime s t).property))⟩, by
    change gamma.val (scaledTime s timeZero) = 1
    have h : scaledTime s timeZero = timeZero := by
      apply Subtype.ext
      simp [scaledTime, timeZero]
    rw [h]
    exact gamma.property⟩

example {G : Type u} [TopologicalSpace G] [Group G]
    (s : UnitTime) : pathRescale (basedPathOne (G := G)) s = basedPathOne := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rfl

/-- Evaluation at the endpoint; its kernel is the based loop group. -/
def basedPathEndpoint {G : Type u} [TopologicalSpace G] [Group G]
    (gamma : BasedPaths G) : G := gamma.val timeOne

/-- The based loop subgroup as the endpoint kernel, Remark 5.4, PDF p. 20.
It inherits the compact-open subspace topology from the based path space. -/
def BasedLoops (G : Type u) [TopologicalSpace G] [Group G] :=
  {gamma : BasedPaths G // basedPathEndpoint gamma = 1}

instance basedLoopsTopology (G : Type u) [TopologicalSpace G] [Group G] :
    TopologicalSpace (BasedLoops G) :=
  inferInstanceAs (TopologicalSpace {gamma : BasedPaths G // basedPathEndpoint gamma = 1})

/-- The underlying set with the final topology of compact Hausdorff probes,
Definitions B.1–B.2, PDF p. 36. Probe and space universes are both u. -/
def KSpace (X : Type u) := X

instance kSpaceTopology (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (KSpace X) := TopologicalSpace.compactlyGenerated.{u} X

/-- A probe, regarded as a continuous map into the final probe topology. -/
def kProbe {X : Type u} [TopologicalSpace X] (S : CompHaus.{u})
    (f : C(S, X)) : C(S, KSpace X) := by
  let e : (Σ i : (T : CompHaus.{u}) × C(T, X), i.fst) → X :=
    fun ⟨⟨_, g⟩, x⟩ => g x
  have h : ∀ i : (T : CompHaus.{u}) × C(T, X),
      Continuous[inferInstance, TopologicalSpace.compactlyGenerated.{u} X]
        (fun a : i.fst => e ⟨i, a⟩) := by
    rw [← @continuous_sigma_iff]
    apply continuous_coinduced_rng
  exact ⟨f, h ⟨S, f⟩⟩

instance kSpaceGenerated (X : Type u) [TopologicalSpace X] :
    UCompactlyGeneratedSpace.{u} (KSpace X) := by
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y tY f hf
  change Continuous[TopologicalSpace.compactlyGenerated.{u} X, tY] f
  apply continuous_from_compactlyGenerated (X := X)
  intro S g
  exact hf S (kProbe S g)

/-- The canonical map kX→Y induced by a continuous map X→Y. -/
def kToOriginal {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : C(KSpace X, Y) :=
  ⟨f, continuous_from_compactlyGenerated f (fun _ g => f.continuous.comp g.continuous)⟩

/-- The identity-on-points lift k(f), PDF p. 36. -/
def kMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : C(KSpace X, KSpace Y) :=
  ⟨f, continuous_from_compactlyGenerated (X := X) (Y := KSpace Y)
    (fun x => f x) (fun S g => (kProbe S (f.comp g)).continuous)⟩

/-- The concrete coreflector: final probe topology on objects, same functions
on morphisms. Definition B.4 and the following paragraph, PDF p. 36. -/
def kCoreflector : TopCat.{u} ⥤ CompactlyGenerated.{u, u} where
  obj X := CompactlyGenerated.of (KSpace X)
  map f := CompactlyGenerated.ofHom (kMap f.hom)
  map_id X := by ext x; rfl
  map_comp f g := by ext x; rfl

example : (kMap (ContinuousMap.id PUnit)) PUnit.unit = PUnit.unit := rfl

/-- Additive loop contraction in kTop. Continuity uses the kified product,
not the ordinary product, as required in Section 6, PDF pp. 25–26. -/
def IsKAddLoopContraction {V : Type u} [TopologicalSpace V] [AddGroup V]
    (phi : V × UnitTime → V) : Prop :=
  Continuous (fun p : KSpace (V × UnitTime) => phi p) ∧
  (∀ x, phi (x, timeZero) = 0) ∧
  (∀ x, phi (x, timeOne) = x) ∧
  ∀ t x y, phi (x + y, t) = phi (x, t) + phi (y, t)

/-- The candidate product in kTop: k applied to the ordinary product,
with the actual ordinary-product projections, Proposition B.8, PDF p. 36. -/
def kProductCone {I : Type u} (Y : I → CompactlyGenerated.{u, u}) : Limits.Fan Y :=
  Limits.Fan.mk (CompactlyGenerated.of (KSpace (∀ i, Y i)))
    (fun i => CompactlyGenerated.ofHom
      (kToOriginal (⟨fun x => x i, continuous_apply i⟩ : C((∀ j, Y j), Y i))))

/-- Definition C.1, PDF p. 38: a countable covering family of images of
compact Hausdorff spaces determines exactly the topology of X. The target
need not be Hausdorff; finite and empty index types are permitted. -/
def IsKOmega (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (I : Type u) (_ : Countable I) (K : I → CompHaus.{u})
    (f : ∀ i, C(K i, X)),
    (∀ x : X, ∃ (i : I) (y : K i), f i y = x) ∧
    ∀ A : Set X, IsOpen A ↔ ∀ i, IsOpen ((f i) ⁻¹' A)

example : IsKOmega PUnit := by
  refine ⟨PUnit, inferInstance, fun _ => CompHaus.of PUnit,
    fun _ => ContinuousMap.id PUnit, ?_, ?_⟩
  · intro x
    exact ⟨PUnit.unit, x, rfl⟩
  · intro A
    constructor
    · intro h i
      exact h
    · intro h
      exact h PUnit.unit

end QAlgorithms.Papers.Independent.Intakethird100.P07


