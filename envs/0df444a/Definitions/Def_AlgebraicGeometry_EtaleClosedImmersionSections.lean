-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleClosedImmersionSections
-- name    : AlgebraicGeometry_EtaleClosedImmersionSections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T21:15:52.258915+00:00
-- url     : https://prove2.me/theorems/a09de9ea-ca98-497f-9b4c-ba0b6ff31e7a
-- title:
--   Sections and direct image over a closed immersion
-- statement:
--   Étale lifting through thickenings, full faithfulness for closed direct images, and restriction of global sections.

import Definitions.Def_AlgebraicGeometry_EtaleModeledCech
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Spectral.ConstructibleTopology
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_zariski_refinement_of_surjective_etale

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject


namespace PhilipponEtaleGeometricStalks

universe u

/-- An algebraically closed geometric point over the given scheme point. -/
def algebraicallyClosedGeometricMap {X : Scheme.{u}} (x : X) :
    Spec (CommRingCat.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
  (Scheme.SpecToEquivOfField (AlgebraicClosure (X.residueField x)) X).2
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩

@[simp] theorem algebraicallyClosedGeometricMap_apply {X : Scheme.{u}} (x : X) :
    algebraicallyClosedGeometricMap x default = x := by
  simp [algebraicallyClosedGeometricMap, Scheme.SpecToEquivOfField]

/-- Stalks at the algebraic closures of the residue fields detect
isomorphisms of étale sheaves. -/
theorem algebraicallyClosedGeometricPoints_conservative (X : Scheme.{u}) :
    (ObjectProperty.ofObj (fun x : X => Scheme.pointSmallEtale
      (algebraicallyClosedGeometricMap x))).IsConservativeFamilyOfPoints := by
  apply Scheme.isConservative_pointSmallEtale
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact ⟨x, default, algebraicallyClosedGeometricMap_apply x⟩

end PhilipponEtaleGeometricStalks

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleGeometricStalks (geometricMap geometricMap_apply geometricPoint)


namespace PhilipponEtaleClosedFiberCovers

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}

/-- Each point closure in a proper scheme over a local ring meets the
closed fiber. -/
theorem closedFiber_inter_closure_nonempty (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (y : Y) :
    (f ⁻¹' {IsLocalRing.closedPoint R} ∩ closure ({y} : Set Y)).Nonempty := by
  have hc : IsClosed (f '' closure ({y} : Set Y)) := f.isClosedMap _ isClosed_closure
  have hy : f y ∈ f '' closure ({y} : Set Y) := ⟨y, subset_closure rfl, rfl⟩
  obtain ⟨z, hz, he⟩ := (IsLocalRing.specializes_closedPoint (f y)).mem_closed hc hy
  exact ⟨z, Set.mem_singleton_iff.mpr he, hz⟩

/-- An open subset of a scheme proper over a local ring contains the whole
scheme if it contains the fiber over the closed point. -/
theorem eq_univ_of_contains_closedFiber (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {U : Set Y} (hU : IsOpen U)
    (h : f ⁻¹' {IsLocalRing.closedPoint R} ⊆ U) : U = Set.univ := by
  have hClosed : IsClosed (f '' Uᶜ) := f.isClosedMap _ hU.isClosed_compl
  have hc : IsLocalRing.closedPoint R ∈ (f '' Uᶜ)ᶜ := by
    rintro ⟨y, hy, hyc⟩
    exact hy (h (Set.mem_singleton_iff.mpr hyc))
  apply Set.eq_univ_of_forall
  intro y
  by_contra hy
  have hy' : f y ∈ (f '' Uᶜ)ᶜ :=
    (IsLocalRing.specializes_closedPoint (f y)).mem_open hClosed.isOpen_compl hc
  exact hy' ⟨y, hy, rfl⟩

/-- A family of étale maps to a scheme proper over a local ring is a cover
as soon as its image contains the fiber over the closed point. -/
theorem covering_of_contains_closedFiber (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {ι : Type u} (V : ι → Y.Etale)
    (g : ∀ a, V a ⟶ Scheme.Etale.mk (𝟙 Y))
    (h : f ⁻¹' {IsLocalRing.closedPoint R} ⊆ ⋃ a, Set.range (g a).left) :
    Sieve.ofArrows V g ∈ Y.smallEtaleTopology (Scheme.Etale.mk (𝟙 Y)) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
  exact eq_univ_of_contains_closedFiber f
    (isOpen_iUnion fun a => (g a).left.isOpenMap.isOpen_range) h

private abbrev terminalChart (Y : Scheme.{u}) := Scheme.Etale.mk (𝟙 Y)

private def terminalPoint (y : Y) : (geometricPoint y).fiber.obj (terminalChart Y) :=
  Over.homMk (geometricMap y) (Category.comp_id _)

/-- Global sections of an étale sheaf on a proper scheme over a local ring
are determined by their germs along the closed fiber. -/
theorem globalSections_eq_of_germs_eq_along_closedFiber
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (a b : ↥(F.obj.obj (op (terminalChart Y))))
    (h : ∀ y : Y, f y = IsLocalRing.closedPoint R →
      (geometricPoint y).toPresheafFiber (terminalChart Y) (terminalPoint y) F.obj a =
        (geometricPoint y).toPresheafFiber (terminalChart Y) (terminalPoint y) F.obj b) :
    a = b := by
  classical
  let T := terminalChart Y
  let S := Presheaf.equalizerSieve (F := F.obj) (X := op T) a b
  have hRefine (y : Y) (hy : f y = IsLocalRing.closedPoint R) :
      ∃ (V : Y.Etale) (g : V ⟶ T), S g ∧ y ∈ Set.range g.left := by
    obtain ⟨V, g, t, ht, he⟩ :=
      ((geometricPoint y).toPresheafFiber_eq_iff' T (terminalPoint y) a b).mp (h y hy)
    have hcomp : t.left ≫ g.left = geometricMap y :=
      congrArg Over.Hom.left ht
    let z : Spec (CommRingCat.of (SeparableClosure (Y.residueField y))) := default
    refine ⟨V, g, he, t.left z, ?_⟩
    let k : V.left ⟶ Y := g.left
    change k (t.left z) = y
    calc
      k (t.left z) = (t.left ≫ k) z := (Scheme.Hom.comp_apply _ _ _).symm
      _ = geometricMap y z := congrArg (fun m : _ ⟶ Y => m z) hcomp
      _ = y := geometricMap_apply y
  let Q := {y : Y // f y = IsLocalRing.closedPoint R}
  choose V g hg hy using fun y : Q => hRefine y.val y.property
  have hCover := covering_of_contains_closedFiber f V g (fun y hy' =>
    Set.mem_iUnion.mpr ⟨⟨y, hy'⟩, hy ⟨y, hy'⟩⟩)
  have hS : S ∈ Y.smallEtaleTopology T :=
    Y.smallEtaleTopology.superset_covering
      ((Sieve.generate_le_iff _ _).mpr (by
        rintro _ _ ⟨j⟩
        exact hg j)) hCover
  have hSheaf := Presheaf.isSheaf_comp_of_isSheaf Y.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp hSheaf _ hS).isSeparatedFor.ext
    (fun _ _ hab => hab)

end PhilipponEtaleClosedFiberCovers

end

section

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Polynomial
open scoped TensorProduct


namespace PhilipponEtaleThickeningLifts

universe u

/- The local algebra and scheme lifting arguments are adapted from the
Prove2Me Fermat's Last Theorem development. The chartwise nilpotence argument
uses local Noetherianity and surjectivity of the closed immersion. -/
private theorem eq_of_comp_eq_of_surjective {X Y T T₀ : Scheme.{u}} (q : Y ⟶ X)
    [FormallyUnramified q] [LocallyOfFiniteType q]
    (k : T₀ ⟶ T) [Surjective k] {s₁ s₂ : T ⟶ Y}
    (hq : s₁ ≫ q = s₂ ≫ q) (hk : k ≫ s₁ = k ≫ s₂) : s₁ = s₂ := by

  haveI : IsOpenImmersion (pullback.diagonal q) := inferInstance
  haveI : IsOpenImmersion (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) := inferInstance

  have hfac : k ≫ pullback.lift s₁ s₂ hq = (k ≫ s₁) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hk]
  have hk' : pullback.lift k (k ≫ s₁) hfac ≫ pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q) = k :=
    pullback.lift_fst _ _ _
  haveI : Surjective (pullback.lift k (k ≫ s₁) hfac ≫
      pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) := by rw [hk']; infer_instance
  haveI : Surjective (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) :=
    Surjective.of_comp (pullback.lift k (k ≫ s₁) hfac) _
  haveI : IsIso (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

  have hp : pullback.lift s₁ s₂ hq =
      inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
        pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) ≫ pullback.diagonal q := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  have h1 : s₁ = inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
      pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) := by
    calc s₁ = pullback.lift s₁ s₂ hq ≫ pullback.fst q q := (pullback.lift_fst _ _ _).symm
      _ = (inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
            pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) ≫ pullback.diagonal q) ≫
              pullback.fst q q := by rw [← hp]
      _ = _ := by simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have h2 : s₂ = inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
      pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) := by
    calc s₂ = pullback.lift s₁ s₂ hq ≫ pullback.snd q q := (pullback.lift_snd _ _ _).symm
      _ = (inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
            pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) ≫ pullback.diagonal q) ≫
              pullback.snd q q := by rw [← hp]
      _ = _ := by simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
  rw [h1, ← h2]

private theorem affine_kernel_nilpotent {T T₀ : Scheme.{u}} [IsLocallyNoetherian T]
    (k : T₀ ⟶ T) [IsClosedImmersion k] [Surjective k] (U : T.affineOpens) :
    IsNilpotent (RingHom.ker (k.app U.val).hom) := by
  have hsupport : k.ker.support = ⊤ := by
    ext1
    rw [Scheme.Hom.support_ker, k.surjective.range_eq]
    simp
  have hle := Scheme.IdealSheafData.le_radical k.ker
  rw [← Scheme.IdealSheafData.vanishingIdeal_support, hsupport,
    Scheme.IdealSheafData.vanishingIdeal_top] at hle
  have hU := hle U
  rw [Scheme.Hom.ker_apply] at hU
  haveI := IsLocallyNoetherian.component_noetherian U
  exact (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr hU

private theorem exists_of_forall_exists_nhd {X Y T T₀ : Scheme.{u}} (q : Y ⟶ X)
    [FormallyUnramified q] [LocallyOfFiniteType q]
    (k : T₀ ⟶ T) [Surjective k] (t : T ⟶ X) (s₀ : T₀ ⟶ Y)
    (H : ∀ p : T, ∃ (U : T.Opens) (_ : p ∈ U) (sU : (U : Scheme.{u}) ⟶ Y),
      sU ≫ q = U.ι ≫ t ∧ (k ∣_ U) ≫ sU = (k ⁻¹ᵁ U).ι ≫ s₀) :
    ∃ s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ := by
  choose U hpU sU hsUq hsUk using H
  let 𝒰 : T.OpenCover :=
    { I₀ := T, X := fun i => (U i), f := fun i => (U i).ι,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ⟨x, by simpa using hpU x⟩, inferInstance⟩ }

  have hcompat : ∀ i j : T, pullback.fst (𝒰.f i) (𝒰.f j) ≫ sU i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ sU j := by
    intro i j
    let g : pullback (𝒰.f i) (𝒰.f j) ⟶ T := pullback.fst (𝒰.f i) (𝒰.f j) ≫ (U i).ι
    have hg : pullback.snd (𝒰.f i) (𝒰.f j) ≫ (U j).ι = g := (pullback.condition).symm

    have key : ∀ (l : T) (m : pullback (𝒰.f i) (𝒰.f j) ⟶ (U l : Scheme.{u})) (hm : m ≫ (U l).ι = g),
        pullback.snd k g ≫ m ≫ sU l = pullback.fst k g ≫ s₀ := by
      intro l m hm
      have w : (pullback.snd k g ≫ m) ≫ (U l).ι = pullback.fst k g ≫ k := by
        rw [Category.assoc, hm, pullback.condition]
      let n := (isPullback_morphismRestrict k (U l)).lift (pullback.snd k g ≫ m) (pullback.fst k g) w
      have hn1 : n ≫ (k ∣_ U l) = pullback.snd k g ≫ m := IsPullback.lift_fst _ _ _ _
      have hn2 : n ≫ (k ⁻¹ᵁ U l).ι = pullback.fst k g := IsPullback.lift_snd _ _ _ _
      rw [← Category.assoc, ← hn1, Category.assoc, hsUk, ← Category.assoc, hn2]
    haveI : Surjective (pullback.snd k g) := inferInstance
    refine eq_of_comp_eq_of_surjective q (pullback.snd k g) ?_ ?_
    · rw [Category.assoc, hsUq, Category.assoc, hsUq, ← Category.assoc, ← Category.assoc, pullback.condition]
    · rw [key i (pullback.fst (𝒰.f i) (𝒰.f j)) rfl, key j (pullback.snd (𝒰.f i) (𝒰.f j)) hg]
  refine ⟨𝒰.glueMorphisms sU hcompat, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun i ↦ ?_
    rw [Scheme.Cover.ι_glueMorphisms_assoc, hsUq]
  ·
    let 𝒱 : T₀.OpenCover :=
      { I₀ := T, X := fun i => (k ⁻¹ᵁ U i), f := fun i => (k ⁻¹ᵁ U i).ι,
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          refine ⟨fun x ↦ ⟨k.base x, by simpa using hpU (k.base x)⟩, inferInstance⟩ }
    refine Scheme.Cover.hom_ext 𝒱 _ _ fun i ↦ ?_
    show (k ⁻¹ᵁ U i).ι ≫ k ≫ 𝒰.glueMorphisms sU hcompat = (k ⁻¹ᵁ U i).ι ≫ s₀
    rw [← morphismRestrict_ι_assoc, show (U i).ι = 𝒰.f i from rfl, Scheme.Cover.ι_glueMorphisms, hsUk]

private theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

private theorem exists_nhd_lift {X Y T T₀ : Scheme.{u}} (q : Y ⟶ X) [Etale q]
    (k : T₀ ⟶ T) [IsClosedImmersion k] [Surjective k] [IsLocallyNoetherian T]
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) (p : T) :
    ∃ (U : T.Opens) (_ : p ∈ U) (sU : (U : Scheme.{u}) ⟶ Y),
      sU ≫ q = U.ι ≫ t ∧ (k ∣_ U) ≫ sU = (k ⁻¹ᵁ U).ι ≫ s₀ := by
  obtain ⟨p₀, hp₀⟩ := k.surjective p

  obtain ⟨_, ⟨R', hR', rfl⟩, hpR', -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t.base p)) isOpen_univ

  have hqs : q.base (s₀.base p₀) = t.base p := by
    have := congrArg (fun f : T₀ ⟶ X => f.base p₀) hs₀
    simpa [hp₀] using this
  have hy : s₀.base p₀ ∈ q ⁻¹ᵁ R' := by
    show q.base (s₀.base p₀) ∈ R'
    rw [hqs]; exact hpR'
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWR'⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy (q ⁻¹ᵁ R').isOpen
  change W ≤ q ⁻¹ᵁ R' at hWR'

  let O : T.Opens := ⟨(k.base '' ((s₀ ⁻¹ᵁ W : T₀.Opens) : Set T₀)ᶜ)ᶜ, by
    rw [isOpen_compl_iff]
    exact k.isClosedEmbedding.isClosedMap _ (isClosed_compl_iff.mpr (s₀ ⁻¹ᵁ W).isOpen)⟩
  have hpO : p ∈ O := by
    rintro ⟨x, hx, hxp⟩
    apply hx
    have : x = p₀ := k.isClosedEmbedding.injective (hxp.trans hp₀.symm)
    subst this
    exact hyW

  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, hUle⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (show p ∈ ((t ⁻¹ᵁ R' ⊓ O : T.Opens) : Set T) from ⟨hpR', hpO⟩) (t ⁻¹ᵁ R' ⊓ O).isOpen
  have hUR' : U ≤ t ⁻¹ᵁ R' := fun x hx => (hUle hx).1
  have hkUW : k ⁻¹ᵁ U ≤ s₀ ⁻¹ᵁ W := by
    intro x hx
    by_contra hxW
    exact (hUle hx).2 ⟨x, hxW, rfl⟩
  have hkU : IsAffineOpen (k ⁻¹ᵁ U) := hU.preimage k
  have hkUR' : k ⁻¹ᵁ U ≤ (k ≫ t) ⁻¹ᵁ R' := fun x hx => hUR' hx

  have hφ : (q.appLE R' W hWR').hom.Etale :=
    HasRingHomProperty.appLE (P := @Etale) q inferInstance ⟨R', hR'⟩ ⟨W, hW⟩ hWR'
  algebraize [(q.appLE R' W hWR').hom, (t.appLE R' U hUR').hom, ((k ≫ t).appLE R' (k ⁻¹ᵁ U) hkUR').hom]
  let σ : Γ(Y, W) →ₐ[Γ(X, R')] Γ(T₀, k ⁻¹ᵁ U) := ⟨(s₀.appLE W (k ⁻¹ᵁ U) hkUW).hom, fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    rw [appLE_congr_hom hs₀]⟩
  let κ : Γ(T, U) →ₐ[Γ(X, R')] Γ(T₀, k ⁻¹ᵁ U) := ⟨(k.appLE U (k ⁻¹ᵁ U) le_rfl).hom, fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]⟩
  have hκs : Function.Surjective κ := by
    show Function.Surjective (k.appLE U (k ⁻¹ᵁ U) le_rfl).hom
    rw [← Scheme.Hom.app_eq_appLE]
    exact k.app_surjective U hU
  have hκn : IsNilpotent (RingHom.ker (κ : Γ(T, U) →+* Γ(T₀, k ⁻¹ᵁ U))) := by
    show IsNilpotent (RingHom.ker (k.appLE U (k ⁻¹ᵁ U) le_rfl).hom)
    rw [← Scheme.Hom.app_eq_appLE]
    exact affine_kernel_nilpotent k ⟨U, hU⟩
  let ψ : Γ(Y, W) →ₐ[Γ(X, R')] Γ(T, U) := Algebra.FormallySmooth.liftOfSurjective σ κ hκs hκn
  have hψ : κ.comp ψ = σ := Algebra.FormallySmooth.comp_liftOfSurjective σ κ hκs hκn

  refine ⟨U, hpU, hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hW.fromSpec, ?_, ?_⟩
  ·
    have h1 : q.appLE R' W hWR' ≫ CommRingCat.ofHom ψ.toRingHom = t.appLE R' U hUR' := by
      ext r
      change ψ (algebraMap Γ(X, R') Γ(Y, W) r) = algebraMap Γ(X, R') Γ(T, U) r
      exact ψ.commutes r
    rw [Category.assoc, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q hR' hW hWR',
      ← Spec.map_comp_assoc, h1, IsAffineOpen.SpecMap_appLE_fromSpec t hR' hU hUR',
      ← hU.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  ·
    have h2 : CommRingCat.ofHom ψ.toRingHom ≫ k.appLE U (k ⁻¹ᵁ U) le_rfl = s₀.appLE W (k ⁻¹ᵁ U) hkUW := by
      ext a
      change κ (ψ a) = σ a
      rw [← hψ]; rfl
    have h3 : Spec.map (k.appLE U (k ⁻¹ᵁ U) le_rfl) ≫ hU.isoSpec.inv = hkU.isoSpec.inv ≫ (k ∣_ U) := by
      rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, Category.assoc, hU.isoSpec_inv_ι, morphismRestrict_ι,
        IsAffineOpen.SpecMap_appLE_fromSpec k hU hkU le_rfl, ← hkU.isoSpec_inv_ι, Category.assoc]
    rw [← cancel_epi hkU.isoSpec.inv, ← Category.assoc, ← h3, Category.assoc, Iso.inv_hom_id_assoc,
      ← Spec.map_comp_assoc, h2, IsAffineOpen.SpecMap_appLE_fromSpec s₀ hW hkU hkUW, ← Category.assoc, hkU.isoSpec_inv_ι]

theorem existsUnique_lift {X Y T T₀ : Scheme.{u}} (q : Y ⟶ X) [Etale q]
    (k : T₀ ⟶ T) [IsClosedImmersion k] [Surjective k] [IsLocallyNoetherian T]
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) :
    ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ := by
  obtain ⟨s, hs, hks⟩ := exists_of_forall_exists_nhd q k t s₀ (exists_nhd_lift q k t s₀ hs₀)
  refine ⟨s, ⟨hs, hks⟩, fun s' hs' => ?_⟩
  exact eq_of_comp_eq_of_surjective q k (hs'.1.trans hs.symm) (hs'.2.trans hks.symm)

private theorem lift_standardEtale
    {C C₀ : Type u} [CommRing C] [CommRing C₀] [Algebra C C₀] (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type u) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧ Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) := by
  classical
  obtain ⟨P₀⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := C₀) (S := S₀)
  rcases subsingleton_or_nontrivial C₀ with hC₀ | hC₀
  ·
    haveI : Subsingleton S₀ := Module.subsingleton C₀ S₀
    refine ⟨C, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
    exact AlgEquiv.ofBijective ((Algebra.ofId C₀ S₀).comp (Algebra.TensorProduct.rid C C₀ C₀).toAlgHom)
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

  set φ : C →+* C₀ := algebraMap C C₀ with hφ
  obtain ⟨f, hf, -, hfm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (f := φ) ((mem_lifts _).mpr (map_surjective φ hC P₀.f)) P₀.monic_f
  obtain ⟨p₁, p₂, n, hP⟩ := P₀.cond
  obtain ⟨g, hg⟩ := map_surjective φ hC P₀.g
  obtain ⟨q₁, hq₁⟩ := map_surjective φ hC p₁
  obtain ⟨q₂, hq₂⟩ := map_surjective φ hC p₂
  let P : StandardEtalePair C :=
    { f := f, monic_f := hfm, g := g * (derivative f * q₁ + f * q₂), cond := ⟨g * q₁, g * q₂, 1, by ring⟩ }
  have hPf : P.f.map φ = P₀.f := hf
  have hPg : P.g.map φ = P₀.g ^ (n + 1) := by
    show (g * (derivative f * q₁ + f * q₂)).map φ = P₀.g ^ (n + 1)
    simp only [Polynomial.map_mul, Polynomial.map_add, ← Polynomial.derivative_map, hf, hg, hq₁, hq₂, hP]
    ring

  letI : Algebra C S₀ := ((algebraMap C₀ S₀).comp φ).toAlgebra
  haveI : IsScalarTower C C₀ S₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have key : ∀ (T : Type u) [CommRing T] [Algebra C₀ T] [Algebra C T] [IsScalarTower C C₀ T] (t : T),
      P.HasMap t ↔ P₀.HasMap t := by
    intro T _ _ _ _ t
    simp only [StandardEtalePair.HasMap]
    rw [← aeval_map_algebraMap C₀ t P.f, ← aeval_map_algebraMap C₀ t P.g, ← hφ, hPf, hPg, map_pow,
      isUnit_pow_iff (Nat.succ_ne_zero n)]
  have h1 : P.HasMap P₀.x := (key S₀ P₀.x).mpr P₀.hasMap
  have h2' : P.HasMap ((1 : C₀) ⊗ₜ[C] P.X) :=
    (StandardEtalePair.hasMap_X (P := P)).map
      (Algebra.TensorProduct.includeRight (R := C) (A := C₀) (B := P.Ring))
  have h2 : P₀.HasMap ((1 : C₀) ⊗ₜ[C] P.X) := (key (C₀ ⊗[C] P.Ring) _).mp h2'
  let F : C₀ ⊗[C] P.Ring →ₐ[C₀] S₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId C₀ S₀) (P.lift P₀.x h1) (fun _ _ => .all _ _)
  let G : S₀ →ₐ[C₀] C₀ ⊗[C] P.Ring := (P₀.lift ((1 : C₀) ⊗ₜ[C] P.X) h2).comp P₀.equivRing.toAlgHom
  have hF : F ((1 : C₀) ⊗ₜ[C] P.X) = P₀.x := by
    simp [F, Algebra.TensorProduct.lift_tmul, StandardEtalePair.lift_X]
  have hG : G P₀.x = (1 : C₀) ⊗ₜ[C] P.X := by
    simp [G, StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X]
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, ⟨AlgEquiv.ofAlgHom F G ?_ ?_⟩⟩
  · apply P₀.hom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hG, hF]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply StandardEtalePair.hom_ext
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
        AlgHom.id_apply, hF, hG]

theorem exists_local_model
    {X X₀ Y₀ : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] (q₀ : Y₀ ⟶ X₀) [Etale q₀] (y : Y₀) :
    ∃ (V₀ : Y₀.Opens) (_ : y ∈ V₀) (V : Scheme.{u}) (qV : V ⟶ X) (_ : Etale qV) (jV : (V₀ : Scheme.{u}) ⟶ V),
      IsPullback jV (V₀.ι ≫ q₀) qV i := by
  classical

  obtain ⟨U, hUa, hxU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show i (q₀ y) ∈ (⊤ : X.Opens) from trivial)
  replace hUa : IsAffineOpen U := hUa

  have hU₀a : IsAffineOpen (i ⁻¹ᵁ U) := hUa.preimage i

  obtain ⟨W, hWa, hyW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp Y₀.isBasis_affineOpens)
    (show y ∈ q₀ ⁻¹ᵁ (i ⁻¹ᵁ U) from hxU)
  replace hWa : IsAffineOpen W := hWa

  letI algA : Algebra Γ(X, U) Γ(X₀, i ⁻¹ᵁ U) := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI algB : Algebra Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, W) := (q₀.appLE (i ⁻¹ᵁ U) W hWle).hom.toAlgebra
  have ha : Function.Surjective (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U)) := by
    show Function.Surjective (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom
    rw [← Scheme.Hom.app_eq_appLE]
    exact i.app_surjective U hUa
  have hEt : Algebra.Etale Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, W) := Etale.etale_appLE q₀ hU₀a hWa hWle
  haveI := hEt.formallyEtale
  haveI := hEt.finitePresentation

  set p : PrimeSpectrum Γ(Y₀, W) := hWa.primeIdealOf ⟨y, hyW⟩ with hp
  obtain ⟨g, hgp, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := Γ(X₀, i ⁻¹ᵁ U)) p.asIdeal
  have hV₀a : IsAffineOpen (Y₀.basicOpen g) := hWa.basicOpen g
  have hV₀le : Y₀.basicOpen g ≤ q₀ ⁻¹ᵁ (i ⁻¹ᵁ U) := (Y₀.basicOpen_le g).trans hWle
  have hyV₀ : y ∈ Y₀.basicOpen g := by
    have h1 : hWa.fromSpec p = y := hWa.fromSpec_primeIdealOf ⟨y, hyW⟩
    rw [← h1]
    show p ∈ hWa.fromSpec ⁻¹ᵁ Y₀.basicOpen g
    rw [hWa.fromSpec_preimage_basicOpen]
    exact hgp
  letI algS₀ : Algebra Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g) :=
    (q₀.appLE (i ⁻¹ᵁ U) (Y₀.basicOpen g) hV₀le).hom.toAlgebra
  haveI : IsScalarTower Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, W) Γ(Y₀, Y₀.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      show (q₀.appLE (i ⁻¹ᵁ U) (Y₀.basicOpen g) hV₀le).hom r =
        (Y₀.presheaf.map (homOfLE (Y₀.basicOpen_le g)).op).hom ((q₀.appLE (i ⁻¹ᵁ U) W hWle).hom r)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map])
  haveI : IsLocalization.Away g Γ(Y₀, Y₀.basicOpen g) := hWa.isLocalization_basicOpen g
  haveI : Algebra.IsStandardEtale Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g) :=
    Algebra.IsStandardEtale.of_equiv
      ((IsLocalization.algEquiv (.powers g) (Localization.Away g) Γ(Y₀, Y₀.basicOpen g)).restrictScalars
        Γ(X₀, i ⁻¹ᵁ U))

  obtain ⟨S, _, _, hS, ⟨e⟩⟩ :=
    lift_standardEtale ha
      Γ(Y₀, Y₀.basicOpen g)
  have hSe : (algebraMap Γ(X, U) S).Etale := RingHom.etale_algebraMap.mpr inferInstance
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S))) := HasRingHomProperty.Spec_iff.mpr hSe
  let ψ : S →+* Γ(Y₀, Y₀.basicOpen g) :=
    e.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeRight (R := Γ(X, U)) (A := Γ(X₀, i ⁻¹ᵁ U)) (B := S))
  refine ⟨Y₀.basicOpen g, hyV₀, Spec (.of S),
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)) ≫ hUa.fromSpec, inferInstance,
    hV₀a.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩

  have top : IsPullback (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U)))) := by
    have H := (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)))).flip
    refine H.of_iso
      (pullbackSpecIso Γ(X, U) Γ(X₀, i ⁻¹ᵁ U) S ≪≫ Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
        Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← Spec.map_comp, ← pullbackSpecIso_hom_snd]
      congr 2
      ext x
      symm
      change e.symm (e (Algebra.TensorProduct.includeRight x)) = Algebra.TensorProduct.includeRight x
      exact e.symm_apply_apply _
    · simp only [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
        Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← Spec.map_comp, ← pullbackSpecIso_hom_fst]
      congr 2
      ext x
      symm
      change e.symm (algebraMap _ _ x) = Algebra.TensorProduct.includeLeftRingHom x
      rw [e.symm.commutes x]
      rfl
  have bot : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U))))
      hU₀a.fromSpec hUa.fromSpec i := by
    have e1 : CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X₀, i ⁻¹ᵁ U)) = i.appLE U (i ⁻¹ᵁ U) le_rfl := rfl
    rw [e1]
    have comm : Spec.map (i.appLE U (i ⁻¹ᵁ U) le_rfl) ≫ hUa.isoSpec.inv = hU₀a.isoSpec.inv ≫ (i ∣_ U) := by
      rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι,
        ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec]
    have sq : IsPullback (Spec.map (i.appLE U (i ⁻¹ᵁ U) le_rfl)) hU₀a.isoSpec.inv hUa.isoSpec.inv (i ∣_ U) :=
      IsPullback.of_vert_isIso ⟨comm⟩
    have := sq.paste_vert (isPullback_morphismRestrict i U)
    simpa only [IsAffineOpen.isoSpec_inv_ι] using this
  have big := top.paste_vert bot
  refine big.of_iso hV₀a.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
  have e2 : CommRingCat.ofHom (algebraMap Γ(X₀, i ⁻¹ᵁ U) Γ(Y₀, Y₀.basicOpen g)) =
      q₀.appLE (i ⁻¹ᵁ U) (Y₀.basicOpen g) hV₀le := rfl
  simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
  rw [e2, IsAffineOpen.SpecMap_appLE_fromSpec q₀ hU₀a hV₀a hV₀le, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]

end PhilipponEtaleThickeningLifts

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison


namespace PhilipponEtaleClosedPushforward

universe u
variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- Étale neighborhoods over the closed subscheme can be refined at each
point by pullbacks of étale neighborhoods over the original scheme. -/
theorem exists_neighborhood_lift [IsClosedImmersion i]
    {V : X.Etale} {W : Z.Etale} (g : W ⟶ (baseChange i).obj V) (w : W.left) :
    ∃ (U : X.Etale) (a : U ⟶ V) (b : (baseChange i).obj U ⟶ W)
      (z : ((baseChange i).obj U).left), b ≫ g = (baseChange i).map a ∧ b.left z = w := by
  let k := pullback.fst V.hom i
  have : IsClosedImmersion k := inferInstanceAs (IsClosedImmersion (pullback.fst V.hom i))
  have : Etale g.left := inferInstance
  obtain ⟨D, hw, T, q, hq, j, hp⟩ :=
    PhilipponEtaleThickeningLifts.exists_local_model k g.left w
  let U := Scheme.Etale.mk (q ≫ V.hom)
  let a : U ⟶ V := MorphismProperty.Over.homMk q rfl trivial
  let sq := map_isPullback i a
  let e := hp.isoIsPullback _ _ sq
  have hmap : e.inv ≫ (D.ι ≫ g.left) = ((baseChange i).map a).left :=
    hp.isoIsPullback_inv_snd _ _ sq
  have hg : (D.ι ≫ g.left) ≫ ((baseChange i).obj V).hom = D.ι ≫ W.hom :=
    (Category.assoc _ _ _).trans (congrArg (D.ι ≫ ·) (MorphismProperty.Over.w g))
  let b : (baseChange i).obj U ⟶ W := MorphismProperty.Over.homMk (e.inv ≫ D.ι) (by
    calc
      (e.inv ≫ D.ι) ≫ W.hom = e.inv ≫ (D.ι ≫ W.hom) := Category.assoc _ _ _
      _ = e.inv ≫ ((D.ι ≫ g.left) ≫ ((baseChange i).obj V).hom) :=
        congrArg (e.inv ≫ ·) hg.symm
      _ = ((baseChange i).map a).left ≫ ((baseChange i).obj V).hom :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hmap)
      _ = _ := MorphismProperty.Over.w ((baseChange i).map a)) trivial
  refine ⟨U, a, b, e.hom ⟨w, hw⟩, ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    change (e.inv ≫ D.ι) ≫ g.left = _
    rw [Category.assoc, hmap]
  · change (e.inv ≫ D.ι) (e.hom ⟨w, hw⟩) = w
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    rfl

private theorem covers_iff_at_points {B : Scheme.{u}} {V : B.Etale} (R : Sieve V) :
    R ∈ B.smallEtaleTopology V ↔
      ∀ x : V.left, ∃ (W : B.Etale) (a : W ⟶ V) (w : W.left), R a ∧ a.left w = x := by
  have h := Scheme.ofArrows_mem_smallEtaleTopology_iff
    (fun (g : R.arrows.category) => g.obj.hom)
  rw [Sieve.ofArrows_category] at h
  rw [h]
  simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_range]
  refine ⟨fun hc x => ?_, fun hc x => ?_⟩
  · obtain ⟨g, w, hw⟩ := hc x
    exact ⟨g.obj.left, g.obj.hom, w, g.property, hw⟩
  · obtain ⟨W, a, w, ha, hw⟩ := hc x
    exact ⟨⟨Over.mk a, ha⟩, w, hw⟩

private instance : PreservesFiniteLimits (baseChange i) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ i))

instance [IsClosedImmersion i] : (baseChange i).IsCoverDense Z.smallEtaleTopology where
  is_cover W := by
    let T := Scheme.Etale.mk (𝟙 X)
    let hT : IsTerminal T :=
      IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal
    let hB : IsTerminal ((baseChange i).obj T) :=
      IsTerminal.isTerminalObj (baseChange i) _ hT
    apply (covers_iff_at_points _).mpr
    intro w
    obtain ⟨U, _, b, z, _, hz⟩ := exists_neighborhood_lift i (hB.from W) w
    exact ⟨(baseChange i).obj U, b, z, Presieve.in_coverByImage (baseChange i) b, hz⟩

/-- Maps between the reductions of two étale charts lift after an étale
refinement of the source chart. -/
instance [IsClosedImmersion i] : (baseChange i).IsLocallyFull Z.smallEtaleTopology where
  functorPushforward_imageSieve_mem {U V} g := by
    let B := baseChange i
    let P := U ⨯ V
    let a : P ⟶ U := prod.fst
    let b : P ⟶ V := prod.snd
    let e := PreservesLimitPair.iso B U V
    let k : B.obj U ⟶ B.obj P := prod.lift (𝟙 _) g ≫ e.inv
    have hk₁ : k ≫ B.map a = 𝟙 (B.obj U) := by
      simp only [k, e, a, Category.assoc, PreservesLimitPair.iso_inv_fst]
      exact prod.lift_fst (𝟙 (B.obj U)) g
    have hk₂ : k ≫ B.map b = g := by
      simp only [k, e, b, Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]
    have hk₁' : k.left ≫ (B.map a).left = 𝟙 (B.obj U).left :=
      congrArg (fun m => m.left) hk₁
    have hk₂' : k.left ≫ (B.map b).left = g.left :=
      congrArg (fun m => m.left) hk₂
    have : Mono k.left := mono_of_mono_fac hk₁'
    have : Etale k.left := inferInstance
    have : IsOpenImmersion k.left := IsOpenImmersion.of_flat_of_mono _
    let p := pullback.fst P.hom i
    have : IsClosedImmersion p := inferInstanceAs
      (IsClosedImmersion (pullback.fst P.hom i))
    obtain ⟨D, hD, hpre⟩ := p.isClosedEmbedding.isInducing.isOpen_iff.mp
      k.left.isOpenMap.isOpen_range
    let O : P.left.Opens := ⟨D, hD⟩
    let Q := Scheme.Etale.mk (O.ι ≫ P.hom)
    let r : Q ⟶ P := MorphismProperty.Over.homMk O.ι rfl trivial
    have hr : Set.range (B.map r).left = Set.range k.left := by
      have h := Scheme.image_preimage_eq_of_isPullback (map_isPullback i r)
        (Set.univ : Set Q.left)
      simp only [Set.preimage_univ, Set.image_univ] at h
      change Set.range (B.map r).left = p ⁻¹' Set.range O.ι at h
      rw [Scheme.Opens.range_ι] at h
      exact h.trans hpre
    let l := IsOpenImmersion.lift k.left (B.map r).left hr.le
    have hl : l ≫ k.left = (B.map r).left := IsOpenImmersion.lift_fac _ _ _
    have ha : (B.map (r ≫ a)).left = l := by
      rw [B.map_comp]
      change (B.map r).left ≫ (B.map a).left = l
      rw [← hl, Category.assoc, hk₁', Category.comp_id]
    have hb : B.map (r ≫ b) = B.map (r ≫ a) ≫ g := by
      apply MorphismProperty.Over.Hom.ext
      rw [B.map_comp]
      change (B.map r).left ≫ (B.map b).left = (B.map (r ≫ a)).left ≫ g.left
      rw [← hl, Category.assoc, hk₂', ha]
    apply (covers_iff_at_points _).mpr
    intro y
    obtain ⟨z, hz⟩ := hr.symm.le (Set.mem_range_self (f := k.left) y)
    refine ⟨B.obj Q, B.map (r ≫ a), z, ?_, ?_⟩
    · exact Sieve.image_mem_functorPushforward B _ ⟨r ≫ b, hb⟩
    · rw [B.map_comp]
      change (B.map a).left ((B.map r).left z) = y
      rw [hz, ← Scheme.Hom.comp_apply, hk₁']
      rfl

/-- Direct image along a closed immersion is fully faithful on étale
abelian sheaves. -/
def fullyFaithfulPushforward [IsClosedImmersion i] : (pushforward i).FullyFaithful := by
  unfold pushforward
  exact Functor.FullyFaithful.ofFullyFaithful _

private theorem exists_empty_neighborhood [IsClosedImmersion i]
    (V : X.Etale) (x : V.left) (hx : x ∉ Set.range (pullback.fst V.hom i)) :
    ∃ (U : X.Etale) (a : U ⟶ V) (y : U.left),
      IsEmpty ((baseChange i).obj U).left ∧ a.left y = x := by
  let k := pullback.fst V.hom i
  have : IsClosedImmersion k := inferInstanceAs (IsClosedImmersion (pullback.fst V.hom i))
  let D : V.left.Opens := ⟨(Set.range k)ᶜ, k.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U := Scheme.Etale.mk (D.ι ≫ V.hom)
  let a : U ⟶ V := MorphismProperty.Over.homMk D.ι rfl trivial
  refine ⟨U, a, ⟨x, hx⟩, ⟨fun z => ?_⟩, rfl⟩
  let y : D := pullback.fst U.hom i z
  have e := congrArg (fun s : ((baseChange i).obj U).left ⟶ V.left => s z)
    (map_isPullback i a).w
  exact y.property ⟨((baseChange i).map a).left z, e.symm⟩

/-- The direct image has zero stalk at every geometric point outside a
closed immersion's image. -/
theorem isZero_stalk_pushforward_of_not_mem_range [IsClosedImmersion i]
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)
    (hs : s default ∉ Set.range i) (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward i).obj G)) := by
  let Φ := Scheme.pointSmallEtale s
  let P := ((pushforward i).obj G).obj
  change IsZero (Φ.presheafFiber.obj P)
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  suffices h : ∀ z : ↥(Φ.presheafFiber.obj P), z = 0 from
    ⟨fun a b => (h a).trans (h b).symm⟩
  intro z
  obtain ⟨V, t, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective z
  let z₀ : Spec (CommRingCat.of K) := default
  have hx : t.left z₀ ∉ Set.range (pullback.fst V.hom i) := by
    rw [Scheme.Pullback.range_fst]
    have ht : V.hom (t.left z₀) = s default :=
      (Scheme.pointSmallEtaleFiberObjToPreimage s rfl t).property
    change V.hom (t.left z₀) ∉ Set.range i
    rwa [ht]
  obtain ⟨U, e, y, hU, hy⟩ := exists_empty_neighborhood i V (t.left z₀) hx
  obtain ⟨l, hl, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed e.left t.left y hy
  let v : Φ.fiber.obj U := Over.homMk l (by
    change l ≫ U.hom = s
    rw [← MorphismProperty.Over.w e, ← Category.assoc, hl]
    exact Over.w t)
  have hv : Φ.fiber.map e v = t :=
    Over.OverMorphism.ext hl
  have hzero : P.map e.op a = 0 := by
    change G.obj.map ((baseChange i).map e).op a = 0
    exact (Scheme.subsingleton_sections_of_isEmpty hU G).elim _ _
  rw [← hv, ← Φ.toPresheafFiber_w_apply, hzero, map_zero]

end PhilipponEtaleClosedPushforward

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtaleAcyclicCohomology

universe u

private abbrev AbelianSheaves (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private def isTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

private def terminalComparison {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (baseChange f).obj (terminal X) ≅ terminal Y := by
  have : PreservesFiniteLimits (baseChange f) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ f))
  exact (IsTerminal.isTerminalObj (baseChange f) _ (isTerminal X)).uniqueUpToIso (isTerminal Y)

/-- Evaluation of the direct-image comparison uses the unique arrow
to the base change of the terminal chart. -/
theorem globalSectionsIso_hom_app_eq_map {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : AbelianSheaves Y) (k : terminal Y ⟶ (baseChange f).obj (terminal X)) :
    (globalSectionsIso f).hom.app F = F.obj.map k.op := by
  have ht := (isTerminal Y).ofIso (terminalComparison f).symm
  rw [ht.hom_ext k (terminalComparison f).inv]
  rfl

end PhilipponEtaleAcyclicCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleBaseChangeMap (stalkToFiberSections stalkOfHigherImageIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtalePullbackResolution

universe u

/-- Restrict global sections along the unit of étale inverse image. -/
def restrictGlobalSections {X Y : Scheme.{u}} (f : Y ⟶ X) :
    globalSections X ⟶ pullbackSheaves f ⋙ globalSections Y :=
  (Functor.leftUnitor (globalSections X)).inv ≫
    Functor.whiskerRight (pullbackAdjunction f).unit (globalSections X) ≫
    (Functor.associator (pullbackSheaves f) (pushforward f) (globalSections X)).hom ≫
    (Functor.isoWhiskerLeft (pullbackSheaves f) (globalSectionsIso f)).hom

end PhilipponEtalePullbackResolution

end

end


