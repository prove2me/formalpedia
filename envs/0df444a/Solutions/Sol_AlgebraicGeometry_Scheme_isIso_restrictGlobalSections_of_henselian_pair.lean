-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isIso_restrictGlobalSections_of_henselian_pair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T23:07:42.905344+00:00
-- url     : https://prove2.me/submissions/467556f9-e396-4440-a538-f424c43a580d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleClosedImmersionSections
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionDescent
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Tactic.Ring
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_coproduct_strictlyHenselian_of_finite
import Theorems.Thm_HenselianRing_of_isIntegral

set_option maxHeartbeats 1600000

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleGeometricStalks (geometricMap geometricMap_apply geometricPoint)


namespace PhilipponEtaleClosedFiberCovers

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}

private abbrev terminalChart (Y : Scheme.{u}) := Scheme.Etale.mk (𝟙 Y)

private def terminalPoint (y : Y) : (geometricPoint y).fiber.obj (terminalChart Y) :=
  Over.homMk (geometricMap y) (Category.comp_id _)

/-- Global étale sections are determined by their germs at a set of points
meeting every point closure. -/
theorem globalSections_eq_of_germs_eq_on
    (S : Set Y) (hS : ∀ y : Y, (S ∩ closure ({y} : Set Y)).Nonempty)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (a b : ↥(F.obj.obj (op (terminalChart Y))))
    (h : ∀ y ∈ S,
      (geometricPoint y).toPresheafFiber (terminalChart Y) (terminalPoint y) F.obj a =
        (geometricPoint y).toPresheafFiber (terminalChart Y) (terminalPoint y) F.obj b) :
    a = b := by
  classical
  let T := terminalChart Y
  let E := Presheaf.equalizerSieve (F := F.obj) (X := op T) a b
  have hRefine (y : Y) (hy : y ∈ S) :
      ∃ (V : Y.Etale) (g : V ⟶ T), E g ∧ y ∈ Set.range g.left := by
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
  let Q := {y : Y // y ∈ S}
  choose V g hg hy using fun y : Q => hRefine y.val y.property
  have hCover : Sieve.ofArrows V g ∈ Y.smallEtaleTopology T := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
    have hOpen : IsOpen (⋃ j, Set.range (g j).left) :=
      isOpen_iUnion fun j => (g j).left.isOpenMap.isOpen_range
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨z, hz, hzy⟩ := hS y
    exact (specializes_iff_mem_closure.mpr hzy).mem_open hOpen
      (Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hy ⟨z, hz⟩⟩)
  have hE : E ∈ Y.smallEtaleTopology T :=
    Y.smallEtaleTopology.superset_covering
      ((Sieve.generate_le_iff _ _).mpr (by
        rintro _ _ ⟨j⟩
        exact hg j)) hCover
  have hSheaf := Presheaf.isSheaf_comp_of_isSheaf Y.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp hSheaf _ hE).isSeparatedFor.ext
    (fun _ _ hab => hab)

end PhilipponEtaleClosedFiberCovers

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSectionsIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleRefinedSectionLifts (exists_global_lift_on_finite_cover pullClosedSection)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleZariskiSections (openToTerminal exists_global_lift_of_open_lifts)
open PhilipponZariskiTorsorCoordinates (opensToEtale)


namespace PhilipponEtaleClosedFiberSections

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Restriction of sections is injective if chosen geometric points lift
from a subset that meets every point closure. -/
theorem restrictGlobalSections_app_injective_of_meets_closures {Y Z : Scheme.{u}}
    (i : Z ⟶ Y) (S : Set Y) (hS : ∀ y : Y, (S ∩ closure ({y} : Set Y)).Nonempty)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (hLift : ∀ y ∈ S,
      ∃ t : Spec (CommRingCat.of (SeparableClosure (Y.residueField y))) ⟶ Z,
        t ≫ i = geometricMap y) :
    Function.Injective ((restrictGlobalSections i).app F) := by
  let T := Scheme.Etale.mk (𝟙 Y)
  let F' := (pushforward i).obj ((pullbackSheaves i).obj F)
  let η : F ⟶ F' := (pullbackAdjunction i).unit.app F
  let e := (globalSectionsIso i).app ((pullbackSheaves i).obj F)
  intro a b hab
  have hη : η.hom.app (op T) a = η.hom.app (op T) b := by
    apply (AddCommGrpCat.mono_iff_injective e.hom).1 inferInstance
    exact hab
  apply PhilipponEtaleClosedFiberCovers.globalSections_eq_of_germs_eq_on S hS F
  intro y hy
  let Φ := geometricPoint y
  obtain ⟨t, ht⟩ := hLift y hy
  let P (s : Spec (CommRingCat.of (SeparableClosure (Y.residueField y))) ⟶ Y) :=
    Function.Injective ((Scheme.pointSmallEtale s).sheafFiber.map η)
  have hinj : P (geometricMap y) :=
    (congrArg P ht).mp (PhilipponEtaleStalkPullback.stalk_unit_injective i t F)
  let v : Φ.fiber.obj T := Over.homMk (geometricMap y) (Category.comp_id _)
  apply hinj
  change (Φ.presheafFiber.map η.hom) (Φ.toPresheafFiber T v F.obj a) =
    (Φ.presheafFiber.map η.hom) (Φ.toPresheafFiber T v F.obj b)
  calc
    _ = Φ.toPresheafFiber T v F'.obj (η.hom.app (op T) a) :=
      Φ.toPresheafFiber_naturality_apply η.hom T v a
    _ = Φ.toPresheafFiber T v F'.obj (η.hom.app (op T) b) := congrArg _ hη
    _ = _ := (Φ.toPresheafFiber_naturality_apply η.hom T v b).symm

end PhilipponEtaleClosedFiberSections

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleClosedFiberSections (FiniteCoverLifts closedFiberι exists_closedFiber_lift_on_finite_cover)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap)
open PhilipponEtalePullbackComposition (restrictGlobalSections_app_eq)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStrictHenselization (toBase)
open PhilipponFiniteEtaleDescent (HasClosedStrictLocalComponents)


namespace PhilipponEtaleClosedFiberDegreeZero

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

set_option maxRecDepth 4096 in
private theorem descend_lift {X P Z Q B : Scheme.{u}} (p : P ⟶ X) [IsFinite p] [Surjective p]
    (i : Z ⟶ X) (d₁ d₂ : Q ⟶ P) (ρ : Q ⟶ X) (hsq : IsPullback d₁ d₂ p p)
    (h₁ : d₁ ≫ p = ρ) (h₂ : d₂ ≫ p = ρ)
    (j : B ⟶ Q) (r : B ⟶ Z) (τ : B ⟶ X) [IsFinite τ]
    (hj : j ≫ ρ = τ) (hr : r ≫ i = τ)
    (hSplitP : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p))
    (hSplitT : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) τ))
    (F : Ab X) (a : (globalSections X).obj ((pushforward i).obj ((pullbackSheaves i).obj F)))
    (b : (globalSections P).obj ((pullbackSheaves p).obj F))
    (hInj : Function.Injective ((restrictGlobalSections j).app ((pullbackSheaves ρ).obj F)))
    (hb : ((pullbackAdjunction (pullback.fst p i)).unit.app ((pullbackSheaves p).obj F)).hom.app
      (op (Scheme.Etale.mk (𝟙 P))) b = PhilipponEtaleRefinedSectionLifts.pullClosedSection i p F a) :
    ∃ c : (globalSections X).obj F, (globalSections X).map ((pullbackAdjunction i).unit.app F) c = a := by
  refine PhilipponEtaleRefinedSectionLifts.closedLift_induction i p F a b hb ?_
  intro A u v σ hu hv hUV hSurj hAgree
  let : Surjective v := hSurj
  exact PhilipponEtaleClosedLiftDescent.exists_preimage_of_closed_lift p i d₁ d₂ ρ hsq h₁ h₂
    u v hUV σ hu hv j r τ hj hr hSplitP hSplitT F
    ((globalSectionsIso p).inv.app ((pullbackSheaves p).obj F) b) a hInj hAgree

/-- Restriction is injective over the closed part of each finite cover. -/
def FiniteOverlapInjection {X Z : Scheme.{u}} (i : Z ⟶ X) : Prop :=
  ∀ {Q : Scheme.{u}} (ρ : Q ⟶ X) [IsFinite ρ] (G : Ab Q),
    ∃ (B : Scheme.{u}) (j : B ⟶ Q) (r : B ⟶ Z) (τ : B ⟶ X),
      IsFinite τ ∧ j ≫ ρ = τ ∧ r ≫ i = τ ∧
        Function.Injective ((restrictGlobalSections j).app G)

set_option maxRecDepth 4096 in
/-- Finite-cover lifts descend to global sections when they agree on overlaps. -/
theorem unitSections_surjective_of_lifts {X Z : Scheme.{u}} (i : Z ⟶ X) (F : Ab X)
    (hLifts : FiniteCoverLifts i F) (hOverlap : FiniteOverlapInjection i)
    (hSplit : ∀ {P : Scheme.{u}} (p : P ⟶ X) [IsFinite p], ∀ x : X,
      HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p)) :
    Function.Surjective ((globalSections X).map ((pullbackAdjunction i).unit.app F)) := by
  intro a
  obtain ⟨P, p, hp, hs, b, hb⟩ := hLifts a
  let : IsFinite p := hp
  let : Surjective p := hs
  obtain ⟨Q, d₁, d₂, ρ, hFinite, hsq, h₁, h₂⟩ := exists_finite_overlap p
  let : IsFinite ρ := hFinite
  obtain ⟨B, j, r, τ, hFinite', hj, hr, hInj⟩ := hOverlap ρ ((pullbackSheaves ρ).obj F)
  let : IsFinite τ := hFinite'
  exact descend_lift p i d₁ d₂ ρ hsq h₁ h₂ j r τ hj hr (hSplit p) (hSplit τ) F a b hInj hb

end PhilipponEtaleClosedFiberDegreeZero

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward
  (pushforward fullyFaithfulPushforward isZero_stalk_pushforward_of_not_mem_range)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback
  (exists_point_lift_of_mem_range stalk_unit_isIso stalkPullbackIso)


namespace PhilipponEtaleClosedImmersionBaseChange

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- A sheaf with zero stalks off a closed subscheme is recovered by
restricting to the closed subscheme and taking the direct image. -/
theorem isIso_unit_of_support {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (F : Ab X)
    (hF : ∀ x : X, geometricMap x default ∉ Set.range f →
      IsZero ((geometricPoint x).sheafFiber.obj F)) :
    IsIso ((pullbackAdjunction f).unit.app F) := by
  let P := ObjectProperty.ofObj fun x : X => geometricPoint x
  have hP : P.IsConservativeFamilyOfPoints :=
    Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let η := (pullbackAdjunction f).unit.app F
  apply ((hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff η).mpr
  intro Φ
  have h := Φ.property
  change ObjectProperty.ofObj (fun x : X => geometricPoint x) Φ.obj at h
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp h
  rw [← hx]
  by_cases hs : geometricMap x default ∈ Set.range f
  · obtain ⟨t, ht⟩ := exists_point_lift_of_mem_range f (geometricMap x) hs
    change IsIso ((Scheme.pointSmallEtale (geometricMap x)).sheafFiber.map η)
    rw [← ht]
    exact stalk_unit_isIso f t F
  · exact (hF x hs).isIso
      (isZero_stalk_pushforward_of_not_mem_range f (geometricMap x) hs
        ((pullbackSheaves f).obj F)) _

end PhilipponEtaleClosedImmersionBaseChange

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleClosedImmersionBaseChange (isIso_unit_of_support)
open PhilipponEtalePullbackComposition (pullbackCompIso restrictGlobalSections_app_eq)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleIteratedFiberSections

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- Pulling sections back along a scheme isomorphism gives an isomorphism. -/
theorem isIso_restrictGlobalSections_of_isIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f]
    (F : Ab X) : IsIso ((restrictGlobalSections f).app F) := by
  let : IsIso ((pullbackAdjunction f).unit.app F) := by
    apply isIso_unit_of_support f F
    intro x hx
    exact (hx (f.surjective _)).elim
  rw [restrictGlobalSections_app_eq]
  infer_instance
end PhilipponEtaleIteratedFiberSections

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PhilipponSchemeIdempotents

universe u

/-- The characteristic section of a clopen subset is a global idempotent. -/
theorem exists_idempotent_of_clopen (X : Scheme.{u}) {s : Set X} (hs : IsClopen s) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      (∀ x ∈ s, X.presheaf.Γgerm x e = 1) ∧
      (∀ x ∉ s, X.presheaf.Γgerm x e = 0) := by
  classical
  let U : Bool → X.Opens := fun i => if i then ⟨s, hs.2⟩ else ⟨sᶜ, hs.1.isOpen_compl⟩
  let a (i : Bool) : Γ(X, U i) := if i then 1 else 0
  let k (i : Bool) : U i ⟶ ⊤ := homOfLE le_top
  have hDisj : ∀ i j : Bool, i ≠ j → U i ⊓ U j = ⊥ := by
    intro i j hij
    cases i <;> cases j <;> simp_all [U]
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    rw [Opens.mem_iSup]
    by_cases hx : x ∈ s
    · exact ⟨true, by simpa [U] using hx⟩
    · exact ⟨false, by simpa [U] using hx⟩
  have hCompatible : TopCat.Presheaf.IsCompatible X.presheaf U a := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · exact (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (hDisj i j hij))).elim _ _
  obtain ⟨e, hRes, hUnique⟩ := X.sheaf.existsUnique_gluing' U ⊤ k hcover a hCompatible
  have hRes' (i : Bool) : (X.presheaf.map (k i).op).hom e = a i := hRes i
  have he : IsIdempotentElem e := by
    change e * e = e
    apply hUnique
    intro i
    let g := (X.presheaf.map (k i).op).hom
    calc
      g (e * e) = g e * g e := map_mul g e e
      _ = a i * a i := congrArg (fun z : Γ(X, U i) => z * z) (hRes' i)
      _ = a i := by cases i <;> simp [a]
  have hg (i : Bool) (x : X) (hx : x ∈ U i) :
      X.presheaf.Γgerm x e = X.presheaf.germ (U i) x hx (a i) := by
    rw [← hRes' i]
    exact (X.presheaf.germ_res_apply (k i) x hx e).symm
  refine ⟨e, he, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ U true := by simpa [U] using hx
    simpa only [a, if_true, map_one] using hg true x hx'
  · intro x hx
    have hx' : x ∈ U false := by simpa [U] using hx
    simpa only [a, Bool.false_eq_true, if_false, map_zero] using hg false x hx'

/-- A scheme whose global functions have only trivial idempotents has
preconnected underlying space. -/
theorem preconnectedSpace_of_trivial_idempotents (X : Scheme.{u})
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) : PreconnectedSpace X := by
  apply preconnectedSpace_iff_clopen.2
  intro s hs
  obtain ⟨e, he, h1, h0⟩ := exists_idempotent_of_clopen X hs
  rcases h e he with he₀ | he₁
  · left
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact zero_ne_one (by simpa only [he₀, map_zero] using h1 x hx)
  · right
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact one_ne_zero (by simpa only [he₁, map_one] using h0 x hx)

end PhilipponSchemeIdempotents

end

section

set_option autoImplicit false

open Polynomial

namespace PhilipponHenselianIdempotents

/-- Idempotents of an affine quotient lift across a henselian pair. -/
theorem exists_lift {A B : Type*} [CommRing A] [CommRing B]
    (r : A →+* B) (hr : Function.Surjective r) [HenselianRing A (RingHom.ker r)]
    (e : B) (he : IsIdempotentElem e) : ∃ a : A, IsIdempotentElem a ∧ r a = e := by
  obtain ⟨a₀, ha₀⟩ := hr e
  let f : A[X] := X ^ 2 - X
  have hmonic : f.Monic := monic_X_pow_sub (degree_X_le.trans_lt (by decide))
  have hf : f.eval a₀ ∈ RingHom.ker r := by
    rw [RingHom.mem_ker]
    simp [f, ha₀, pow_two, he.eq]
  have hderiv : IsUnit (2 * e - 1) := by
    apply IsUnit.of_mul_eq_one (b := 2 * e - 1)
    calc
      (2 * e - 1) * (2 * e - 1) = 4 * (e * e - e) + 1 := by ring
      _ = 1 := by simp [he.eq]
  let q := r.quotientKerEquivOfSurjective hr
  have hmap : q (Ideal.Quotient.mk _ (f.derivative.eval a₀)) = 2 * e - 1 := by
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp [f, ha₀, two_mul, add_mul]
  let d := Ideal.Quotient.mk (RingHom.ker r) (f.derivative.eval a₀)
  have hq : IsUnit (q d) := hmap.symm ▸ hderiv
  have hunit : IsUnit d := by
    have hback : IsUnit (q.symm (q d)) := hq.map q.symm.toMonoidHom
    rwa [RingEquiv.symm_apply_apply] at hback
  obtain ⟨a, ha, hdiff⟩ := HenselianRing.is_henselian f hmonic a₀ hf hunit
  refine ⟨a, ?_, ?_⟩
  · simpa [Polynomial.IsRoot, f, pow_two, sub_eq_zero, IsIdempotentElem] using ha
  · rw [RingHom.mem_ker, map_sub, sub_eq_zero, ha₀] at hdiff
    exact hdiff

end PhilipponHenselianIdempotents

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponHenselianPairConnectedness

universe u

/-- Henselian pairs are stable under integral base change. -/
abbrev IntegralStability : Prop :=
  ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A)
    [HenselianRing A I], f.IsIntegral → HenselianRing B (I.map f)

/-- In the spectrum of a domain, a closed subset cut out by a henselian
ideal is connected, since all its idempotents lift. -/
theorem isConnected_zeroLocus {A : Type u} [CommRing A] [IsDomain A]
    (I : Ideal A) [HenselianRing A I] : _root_.IsConnected (PrimeSpectrum.zeroLocus (I : Set A)) := by
  let r := Ideal.Quotient.mk I
  let : HenselianRing A (RingHom.ker r) := by simpa [r] using (inferInstance : HenselianRing A I)
  have htop : I ≠ ⊤ := by
    intro ht
    have h := HenselianRing.jac (R := A) (I := I)
    rw [ht] at h
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp (top_unique h))
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr htop
  let S := Spec (.of (A ⧸ I))
  let e := (Scheme.ΓSpecIso (.of (A ⧸ I))).commRingCatIsoToRingEquiv
  let : PreconnectedSpace S := PhilipponSchemeIdempotents.preconnectedSpace_of_trivial_idempotents S (by
    intro a ha
    obtain ⟨b, hb, hba⟩ := PhilipponHenselianIdempotents.exists_lift r Ideal.Quotient.mk_surjective
      (e a) (ha.map e.toRingHom)
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hb with h₀ | h₁
    · left
      apply e.injective
      rw [← hba, h₀, map_zero, map_zero]
    · right
      apply e.injective
      rw [← hba, h₁, map_one, map_one])
  let : ConnectedSpace (PrimeSpectrum (A ⧸ I)) :=
    { toPreconnectedSpace := inferInstanceAs (PreconnectedSpace S)
      toNonempty := inferInstance }
  have h := isConnected_univ.image (PrimeSpectrum.comap r) (PrimeSpectrum.continuous_comap r).continuousOn
  rw [Set.image_univ, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker] at h
  exact h

/-- Connectedness of closed-fiber intersections with point closures on
a finite scheme over a henselian pair, from integral stability. -/
theorem isConnected_inter_closure (stable : IntegralStability.{u})
    {A B : Type u} [CommRing A] [CommRing B] (r : A →+* B) [HenselianRing A (RingHom.ker r)]
    (hr : Function.Surjective r) {P : Scheme.{u}} (p : P ⟶ Spec (.of A)) [IsFinite p] (x : P) :
    _root_.IsConnected (Set.range (pullback.fst p (Spec.map (CommRingCat.ofHom r))) ∩ closure ({x} : Set P)) := by
  let : IsAffine P := isAffine_of_isAffineHom p
  let S := Γ(P, ⊤)
  let e := P.isoSpec
  let y : PrimeSpectrum S := e.hom x
  let T := S ⧸ y.asIdeal
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk y.asIdeal)) ≫ e.inv
  have hrange : Set.range j = closure ({x} : Set P) := by
    change Set.range (e.inv ∘ PrimeSpectrum.comap (Ideal.Quotient.mk y.asIdeal)) = _
    rw [Set.range_comp, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, ← PrimeSpectrum.closure_singleton]
    change e.inv.homeomorph '' closure ({y} : Set (Spec S)) = _
    have hy : e.inv.homeomorph y = x := by
      change (e.hom ≫ e.inv) x = x
      rw [e.hom_inv_id]
      rfl
    rw [Homeomorph.image_closure, Set.image_singleton, hy]
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk y.asIdeal))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let : IsFinite (j ≫ p) := inferInstanceAs (IsFinite
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk y.asIdeal)) ≫ e.inv) ≫ p))
  let f : CommRingCat.of A ⟶ CommRingCat.of T := Spec.preimage (j ≫ p)
  have hf : Spec.map f = j ≫ p := Spec.map_preimage _
  have hFinite : f.hom.Finite := (IsFinite.SpecMap_iff f).mp (hf.symm ▸ inferInstanceAs (IsFinite (j ≫ p)))
  let I := RingHom.ker r
  let : HenselianRing T (I.map f.hom) := stable f.hom I (RingHom.finite_iff_isIntegral_and_finiteType.mp hFinite).1
  have hC := isConnected_zeroLocus (I.map f.hom)
  let i := Spec.map (CommRingCat.ofHom r)
  have hi : Set.range i = PrimeSpectrum.zeroLocus (I : Set A) :=
    range_comap_of_surjective _ _ hr
  have hpre : j ⁻¹' (p ⁻¹' Set.range i) = PrimeSpectrum.zeroLocus (I.map f.hom : Set T) := by
    rw [hi, ← Set.preimage_comp]
    change (j ≫ p) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) = _
    rw [← hf]
    change PrimeSpectrum.comap f.hom ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) = _
    rw [PrimeSpectrum.preimage_comap_zeroLocus, ← PrimeSpectrum.zeroLocus_span, ← Ideal.map_span, Ideal.span_eq]
  have hj := hC.image j j.continuous.continuousOn
  rw [← hpre, Set.image_preimage_eq_inter_range, hrange, ← Scheme.Pullback.range_fst] at hj
  exact hj

end PhilipponHenselianPairConnectedness

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleClosedFiberDegreeZero (FiniteOverlapInjection unitSections_surjective_of_lifts)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap geometricMap geometricMap_apply)
open PhilipponEtaleLocalRing (stalkRing)
open PhilipponEtalePullbackComposition (pullbackCompIso restrictGlobalSections_app_eq restrictGlobalSections_comp)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (exists_point_lift_of_mem_range)
open PhilipponEtaleStrictHenselization (toBase)
open PhilipponFiniteEtaleDescent (HasClosedStrictLocalComponents)


namespace PhilipponHenselianPairSections

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (r : A →+* B)

private abbrev X := Spec (CommRingCat.of A)
private abbrev i := Spec.map (CommRingCat.ofHom r)
private abbrev fiber : Set (X (A := A)) := PrimeSpectrum.zeroLocus (RingHom.ker r : Set A)

private theorem fiber_meets_closures (h : RingHom.ker r ≤ Ideal.jacobson ⊥) (y : X (A := A)) :
    (fiber r ∩ closure ({y} : Set (X (A := A)))).Nonempty := by
  obtain ⟨m, hm, hym⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
  let z : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  refine ⟨z, (PrimeSpectrum.mem_zeroLocus z _).mpr (h.trans (sInf_le ⟨bot_le, hm⟩)), ?_⟩
  change z ∈ closure ({y} : Set (PrimeSpectrum A))
  rw [PrimeSpectrum.closure_singleton]
  exact hym

private theorem range_i (hr : Function.Surjective r) : Set.range (i r) = fiber r :=
  range_comap_of_surjective _ _ hr

/-- Restriction of global étale sections along an affine quotient with
kernel in the Jacobson radical is injective. -/
theorem restrictGlobalSections_injective (hr : Function.Surjective r)
    (h : RingHom.ker r ≤ Ideal.jacobson ⊥)
    (F : Sheaf (X (A := A)).smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Injective ((restrictGlobalSections (i r)).app F) := by
  let : IsClosedImmersion (i r) := IsClosedImmersion.spec_of_surjective _ hr
  apply PhilipponEtaleClosedFiberSections.restrictGlobalSections_app_injective_of_meets_closures
    (i r) (fiber r) (fiber_meets_closures r h) F
  intro y hy
  exact exists_point_lift_of_mem_range (i r) (geometricMap y) (by rwa [range_i r hr, geometricMap_apply])

/-- After a proper base change, sections are still determined by their
restriction to the inverse image of a quotient supported at all closed points. -/
theorem restrictGlobalSections_injective_on_baseChange (hr : Function.Surjective r)
    (h : RingHom.ker r ≤ Ideal.jacobson ⊥) {Y : Scheme.{u}} (f : Y ⟶ X (A := A)) [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Injective ((restrictGlobalSections (pullback.fst f (i r))).app F) := by
  let : IsClosedImmersion (i r) := IsClosedImmersion.spec_of_surjective _ hr
  let j := pullback.fst f (i r)
  let S := f ⁻¹' fiber r
  have hS (y : Y) : (S ∩ closure ({y} : Set Y)).Nonempty := by
    obtain ⟨z, hz, hzy⟩ := fiber_meets_closures r h (f y)
    have hclosed : IsClosed (f '' closure ({y} : Set Y)) := f.isClosedMap _ isClosed_closure
    obtain ⟨w, hw, hwz⟩ := (specializes_iff_mem_closure.mpr hzy).mem_closed hclosed
      ⟨y, subset_closure rfl, rfl⟩
    refine ⟨w, ?_, hw⟩
    change f w ∈ fiber r
    rwa [hwz]
  apply PhilipponEtaleClosedFiberSections.restrictGlobalSections_app_injective_of_meets_closures
    j S hS F
  intro y hy
  apply exists_point_lift_of_mem_range j (geometricMap y)
  change geometricMap y default ∈ Set.range (pullback.fst f (i r))
  rwa [Scheme.Pullback.range_fst, range_i r hr, geometricMap_apply]

/-- The degree-zero comparison follows from connected intersections with
point closures on finite covers and decomposition over strict henselizations. -/
theorem isIso_restrictGlobalSections_of_connectedness (hr : Function.Surjective r)
    (h : RingHom.ker r ≤ Ideal.jacobson ⊥)
    (hConn : ∀ {P : Scheme.{u}} (p : P ⟶ X (A := A)), IsFinite p → Surjective p →
      ∀ x : P, IsConnected (Set.range (pullback.fst p (i r)) ∩ closure ({x} : Set P)))
    (hSplit : ∀ {P : Scheme.{u}} (p : P ⟶ X (A := A)) [IsFinite p], ∀ x : X (A := A),
      HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p))
    (F : Sheaf (X (A := A)).smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((restrictGlobalSections (i r)).app F) := by
  let : IsClosedImmersion (i r) := IsClosedImmersion.spec_of_surjective _ hr
  let : SpectralSpace (X (A := A)) := inferInstanceAs (SpectralSpace (PrimeSpectrum A))
  have hOverlap : FiniteOverlapInjection (i r) := by
    intro Q p hp G
    let a := pullback.fst p (i r)
    let b := pullback.snd p (i r)
    refine ⟨pullback p (i r), a, b, a ≫ p,
      inferInstanceAs (IsFinite (pullback.fst p (i r) ≫ p)), rfl, pullback.condition.symm, ?_⟩
    exact restrictGlobalSections_injective_on_baseChange r hr h p G
  have hLifts : PhilipponEtaleClosedFiberSections.FiniteCoverLifts (i r) F :=
    PhilipponEtaleRefinedSectionLifts.exists_global_lift_on_finite_cover (i r) F hConn
  have hSurj := unitSections_surjective_of_lifts (i r) F hLifts hOverlap hSplit
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨restrictGlobalSections_injective r hr h F, ?_⟩
  let e := (globalSectionsIso (i r)).app ((pullbackSheaves (i r)).obj F)
  intro b
  obtain ⟨a, ha⟩ := hSurj (e.inv b)
  refine ⟨a, ?_⟩
  rw [restrictGlobalSections_app_eq]
  exact (congrArg (fun x => e.hom x) ha).trans (ConcreteCategory.congr_hom e.inv_hom_id b)

/-- A finite scheme over a strictly henselian local ring decomposes into
a finite coproduct of strictly henselian local spectra. -/
abbrev StrictFiniteDecomposition : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [IsFinite p],
    ∃ (ι : Type u) (_ : Fintype ι) (T : ι → Type u) (_ : ∀ i, CommRing (T i))
      (h : ∀ i, HenselianLocalRing (T i)),
      (∀ i, let _ := h i; IsSepClosed (IsLocalRing.ResidueField (T i))) ∧
        ∃ (c : (∐ fun i ↦ Spec (.of (T i))) ≅ Y),
          ∀ i, IsClosedImmersion (Sigma.ι (fun j ↦ Spec (.of (T j))) i ≫ c.hom)

/-- Given the finite-scheme decomposition theorem, the remaining input
for degree zero is connectedness of the intersections with point closures. -/
theorem isIso_restrictGlobalSections_of_finite_decomposition (decompose : StrictFiniteDecomposition.{u})
    (hr : Function.Surjective r) (h : RingHom.ker r ≤ Ideal.jacobson ⊥)
    (hConn : ∀ {P : Scheme.{u}} (p : P ⟶ X (A := A)), IsFinite p → Surjective p →
      ∀ x : P, IsConnected (Set.range (pullback.fst p (i r)) ∩ closure ({x} : Set P)))
    {Z : Scheme.{u}} (e : Z ≅ Spec (.of B)) (F : Sheaf (X (A := A)).smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((restrictGlobalSections (e.hom ≫ i r)).app F) := by
  have hSplit {P : Scheme.{u}} (p : P ⟶ X (A := A)) [IsFinite p] (x : X (A := A)) :
      HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p) := by
    let s := algebraicallyClosedGeometricMap x
    let q := pullback.fst (toBase s) p
    let : IsFinite q := inferInstanceAs (IsFinite (pullback.fst (toBase s) p))
    obtain ⟨ι, _, T, hT, hH, hK, c, hc⟩ := decompose (stalkRing s) q
    exact ⟨ι, T, hT, hH, hK, c, hc⟩
  let : IsIso ((restrictGlobalSections (i r)).app F) :=
    isIso_restrictGlobalSections_of_connectedness r hr h hConn hSplit F
  let : IsIso ((restrictGlobalSections e.hom).app ((pullbackSheaves (i r)).obj F)) :=
    PhilipponEtaleIteratedFiberSections.isIso_restrictGlobalSections_of_isIso e.hom _
  rw [← restrictGlobalSections_comp (i r) e.hom F]
  infer_instance

end PhilipponHenselianPairSections

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePullbackResolution (restrictGlobalSections)
universe u

theorem solution
    (A B : Type u) [CommRing A] [CommRing B] (r : A →+* B) [HenselianRing A (RingHom.ker r)]
    (hr : Function.Surjective r) {Z : Scheme.{u}} (e : Z ≅ Spec (.of B))
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((restrictGlobalSections (e.hom ≫ Spec.map (CommRingCat.ofHom r))).app F) := by
  apply PhilipponHenselianPairSections.isIso_restrictGlobalSections_of_finite_decomposition
    r AlgebraicGeometry.Scheme.exists_finite_coproduct_strictlyHenselian_of_finite hr (HenselianRing.jac (R := A) (I := RingHom.ker r)) _ e F
  intro P p hp _ x
  let : IsFinite p := hp
  exact PhilipponHenselianPairConnectedness.isConnected_inter_closure HenselianRing.of_isIntegral r hr p x

end

end
