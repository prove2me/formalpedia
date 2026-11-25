-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_finite_surjective_effacing_unit_on_closed_fiber
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T00:31:15.728902+00:00
-- url     : https://prove2.me/submissions/c158b4d6-b102-4432-985e-234183a64aa6

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Henselian
import Theorems.Thm_AlgebraicGeometry_Scheme_etale_pushforward_preservesFiniteColimits_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_surjective_effacing_constant_closed_fiber
import Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_finite_directImage_baseChange_of_isClosedImmersion

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponExtComparison

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  {Q : C} {P : D} (p : P ⟶ R.obj Q)

/-- Apply an exact functor to Ext, then precompose with the comparison map. -/
def comparison (M : C) (n : ℕ) : Ext Q M n →+ Ext P (R.obj M) n :=
  ((Ext.mk₀ p).precomp (R.obj M) (zero_add n)).comp (R.mapExtAddHom Q M n)

private theorem comparison_comp {M N : C} {n k m : ℕ} (x : Ext Q M n) (a : Ext M N k)
    (h : n + k = m) :
    comparison R p N m (x.comp a h) =
      (comparison R p M n x).comp (a.mapExactFunctor R) h := by
  change (Ext.mk₀ p).comp ((x.comp a h).mapExactFunctor R) (zero_add m) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ p) (x.mapExactFunctor R) (a.mapExactFunctor R)
    (zero_add n) h (by simpa using h)).symm

theorem comparison_mk₀ {M : C} (x : Q ⟶ M) :
    comparison R p M 0 (Ext.mk₀ x) = Ext.mk₀ (p ≫ R.map x) := by
  change (Ext.mk₀ p).comp ((Ext.mk₀ x).mapExactFunctor R) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

private theorem comparison_boundary {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext Q S.X₃ n) :
    comparison R p S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison R p S.X₃ n x).comp (hS.map_of_exact R).extClass rfl := by
  rw [comparison_comp, Ext.mapExactFunctor_extClass]

theorem comparison_post {M N : C} (a : M ⟶ N) (n : ℕ) (x : Ext Q M n) :
    comparison R p N n (x.comp (Ext.mk₀ a) (add_zero n)) =
      (comparison R p M n x).comp (Ext.mk₀ (R.map a)) (add_zero n) := by
  rw [comparison_comp, Ext.mapExactFunctor_mk₀]

theorem comparison_zero_bijective (M : C)
    (h : Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a)) :
    Function.Bijective (comparison R p M 0) := by
  have hz : (comparison R p M 0 : Ext Q M 0 → Ext P (R.obj M) 0) =
      fun x => Ext.mk₀ (p ≫ R.map (Ext.addEquiv₀ x)) := by
    funext x
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective Q M).surjective x
    rw [show Ext.addEquiv₀ (Ext.mk₀ a) = a from Ext.addEquiv₀.apply_symm_apply a]
    exact comparison_mk₀ R p a
  rw [hz]
  exact (Ext.mk₀_bijective _ _).comp (h.comp Ext.addEquiv₀.bijective)

/-- A class of coefficients admits comparison in all degrees if each class
on either side can be killed by a monomorphism with cokernel in the class. -/
theorem comparison_bijective_of_effacement (B : C → Prop)
    (h : ∀ M : C, B M → Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (left : ∀ M : C, B M → ∀ (n : ℕ) (x : Ext Q M (n + 1)),
      ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
        x.comp (Ext.mk₀ i) (add_zero (n + 1)) = 0)
    (right : ∀ M : C, B M → ∀ (n : ℕ) (x : Ext P (R.obj M) (n + 1)),
      ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
        x.comp (Ext.mk₀ (R.map i)) (add_zero (n + 1)) = 0)
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  induction n generalizing M with
  | zero => exact comparison_zero_bijective R p M (h M hM)
  | succ n ih =>
      constructor
      · apply (AddMonoidHom.ker_eq_bot_iff _).mp
        rw [AddSubgroup.eq_bot_iff_forall]
        intro x hx
        obtain ⟨J, i, hi, hJ, hQ, hkill⟩ := left M hM n x
        let _ : Mono i := hi
        let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
        have hSR := hS.map_of_exact R
        have hx' : comparison R p S.X₁ (n + 1) x = 0 := hx
        obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Q hS x hkill (n₀ := n) rfl
        have hzero : (comparison R p S.X₃ n y).comp hSR.extClass rfl = 0 := by
          rw [← comparison_boundary R p hS n y, hy]
          exact hx'
        obtain ⟨z', hz'⟩ := Ext.covariant_sequence_exact₃ P hSR _ rfl hzero
        obtain ⟨z, hz⟩ := (ih S.X₂ hJ).surjective z'
        have hyz : z.comp (Ext.mk₀ S.g) (add_zero n) = y := (ih S.X₃ hQ).injective (by
          rw [comparison_post, hz]
          exact hz')
        rw [← hy, ← hyz, Ext.comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
      · intro x'
        obtain ⟨J, i, hi, _, hQ, hkill⟩ := right M hM n x'
        let _ : Mono i := hi
        let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
        have hSR := hS.map_of_exact R
        obtain ⟨y', hy'⟩ := Ext.covariant_sequence_exact₁ P hSR x' hkill (n₀ := n) rfl
        obtain ⟨y, hy⟩ := (ih S.X₃ hQ).surjective y'
        refine ⟨y.comp hS.extClass rfl, ?_⟩
        rw [comparison_boundary R p hS, hy]
        exact hy'

/-- Acyclic embeddings give the class-by-class effacement criterion. -/
theorem comparison_bijective_of_acyclic_embeddings (B : C → Prop)
    (h : ∀ M : C, B M → Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (emb : ∀ M : C, B M → ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
      ∀ n : ℕ, Subsingleton (Ext Q J (n + 1)) ∧ Subsingleton (Ext P (R.obj J) (n + 1)))
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  apply comparison_bijective_of_effacement R p B h _ _ n M hM
  · intro M hM q x
    obtain ⟨J, i, hi, hJ, hQ, hA⟩ := emb M hM
    exact ⟨J, i, hi, hJ, hQ, (hA q).1.elim _ _⟩
  · intro M hM q x
    obtain ⟨J, i, hi, hJ, hQ, hA⟩ := emb M hM
    exact ⟨J, i, hi, hJ, hQ, (hA q).2.elim _ _⟩

/-- A Hom comparison extends to all Ext degrees when the exact functor
also preserves injectives. -/
theorem comparison_bijective [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (h : ∀ M : C, Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (n : ℕ) (M : C) : Function.Bijective (comparison R p M n) := by
  refine comparison_bijective_of_acyclic_embeddings R p (fun _ => True) (fun M _ => h M) ?_ n M trivial
  intro A _
  refine ⟨Injective.under A, Injective.ι A, inferInstance, trivial, trivial, fun q => ?_⟩
  let : Injective (R.obj (Injective.under A)) := R.injective_obj_of_injective inferInstance
  exact ⟨⟨fun x y => (Ext.eq_zero_of_injective x).trans (Ext.eq_zero_of_injective y).symm⟩,
    ⟨fun x y => (Ext.eq_zero_of_injective x).trans (Ext.eq_zero_of_injective y).symm⟩⟩

end PhilipponExtComparison

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackComposition (pullbackCompIso pullbackCompIso_over_hom restrictDirectImage)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtalePullbackSquareUnits

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

section Adjunctions

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {L : A ⥤ B} {R : B ⥤ A} {M : A ⥤ C} {S : C ⥤ A}
  {N : C ⥤ D} {T : D ⥤ C} {Q : B ⥤ D} {V : D ⥤ B}
  (a : M ⊣ S) (b : N ⊣ T) (c : L ⊣ R) (d : Q ⊣ V)
  (e : V ⋙ R ≅ T ⋙ S)

private theorem base_change_naturality {F G : B} (g : F ⟶ G) :
    M.map (R.map g) ≫ (a.homEquiv _ _).symm (R.map (d.unit.app G) ≫ e.hom.app (Q.obj G)) =
      (a.homEquiv _ _).symm (R.map (d.unit.app F) ≫ e.hom.app (Q.obj F)) ≫ T.map (Q.map g) := by
  apply (a.homEquiv (R.obj F) (T.obj (Q.obj G))).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Functor.id_obj, Equiv.apply_symm_apply]
  have h : R.map (V.map (Q.map g)) ≫ e.hom.app (Q.obj G) =
    e.hom.app (Q.obj F) ≫ S.map (T.map (Q.map g)) := e.hom.naturality (Q.map g)
  have hUnit : g ≫ d.unit.app G = d.unit.app F ≫ V.map (Q.map g) := d.unit.naturality g
  change R.map g ≫ R.map (d.unit.app G) ≫ e.hom.app (Q.obj G) =
    (R.map (d.unit.app F) ≫ e.hom.app (Q.obj F)) ≫ S.map (T.map (Q.map g))
  rw [Category.assoc, ← h, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, hUnit]

end Adjunctions

section OverComposite

variable {X P Z W : Scheme.{u}} (p : P ⟶ X) (i : Z ⟶ X) (j : W ⟶ P) (r : W ⟶ Z)
    (ρ : W ⟶ X) (hp : j ≫ p = ρ) (hi : r ≫ i = ρ)

/-- Ordinary base change is natural in the coefficients. -/
@[reassoc]
theorem restrictionBaseChangeOver_naturality {B C : Ab Z} (a : B ⟶ C) :
    (pullbackSheaves p).map ((pushforward i).map a) ≫
      restrictionBaseChangeOver p i j r ρ hp hi C =
    restrictionBaseChangeOver p i j r ρ hp hi B ≫
      (pushforward j).map ((pullbackSheaves r).map a) := by
  unfold restrictionBaseChangeOver
  exact base_change_naturality (pullbackAdjunction p) (pullbackAdjunction r) _ a

end OverComposite

end PhilipponEtalePullbackSquareUnits

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleCohomologyUnits

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev H (X : Scheme.{u}) (q : ℕ) := Sheaf.functorH X.smallEtaleTopology q
private abbrev Z := AddCommGrpCat.of (ULift.{u} ℤ)
private abbrev C (X : Scheme.{u}) := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj Z

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The cohomology map of the inverse-image unit. -/
abbrev unitMap (F : Ab X) (q : ℕ) := (H X q).map ((pullbackAdjunction p).unit.app F)

private def directImageConstant : C X ⟶ (pushforward p).obj (C Y) :=
  (pullbackAdjunction p).homEquiv _ _ ((pullbackConstantIso p).hom.app Z)

variable [PreservesFiniteColimits (pushforward p)]

/-- The exact direct-image comparison, in the direction given by applying
pushforward to extensions. -/
def toDirectImage (F : Ab Y) (q : ℕ) : F.H q →+ ((pushforward p).obj F).H q :=
  PhilipponExtComparison.comparison (pushforward p) (directImageConstant p) F q

/-- The direct-image comparison is natural in the coefficients. -/
theorem toDirectImage_naturality {F G : Ab Y} (a : F ⟶ G) (q : ℕ) (x : F.H q) :
    toDirectImage p G q ((H Y q).map a x) =
      (H X q).map ((pushforward p).map a) (toDirectImage p F q x) :=
  PhilipponExtComparison.comparison_post (pushforward p) (directImageConstant p) a q x

/-- Exact direct image preserves cohomology, including the coefficient maps. -/
theorem bijective_toDirectImage (F : Ab Y) (q : ℕ) : Function.Bijective (toDirectImage p F q) := by
  apply PhilipponExtComparison.comparison_bijective
  intro G
  let L := pullbackAdjunction p
  let e := (pullbackConstantIso p).app Z
  let h := L.homEquiv (C X) G
  have hEq : (fun a : C Y ⟶ G => directImageConstant p ≫ (pushforward p).map a) =
      h ∘ fun a : C Y ⟶ G => e.hom ≫ a := by
    funext a
    exact (L.homEquiv_naturality_right e.hom a).symm
  rw [hEq]
  exact h.bijective.comp ((Iso.homCongr e (Iso.refl G)).symm.bijective)

end PhilipponEtaleCohomologyUnits

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleCohomologyUnits (bijective_toDirectImage toDirectImage toDirectImage_naturality unitMap)
open PhilipponEtalePullbackSquareUnits (pulledImageComparisonOver pulledImageComparison_unit
  restrictionBaseChangeOver restrictionBaseChangeOver_naturality)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleCohomologyEffacement

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev constant (X : Scheme.{u}) := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- Direct image of the constant sheaf with coefficient group `M`. -/
abbrev constantDirectImage {X Y : Scheme.{u}} (p : Y ⟶ X) (M : AddCommGrpCat.{u}) : Ab X :=
  (pushforward p).obj ((constant Y).obj M)

set_option maxHeartbeats 1500000 in
/-- A cover killing a class on the closed fiber also kills the corresponding
class of the constant direct image, via ordinary base change. -/
theorem finiteDirectImage_unit_kills_of_baseChange
    {X Z Y Y' W W' : Scheme.{u}} (i : Z ⟶ X) (p : Y ⟶ X) (a : Y' ⟶ Y)
    (p₀ : W ⟶ Z) (j : W ⟶ Y) (a₀ : W' ⟶ W) (j' : W' ⟶ Y')
    (hp : IsPullback p₀ j i p) (ha : IsPullback a₀ j' j a)
    [PreservesFiniteColimits (pushforward p₀)]
    (M : AddCommGrpCat.{u}) (q : ℕ) (x : ((pullbackSheaves i).obj (constantDirectImage p M)).H q)
    (y : ((pullbackSheaves j).obj ((constant Y).obj M)).H q)
    (hy : toDirectImage p₀ _ q y = Sheaf.H.map
      (restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl hp.w.symm ((constant Y).obj M)) q x)
    (hy₀ : unitMap a₀ ((pullbackSheaves j).obj ((constant Y).obj M)) q y = 0)
    (hBaseP : ∀ B, IsIso (restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl hp.w.symm B))
    (hBaseA : IsIso (restrictionBaseChangeOver j a a₀ j' (a₀ ≫ j) rfl ha.w.symm
      ((pullbackSheaves a).obj ((constant Y).obj M)))) :
    Sheaf.H.map ((pullbackSheaves i).map ((pushforward p).map
      ((pullbackAdjunction a).unit.app ((constant Y).obj M)))) q x = 0 := by
  let F := (constant Y).obj M
  let η := (pullbackAdjunction a).unit.app F
  let η₀ := (pullbackAdjunction a₀).unit.app ((pullbackSheaves j).obj F)
  let c := restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl hp.w.symm
  let e := pulledImageComparisonOver j a a₀ j' (a₀ ≫ j) rfl ha.w.symm F
  let g := c _ ≫ (pushforward p₀).map e
  let f := (pullbackSheaves i).map ((pushforward p).map η)
  have hNatural : f ≫ c _ = c F ≫ (pushforward p₀).map ((pullbackSheaves j).map η) :=
    restrictionBaseChangeOver_naturality i p p₀ j (p₀ ≫ i) rfl hp.w.symm η
  have hUnit : (pullbackSheaves j).map η ≫ e = η₀ :=
    pulledImageComparison_unit j a a₀ j' (a₀ ≫ j) rfl ha.w.symm F
  have hSquare : f ≫ g = c F ≫ (pushforward p₀).map η₀ := by
    change f ≫ c _ ≫ (pushforward p₀).map e = _
    rw [← Category.assoc, hNatural, Category.assoc, ← Functor.map_comp, hUnit]
  have hg : IsIso g := by
    let : IsIso (c ((pushforward a).obj ((pullbackSheaves a).obj F))) := hBaseP _
    have he : IsIso e := by
      unfold e pulledImageComparisonOver
      let := hBaseA
      infer_instance
    unfold g
    infer_instance
  change Sheaf.H.map f q x = 0
  apply (ConcreteCategory.bijective_of_isIso
    ((Sheaf.functorH Z.smallEtaleTopology q).map g)).injective
  change Sheaf.H.map g q (Sheaf.H.map f q x) = Sheaf.H.map g q 0
  let d := (pushforward p₀).map η₀
  calc
    _ = Sheaf.H.map (f ≫ g) q x := (Sheaf.H.map_comp_apply f g x).symm
    _ = Sheaf.H.map (c F ≫ d) q x := congrArg (fun m => Sheaf.H.map m q x) hSquare
    _ = Sheaf.H.map d q (Sheaf.H.map (c F) q x) := Sheaf.H.map_comp_apply _ _ _
    _ = Sheaf.H.map d q (toDirectImage p₀ _ q y) :=
      congrArg (fun z => Sheaf.H.map d q z) hy.symm
    _ = toDirectImage p₀ _ q (unitMap a₀ _ q y) := (toDirectImage_naturality p₀ η₀ q y).symm
    _ = 0 := (congrArg (toDirectImage p₀ _ q) hy₀).trans (map_zero _)
    _ = _ := (map_zero (Sheaf.H.map g q)).symm

set_option maxHeartbeats 1500000 in
/-- The finite-cover input for a constant direct image follows from finite
base change, exact direct image, and the finite-cover input for constants. -/
theorem exists_finite_surjective_effacing_unit_of_baseChange
    (hExact : ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p],
      PreservesFiniteColimits (pushforward p))
    (hBase : ∀ {X Y U V : Scheme.{u}} (i : U ⟶ X) [IsClosedImmersion i] (p : Y ⟶ X) [IsFinite p]
      (p₀ : V ⟶ U) (j : V ⟶ Y) (h : IsPullback p₀ j i p) (B : Ab Y),
      IsIso (restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl h.w.symm B))
    (hCover : ∀ {Y W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
      (M : AddCommGrpCat.{u}) (_ : Finite M) (q : ℕ)
      (y : ((pullbackSheaves j).obj ((constant Y).obj M)).H (q + 1)),
      ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y), IsFinite a ∧ Surjective a ∧
        unitMap (pullback.fst j a) ((pullbackSheaves j).obj ((constant Y).obj M)) (q + 1) y = 0)
    {X Z Y : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (p : Y ⟶ X) [IsFinite p] (M : AddCommGrpCat.{u}) (hM : Finite M) (q : ℕ)
    (x : ((pullbackSheaves i).obj (constantDirectImage p M)).H (q + 1)) :
    ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y), IsFinite a ∧ Surjective a ∧
      Sheaf.H.map ((pullbackSheaves i).map ((pushforward p).map
        ((pullbackAdjunction a).unit.app ((constant Y).obj M)))) (q + 1) x = 0 := by
  let p₀ := pullback.fst i p
  let j := pullback.snd i p
  let hp := IsPullback.of_hasPullback i p
  let : IsAffine Y := isAffine_of_isAffineHom p
  let : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (pullback.snd i p))
  let : IsFinite p₀ := inferInstanceAs (IsFinite (pullback.fst i p))
  let : PreservesFiniteColimits (pushforward p₀) := hExact p₀
  obtain ⟨y, hy⟩ := (bijective_toDirectImage p₀ _ (q + 1)).surjective
    (Sheaf.H.map (restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl hp.w.symm ((constant Y).obj M))
      (q + 1) x)
  obtain ⟨Y', a, ha, hs, hz⟩ := hCover j M hM q y
  let : IsFinite a := ha
  let a₀ := pullback.fst j a
  let j' := pullback.snd j a
  let h := IsPullback.of_hasPullback j a
  exact ⟨Y', a, ha, hs, finiteDirectImage_unit_kills_of_baseChange i p a p₀ j a₀ j' hp h
      M (q + 1) x y hy hz (hBase i p p₀ j hp) (hBase j a a₀ j' h _)⟩

end PhilipponEtaleCohomologyEffacement

end

open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {X Z Y : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (p : Y ⟶ X) (hp : IsFinite p) (M : AddCommGrpCat.{u}) (hM : Finite M) (q : ℕ)
    (x : ((pullbackSheaves i).obj ((pushforward p).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M))).H (q + 1)) :
    ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y), IsFinite a ∧ Surjective a ∧
      Sheaf.H.map ((pullbackSheaves i).map ((pushforward p).map ((pullbackAdjunction a).unit.app
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M)))) (q + 1) x = 0 := by
  let : IsFinite p := hp
  exact PhilipponEtaleCohomologyEffacement.exists_finite_surjective_effacing_unit_of_baseChange
    (fun p => AlgebraicGeometry.Scheme.etale_pushforward_preservesFiniteColimits_of_isFinite p)
    (by
      intro _ _ _ _ i _ p _ p₀ j h B
      exact AlgebraicGeometry.Scheme.isIso_etale_finite_directImage_baseChange_of_isClosedImmersion i p p₀ j h B)
    (by
      intro _ _ _ j _ M hM q x
      exact AlgebraicGeometry.Scheme.exists_finite_surjective_effacing_constant_closed_fiber j M hM q x) i p M hM q x

end
