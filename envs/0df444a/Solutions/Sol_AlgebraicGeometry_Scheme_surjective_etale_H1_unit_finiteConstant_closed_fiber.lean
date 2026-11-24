-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.surjective_etale_H1_unit_finiteConstant_closed_fiber
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T05:48:11.814961+00:00
-- url     : https://prove2.me/submissions/620f14a3-33ba-4616-b562-466e7403def0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_AlgebraicGeometry_Scheme_etale_pushforward_preservesFiniteColimits_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_isIso_etale_restrictionBaseChangeOver_of_isProper
import Theorems.Thm_AlgebraicGeometry_Scheme_surjective_etale_H1_unit_constant_closed_fiber_of_isProper

set_option maxHeartbeats 1300000

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

/-- A class of coefficients admits comparison in all degrees if every
object embeds in a coefficient acyclic on both sides, with cokernel
still in the class. -/
theorem comparison_bijective_of_acyclic_embeddings (B : C → Prop)
    (h : ∀ M : C, B M → Function.Bijective (fun a : Q ⟶ M => p ≫ R.map a))
    (emb : ∀ M : C, B M → ∃ (J : C) (i : M ⟶ J), Mono i ∧ B J ∧ B (cokernel i) ∧
      ∀ n : ℕ, Subsingleton (Ext Q J (n + 1)) ∧ Subsingleton (Ext P (R.obj J) (n + 1)))
    (n : ℕ) (M : C) (hM : B M) : Function.Bijective (comparison R p M n) := by
  induction n generalizing M with
  | zero => exact comparison_zero_bijective R p M (h M hM)
  | succ n ih =>
      obtain ⟨J, i, hi, hJ, hQ, hA⟩ := emb M hM
      let _ : Mono i := hi
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      have hSR := hS.map_of_exact R
      constructor
      · apply (AddMonoidHom.ker_eq_bot_iff _).mp
        rw [AddSubgroup.eq_bot_iff_forall]
        intro x hx
        have hx' : comparison R p S.X₁ (n + 1) x = 0 := hx
        obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Q hS x
          ((hA n).1.elim _ _) (n₀ := n) rfl
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
        obtain ⟨y', hy'⟩ := Ext.covariant_sequence_exact₁ P hSR x'
          ((hA n).2.elim _ _) (n₀ := n) rfl
        obtain ⟨y, hy⟩ := (ih S.X₃ hQ).surjective y'
        refine ⟨y.comp hS.extClass rfl, ?_⟩
        rw [comparison_boundary R p hS, hy]
        exact hy'

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

section Square

variable {S T : Scheme.{u}} (i : S ⟶ X) (p₀ : T ⟶ S) (j : T ⟶ Y)

private theorem unit_comp_map_of_mate {A B : Type*} [Category* A] [Category* B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) {F : A} {G : B} (a : F ⟶ R.obj G) :
    adj.unit.app F ≫ R.map ((adj.homEquiv F G).symm a) = a :=
  (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv F G).apply_symm_apply a)

private theorem surjective_unitMap_of_invertible_mate
    (e : pushforward j ⋙ pushforward p ≅ pushforward p₀ ⋙ pushforward i)
    (F : Ab Y) (q : ℕ)
    (hBase : IsIso (((pullbackAdjunction i).homEquiv _ _).symm
      ((pushforward p).map ((pullbackAdjunction j).unit.app F) ≫
        e.hom.app ((pullbackSheaves j).obj F))))
    (hUnit : Function.Surjective (unitMap j F q)) :
    Function.Surjective (unitMap i ((pushforward p).obj F) q) := by
  let R := pushforward p
  let I := pushforward i
  let L := pullbackSheaves j
  let adj := pullbackAdjunction i
  let η := (pullbackAdjunction j).unit.app F
  let ηF := adj.unit.app (R.obj F)
  let d : R.obj F ⟶ I.obj ((pushforward p₀).obj (L.obj F)) := R.map η ≫ e.hom.app (L.obj F)
  let c := (adj.homEquiv _ _).symm d
  let : IsIso c := hBase
  have hc : ηF ≫ I.map c = R.map η ≫ e.hom.app (L.obj F) := unit_comp_map_of_mate adj d
  let k := I.mapIso (asIso c) ≪≫ e.symm.app (L.obj F)
  have hk : ηF ≫ k.hom = R.map η := by
    change ηF ≫ I.map c ≫ e.inv.app (L.obj F) = _
    rw [← Category.assoc, hc, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  intro y
  obtain ⟨z, hz⟩ := (bijective_toDirectImage p _ q).surjective ((H X q).map k.hom y)
  obtain ⟨x, hx⟩ := hUnit z
  refine ⟨toDirectImage p F q x, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso ((H X q).map k.hom)).injective
  calc
    _ = (H X q).map (R.map η) (toDirectImage p F q x) := by
      change ((H X q).map ηF ≫ (H X q).map k.hom) (toDirectImage p F q x) = _
      rw [← (H X q).map_comp, hk]
    _ = toDirectImage p _ q ((H Y q).map η x) := (toDirectImage_naturality p η q x).symm
    _ = _ := by
      rw [show (H Y q).map η x = z from hx]
      exact hz

/-- Surjectivity of the restriction unit passes through exact direct image
when the canonical ordinary base-change map is invertible. -/
theorem surjective_unitMap_of_baseChange (h : IsPullback p₀ j i p) (F : Ab Y) (q : ℕ)
    (hBase : IsIso (restrictionBaseChangeOver i p p₀ j (p₀ ≫ i) rfl h.w.symm F))
    (hUnit : Function.Surjective (unitMap j F q)) :
    Function.Surjective (unitMap i ((pushforward p).obj F) q) := by
  unfold restrictionBaseChangeOver at hBase
  exact surjective_unitMap_of_invertible_mate p i p₀ j _ F q hBase hUnit

end Square

end PhilipponEtaleCohomologyUnits

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] {P Y : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [IsProper r]
    (p : Y ⟶ P) [IsFinite p] (N : ℕ) (hN : N.Prime) :
    Function.Surjective ((Sheaf.functorH P.smallEtaleTopology 1).map
      ((PhilipponEtaleSmallSite.pullbackAdjunction (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) r)).unit.app ((PhilipponEtaleClosedPushforward.pushforward p).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N))))))) := by
  let ρ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let a := pullback.fst ρ r
  let i := pullback.snd ρ r
  let p₀ := pullback.fst i p
  let j := pullback.snd i p
  let h := IsPullback.of_hasPullback i p
  let F := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod N)))
  let : IsProper (p ≫ r) := inferInstance
  let : PreservesFiniteColimits (PhilipponEtaleClosedPushforward.pushforward p) := AlgebraicGeometry.Scheme.etale_pushforward_preservesFiniteColimits_of_isFinite p
  exact PhilipponEtaleCohomologyUnits.surjective_unitMap_of_baseChange p i p₀ j h F 1
    (AlgebraicGeometry.Scheme.isIso_etale_restrictionBaseChangeOver_of_isProper p i p₀ j h F)
    (AlgebraicGeometry.Scheme.surjective_etale_H1_unit_constant_closed_fiber_of_isProper A (p ≫ r) (p₀ ≫ a) j
      (h.paste_horiz (IsPullback.of_hasPullback ρ r)) N hN)

end

end
