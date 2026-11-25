-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineStageSystems
-- name    : AlgebraicGeometry_EtaleAffineStageSystems
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T04:51:31.313839+00:00
-- url     : https://prove2.me/theorems/6da16759-1061-4e1f-87f0-7951798b734e
-- title:
--   Compatible abelian étale sheaves and the total site of an affine diagram
-- statement:
--   The objects of the total site are étale charts over individual stages. A compatible system gives a section presheaf on this site, and its stage maps determine natural maps into a sheaf on the inverse-limit scheme.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleModeledCech
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.WithTerminal.Basic

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
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponCompatibleInjectiveSystems

universe u v w

variable {I : Type u} [Category.{u} I]
  (C : I → Type v) [∀ i, Category.{w} (C i)]

/-- The unit and composition isomorphisms of direct images used to form
compatible coefficient systems over an inverse diagram. -/
structure DirectImages where
  functor {i j : I} : (i ⟶ j) → C i ⥤ C j
  identity (i : I) : functor (𝟙 i) ≅ 𝟭 (C i)
  composition {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    functor (a ≫ b) ≅ functor a ⋙ functor b
  comp_identity {i j : I} (a : i ⟶ j) (A : C i) :
    (composition a (𝟙 j)).hom.app A ≫ (identity j).hom.app ((functor a).obj A) =
      eqToHom (congrArg (fun d => (functor d).obj A) (Category.comp_id a))
  comp_assoc {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l) (A : C i) :
    (composition (a ≫ b) c).hom.app A ≫ (functor c).map ((composition a b).hom.app A) =
      eqToHom (congrArg (fun d => (functor d).obj A) (Category.assoc a b c)) ≫
        (composition a (b ≫ c)).hom.app A ≫ (composition b c).hom.app ((functor a).obj A)

variable {C} (R : DirectImages C)

/-- A family with transition maps into the direct images at earlier stages. -/
structure System where
  obj (i : I) : C i
  map {i j : I} (a : i ⟶ j) : obj j ⟶ (R.functor a).obj (obj i)
  map_identity (i : I) : map (𝟙 i) ≫ (R.identity i).hom.app (obj i) = 𝟙 (obj i)
  map_composition {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    map (a ≫ b) ≫ (R.composition a b).hom.app (obj i) =
      map b ≫ (R.functor b).map (map a)

variable [∀ i, HasProducts.{u} (C i)]

private abbrev Incoming (i : I) := Σ k, k ⟶ i

private abbrev factors (M : ∀ i, C i) (i : I) (a : Incoming i) :=
  (R.functor a.2).obj (M a.1)

private abbrev stage (M : ∀ i, C i) (i : I) := ∏ᶜ factors R M i

private abbrev proj (M : ∀ i, C i) {i k : I} (a : k ⟶ i) :
    stage R M i ⟶ (R.functor a).obj (M k) := Pi.π (factors R M i) ⟨k, a⟩

@[reassoc]
private theorem proj_congr (M : ∀ i, C i) {i k : I} {a b : k ⟶ i} (h : a = b) :
    proj R M a ≫ eqToHom (congrArg (fun d => (R.functor d).obj (M k)) h) = proj R M b := by
  subst b
  simp

private def transitionFan (M : ∀ i, C i) {i j : I} (b : i ⟶ j) :
    Fan (fun a : Incoming i => (R.functor b).obj (factors R M i a)) :=
  Fan.mk (stage R M j) (fun a => proj R M (a.2 ≫ b) ≫ (R.composition a.2 b).hom.app (M a.1))

variable [∀ {i j : I} (a : i ⟶ j), PreservesLimitsOfSize.{u, u} (R.functor a)]

private def mappedProduct (M : ∀ i, C i) {i j : I} (b : i ⟶ j) :
    IsLimit (Fan.mk ((R.functor b).obj (stage R M i))
      (fun a : Incoming i => (R.functor b).map (proj R M a.2))) :=
  isLimitFanMkObjOfIsLimit (R.functor b) (factors R M i) _ (productIsProduct (factors R M i))

private def transition (M : ∀ i, C i) {i j : I} (b : i ⟶ j) :
    stage R M j ⟶ (R.functor b).obj (stage R M i) :=
  (mappedProduct R M b).lift (transitionFan R M b)

@[reassoc]
private theorem transition_proj (M : ∀ i, C i) {i j k : I} (a : k ⟶ i) (b : i ⟶ j) :
    transition R M b ≫ (R.functor b).map (proj R M a) =
      proj R M (a ≫ b) ≫ (R.composition a b).hom.app (M k) :=
  (mappedProduct R M b).fac (transitionFan R M b) ⟨⟨k, a⟩⟩

private theorem transition_identity (M : ∀ i, C i) (i : I) :
    transition R M (𝟙 i) ≫ (R.identity i).hom.app (stage R M i) = 𝟙 _ := by
  apply Pi.hom_ext
  rintro ⟨k, a⟩
  change (transition R M (𝟙 i) ≫ (R.identity i).hom.app (stage R M i)) ≫ proj R M a =
    𝟙 _ ≫ proj R M a
  rw [Category.id_comp, Category.assoc]
  have hNat : (R.functor (𝟙 i)).map (proj R M a) ≫
      (R.identity i).hom.app ((R.functor a).obj (M k)) =
    (R.identity i).hom.app (stage R M i) ≫ proj R M a :=
    (R.identity i).hom.naturality (proj R M a)
  rw [← hNat, transition_proj_assoc, R.comp_identity, proj_congr R M (Category.comp_id a)]

private theorem transition_composition (M : ∀ i, C i) {i j k : I} (b : i ⟶ j) (c : j ⟶ k) :
    transition R M (b ≫ c) ≫ (R.composition b c).hom.app (stage R M i) =
      transition R M c ≫ (R.functor c).map (transition R M b) := by
  have hProduct : IsLimit (Fan.mk ((R.functor c).obj ((R.functor b).obj (stage R M i)))
      (fun a : Incoming i => (R.functor c).map ((R.functor b).map (proj R M a.2)))) :=
    isLimitFanMkObjOfIsLimit (R.functor b ⋙ R.functor c) (factors R M i) _
      (productIsProduct (factors R M i))
  apply Fan.IsLimit.hom_ext hProduct
  rintro ⟨l, a⟩
  change (transition R M (b ≫ c) ≫ (R.composition b c).hom.app (stage R M i)) ≫
        (R.functor c).map ((R.functor b).map (proj R M a)) =
    (transition R M c ≫ (R.functor c).map (transition R M b)) ≫
        (R.functor c).map ((R.functor b).map (proj R M a))
  have hNat : (R.functor (b ≫ c)).map (proj R M a) ≫
      (R.composition b c).hom.app ((R.functor a).obj (M l)) =
      (R.composition b c).hom.app (stage R M i) ≫
        (R.functor c).map ((R.functor b).map (proj R M a)) :=
    (R.composition b c).hom.naturality (proj R M a)
  rw [Category.assoc, ← hNat, transition_proj_assoc, Category.assoc, ← Functor.map_comp,
    transition_proj, Functor.map_comp, transition_proj_assoc]
  symm
  calc
    _ = proj R M ((a ≫ b) ≫ c) ≫
        (eqToHom (congrArg (fun d => (R.functor d).obj (M l)) (Category.assoc a b c)) ≫
          (R.composition a (b ≫ c)).hom.app (M l) ≫
          (R.composition b c).hom.app ((R.functor a).obj (M l))) :=
      congrArg (fun d => proj R M ((a ≫ b) ≫ c) ≫ d) (R.comp_assoc a b c (M l))
    _ = _ := proj_congr_assoc R M (Category.assoc a b c) _

/-- At each stage take the product of the direct images of objects at
stages mapping to it. -/
def productSystem (M : ∀ i, C i) : System R where
  obj := stage R M
  map := transition R M
  map_identity := transition_identity R M
  map_composition := transition_composition R M

private def embed (F : System R) (M : ∀ i, C i) (m : ∀ i, F.obj i ⟶ M i) (i : I) :
    F.obj i ⟶ stage R M i :=
  Pi.lift (fun a : Incoming i => F.map a.2 ≫ (R.functor a.2).map (m a.1))

omit [∀ {i j : I} (a : i ⟶ j), PreservesLimitsOfSize.{u, u} (R.functor a)] in
@[reassoc]
private theorem embed_proj (F : System R) (M : ∀ i, C i) (m : ∀ i, F.obj i ⟶ M i)
    {i k : I} (a : k ⟶ i) :
    embed R F M m i ≫ proj R M a = F.map a ≫ (R.functor a).map (m k) :=
  Pi.lift_π (fun a : Incoming i => F.map a.2 ≫ (R.functor a.2).map (m a.1)) ⟨k, a⟩

private theorem embed_compatible (F : System R) (M : ∀ i, C i) (m : ∀ i, F.obj i ⟶ M i)
    {i j : I} (b : i ⟶ j) :
    embed R F M m j ≫ (productSystem R M).map b =
      F.map b ≫ (R.functor b).map (embed R F M m i) := by
  apply Fan.IsLimit.hom_ext (mappedProduct R M b)
  rintro ⟨k, a⟩
  change (embed R F M m j ≫ transition R M b) ≫ (R.functor b).map (proj R M a) =
    (F.map b ≫ (R.functor b).map (embed R F M m i)) ≫ (R.functor b).map (proj R M a)
  have hNat : (R.functor (a ≫ b)).map (m k) ≫ (R.composition a b).hom.app (M k) =
      (R.composition a b).hom.app (F.obj k) ≫ (R.functor b).map ((R.functor a).map (m k)) :=
    (R.composition a b).hom.naturality (m k)
  rw [Category.assoc, transition_proj, embed_proj_assoc, hNat, ← Category.assoc, F.map_composition]
  simpa only [Category.assoc, ← (R.functor b).map_comp] using
    congrArg (fun f => F.map b ≫ (R.functor b).map f) (embed_proj R F M m a).symm

omit [∀ {i j : I} (a : i ⟶ j), PreservesLimitsOfSize.{u, u} (R.functor a)] in
private theorem mono_embed (F : System R) (M : ∀ i, C i) (m : ∀ i, F.obj i ⟶ M i)
    (hm : ∀ i, Mono (m i)) (i : I) : Mono (embed R F M m i) := by
  let : Mono (m i) := hm i
  have h : embed R F M m i ≫ proj R M (𝟙 i) ≫ (R.identity i).hom.app (M i) = m i := by
    have hNat : (R.functor (𝟙 i)).map (m i) ≫ (R.identity i).hom.app (M i) =
        (R.identity i).hom.app (F.obj i) ≫ m i :=
      (R.identity i).hom.naturality (m i)
    rw [embed_proj_assoc, hNat, ← Category.assoc, F.map_identity, Category.id_comp]
  constructor
  intro Z a b he
  apply (cancel_mono (m i)).mp
  simpa only [Category.assoc, h] using congrArg
    (fun t => t ≫ proj R M (𝟙 i) ≫ (R.identity i).hom.app (M i)) he

variable [∀ i, EnoughInjectives (C i)]
  [∀ {i j : I} (a : i ⟶ j), (R.functor a).PreservesInjectiveObjects]

/-- Every compatible system embeds into a compatible system of injective
objects. The identity-indexed factor detects monicity of each embedding. -/
theorem exists_injective_extension (F : System R) :
    ∃ (G : System R) (m : ∀ i, F.obj i ⟶ G.obj i),
      (∀ i, Mono (m i) ∧ Injective (G.obj i)) ∧
      ∀ {i j : I} (a : i ⟶ j), m j ≫ G.map a = F.map a ≫ (R.functor a).map (m i) := by
  let M i := Injective.under (F.obj i)
  let m i := Injective.ι (F.obj i)
  refine ⟨productSystem R M, embed R F M m, fun i => ⟨mono_embed R F M m (fun _ => inferInstance) i, ?_⟩,
    fun a => embed_compatible R F M m a⟩
  let (a : Incoming i) : Injective (factors R M i a) :=
    (R.functor a.2).injective_obj_of_injective inferInstance
  change Injective (∏ᶜ factors R M i)
  refine ⟨fun {X Y} g f _ => ?_⟩
  refine ⟨Pi.lift (fun a => Injective.factorThru (g ≫ Pi.π _ a) f), ?_⟩
  apply Pi.hom_ext
  intro a
  rw [Category.assoc, Pi.lift_π, Injective.comp_factorThru]

end PhilipponCompatibleInjectiveSystems

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems
open PhilipponEtaleBaseChangeComparison (baseChange baseChange_isContinuous map_isPullback)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction)


namespace PhilipponEtaleDirectImageSystem

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

abbrev chart {i j : I} (a : i ⟶ j) := baseChange (D.map a)

abbrev fst {i j : I} (a : i ⟶ j) (U : (D.obj j).Etale) :
    ((chart D a).obj U).left ⟶ U.left := pullback.fst U.hom (D.map a)

theorem fst_ext {i j : I} (a : i ⟶ j) (U : (D.obj j).Etale)
    {V : (D.obj i).Etale} {g h : V ⟶ (chart D a).obj U}
    (e : g.left ≫ fst D a U = h.left ≫ fst D a U) : g = h :=
  MorphismProperty.Over.Hom.ext (pullback.hom_ext e
    ((MorphismProperty.Over.w g).trans (MorphismProperty.Over.w h).symm))

@[reassoc]
theorem map_fst {i j : I} (a : i ⟶ j) {U V : (D.obj j).Etale} (s : U ⟶ V) :
    ((chart D a).map s).left ≫ fst D a V = fst D a U ≫ s.left :=
  (map_isPullback (D.map a) s).w.symm

def unitChart (i : I) : chart D (𝟙 i) ≅ 𝟭 ((D.obj i).Etale) := by
  refine NatIso.ofComponents (fun U => ?_) (fun s => ?_)
  · have hi : IsIso (D.map (𝟙 i)) := by rw [D.map_id]; infer_instance
    let e := asIso (fst D (𝟙 i) U)
    refine MorphismProperty.Over.isoMk e ?_
    change fst D (𝟙 i) U ≫ U.hom = pullback.snd U.hom (D.map (𝟙 i))
    exact pullback.condition.trans
      ((congrArg (fun z => pullback.snd U.hom (D.map (𝟙 i)) ≫ z) (D.map_id i)).trans
        (Category.comp_id _))
  · apply MorphismProperty.Over.Hom.ext
    exact map_fst D (𝟙 i) s

@[reassoc]
theorem unitChart_inv_fst (i : I) (U : (D.obj i).Etale) :
    ((unitChart D i).inv.app U).left ≫ fst D (𝟙 i) U = 𝟙 U.left :=
  congrArg (fun s => s.left) ((unitChart D i).app U).inv_hom_id

def flatten {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    chart D b ⋙ chart D a ≅ chart D (a ≫ b) :=
  (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)).symm

@[reassoc]
theorem flatten_fst {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (U : (D.obj k).Etale) :
    ((flatten D a b).hom.app U).left ≫ fst D (a ≫ b) U =
      fst D a ((chart D b).obj U) ≫ fst D b U := by
  change ((pullback.congrHom rfl (D.map_comp a b) ≪≫
    (pullbackLeftPullbackSndIso U.hom (D.map b) (D.map a)).symm).inv) ≫ _ = _
  simp
  rfl

abbrev castChart {i j : I} {a b : i ⟶ j} (h : a = b) (U : (D.obj j).Etale) :
    (chart D a).obj U ⟶ (chart D b).obj U :=
  eqToHom (congrArg (fun d => (chart D d).obj U) h)

@[reassoc]
theorem castChart_fst {i j : I} {a b : i ⟶ j} (h : a = b) (U : (D.obj j).Etale) :
    (castChart D h U).left ≫ fst D b U = fst D a U := by
  subst b
  change 𝟙 _ ≫ fst D a U = fst D a U
  exact Category.id_comp _

private theorem chart_comp_identity {i j : I} (a : i ⟶ j) (U : (D.obj j).Etale) :
    (chart D a).map ((unitChart D j).inv.app U) ≫ (flatten D a (𝟙 j)).hom.app U =
      castChart D (Category.comp_id a).symm U := by
  apply fst_ext D (a ≫ 𝟙 j) U
  change ((chart D a).map ((unitChart D j).inv.app U)).left ≫
      ((flatten D a (𝟙 j)).hom.app U).left ≫ fst D (a ≫ 𝟙 j) U =
    (castChart D (Category.comp_id a).symm U).left ≫ fst D (a ≫ 𝟙 j) U
  rw [flatten_fst, map_fst_assoc, unitChart_inv_fst, castChart_fst]
  exact Category.comp_id _

private theorem chart_identity_comp {i j : I} (a : i ⟶ j) (U : (D.obj j).Etale) :
    (unitChart D i).inv.app ((chart D a).obj U) ≫ (flatten D (𝟙 i) a).hom.app U =
      castChart D (Category.id_comp a).symm U := by
  apply fst_ext D (𝟙 i ≫ a) U
  change ((unitChart D i).inv.app ((chart D a).obj U)).left ≫
      ((flatten D (𝟙 i) a).hom.app U).left ≫ fst D (𝟙 i ≫ a) U =
    (castChart D (Category.id_comp a).symm U).left ≫ fst D (𝟙 i ≫ a) U
  rw [flatten_fst, unitChart_inv_fst_assoc, castChart_fst]

private theorem chart_comp_assoc {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l)
    (U : (D.obj l).Etale) :
    (flatten D a b).hom.app ((chart D c).obj U) ≫ (flatten D (a ≫ b) c).hom.app U =
      (chart D a).map ((flatten D b c).hom.app U) ≫ (flatten D a (b ≫ c)).hom.app U ≫
        castChart D (Category.assoc a b c).symm U := by
  apply fst_ext D ((a ≫ b) ≫ c) U
  change (((flatten D a b).hom.app ((chart D c).obj U)).left ≫
      ((flatten D (a ≫ b) c).hom.app U).left) ≫ fst D ((a ≫ b) ≫ c) U =
    (((chart D a).map ((flatten D b c).hom.app U)).left ≫
      ((flatten D a (b ≫ c)).hom.app U).left ≫
      (castChart D (Category.assoc a b c).symm U).left) ≫ fst D ((a ≫ b) ≫ c) U
  simp only [Category.assoc, castChart_fst, flatten_fst, flatten_fst_assoc, map_fst_assoc,
    Functor.comp_obj]

private def unitDirectImage (i : I) : pushforward (D.map (𝟙 i)) ≅ 𝟭 (Ab (D.obj i)) :=
  Functor.sheafPushforwardContinuousId' (unitChart D i) AddCommGrpCat.{u} _

private def splitDirectImage {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    pushforward (D.map (a ≫ b)) ≅ pushforward (D.map a) ⋙ pushforward (D.map b) :=
  (Functor.sheafPushforwardContinuousComp' (flatten D a b) AddCommGrpCat.{u}
    (D.obj k).smallEtaleTopology (D.obj j).smallEtaleTopology (D.obj i).smallEtaleTopology).symm

theorem castDirectImage_app {i j : I} {a b : i ⟶ j} (h : a = b)
    (A : Ab (D.obj i)) (U : (D.obj j).Etale) :
    (eqToHom (congrArg (fun d => (pushforward (D.map d)).obj A) h)).hom.app (op U) =
      A.obj.map (castChart D h.symm U).op := by
  subst b
  simp
  rfl

set_option maxHeartbeats 900000 in
private theorem directImage_comp_identity {i j : I} (a : i ⟶ j) (A : Ab (D.obj i)) :
    (splitDirectImage D a (𝟙 j)).hom.app A ≫
        (unitDirectImage D j).hom.app ((pushforward (D.map a)).obj A) =
      eqToHom (congrArg (fun d => (pushforward (D.map d)).obj A) (Category.comp_id a)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  let U := T.unop
  change A.obj.map ((flatten D a (𝟙 j)).hom.app U).op ≫
    A.obj.map ((chart D a).map ((unitChart D j).inv.app U)).op = _
  have h := castDirectImage_app D (Category.comp_id a) A U
  rw [← Functor.map_comp, ← op_comp, chart_comp_identity, h]

set_option maxHeartbeats 900000 in
private theorem directImage_comp_assoc {i j k l : I} (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l)
    (A : Ab (D.obj i)) :
    (splitDirectImage D (a ≫ b) c).hom.app A ≫
        (pushforward (D.map c)).map ((splitDirectImage D a b).hom.app A) =
      eqToHom (congrArg (fun d => (pushforward (D.map d)).obj A) (Category.assoc a b c)) ≫
        (splitDirectImage D a (b ≫ c)).hom.app A ≫
        (splitDirectImage D b c).hom.app ((pushforward (D.map a)).obj A) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  let U := T.unop
  change A.obj.map ((flatten D (a ≫ b) c).hom.app U).op ≫
    A.obj.map ((flatten D a b).hom.app ((chart D c).obj U)).op =
    (eqToHom (congrArg (fun d => (pushforward (D.map d)).obj A) (Category.assoc a b c))).hom.app T ≫
      A.obj.map ((flatten D a (b ≫ c)).hom.app U).op ≫
      A.obj.map ((chart D a).map ((flatten D b c).hom.app U)).op
  have h := castDirectImage_app D (Category.assoc a b c) A U
  change _ = (eqToHom (congrArg (fun d => (pushforward (D.map d)).obj A)
    (Category.assoc a b c))).hom.app (op U) ≫ _ ≫ _
  rw [h, ← Functor.map_comp, ← op_comp, chart_comp_assoc, op_comp, op_comp]
  let x := (castChart D (Category.assoc a b c).symm U).op
  let y := ((flatten D a (b ≫ c)).hom.app U).op
  let z := ((chart D a).map ((flatten D b c).hom.app U)).op
  exact ((A.obj.map_comp (x ≫ y) z).trans
    (congrArg (fun m => m ≫ A.obj.map z) (A.obj.map_comp x y))).trans (Category.assoc _ _ _)

/-- Étale direct images of an inverse diagram, including their coherence. -/
def directImages : DirectImages (fun i => Ab (D.obj i)) where
  functor a := pushforward (D.map a)
  identity := unitDirectImage D
  composition := splitDirectImage D
  comp_identity := directImage_comp_identity D
  comp_assoc := directImage_comp_assoc D

/-- The direct-image composition comparison also satisfies the left unit law. -/
theorem directImages_identity_comp {i j : I} (a : i ⟶ j) (A : Ab (D.obj i)) :
    ((directImages D).composition (𝟙 i) a).hom.app A ≫
        ((directImages D).functor a).map (((directImages D).identity i).hom.app A) =
      eqToHom (congrArg (fun d => ((directImages D).functor d).obj A) (Category.id_comp a)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  let U := T.unop
  change A.obj.map ((flatten D (𝟙 i) a).hom.app U).op ≫
    A.obj.map ((unitChart D i).inv.app ((chart D a).obj U)).op = _
  have h := castDirectImage_app D (Category.id_comp a) A U
  rw [← Functor.map_comp, ← op_comp, chart_identity_comp, h]

instance directImages_preservesLimits {i j : I} (a : i ⟶ j) :
    PreservesLimitsOfSize.{u, u} ((directImages D).functor a) :=
  (pullbackAdjunction (D.map a)).rightAdjoint_preservesLimits

instance directImages_preservesInjectives {i j : I} (a : i ⟶ j) :
    ((directImages D).functor a).PreservesInjectiveObjects :=
  inferInstanceAs ((pushforward (D.map a)).PreservesInjectiveObjects)

instance directImages_preservesZero {i j : I} (a : i ⟶ j) :
    ((directImages D).functor a).PreservesZeroMorphisms :=
  inferInstanceAs ((pushforward (D.map a)).PreservesZeroMorphisms)

/-- A compatible diagram of étale abelian sheaves has a compatible
stagewise injective embedding. -/
theorem exists_injective_extension (F : System (directImages D)) :
    ∃ (G : System (directImages D)) (m : ∀ i, F.obj i ⟶ G.obj i),
      (∀ i, Mono (m i) ∧ Injective (G.obj i)) ∧
      ∀ {i j : I} (a : i ⟶ j), m j ≫ G.map a = F.map a ≫ (pushforward (D.map a)).map (m i) :=
  PhilipponCompatibleInjectiveSystems.exists_injective_extension (directImages D) F

end PhilipponEtaleDirectImageSystem

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleDirectImageSystem (chart fst fst_ext map_fst_assoc unitChart
  unitChart_inv_fst_assoc flatten flatten_fst_assoc castChart castChart_fst)


namespace PhilipponEtaleStageCharts

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) {i : I}

/-- An étale chart of the fixed stage viewed at a stage mapping to it. -/
abbrev model (U : (D.obj i).Etale) (a : Over i) :=
  (chart D a.hom).obj U

/-- The base changes at two related stages identify via the iterated
pullback of the same original chart. -/
def transition (U : (D.obj i).Etale) {a b : Over i} (f : a ⟶ b) :
    model D U a ⟶ (chart D f.left).obj (model D U b) :=
  castChart D (Over.w f).symm U ≫ (flatten D f.left b.hom).inv.app U

@[reassoc]
theorem transition_proj (U : (D.obj i).Etale) {a b : Over i} (f : a ⟶ b) :
    (transition D U f).left ≫ fst D f.left (model D U b) ≫ fst D b.hom U = fst D a.hom U := by
  let e := (flatten D f.left b.hom).app U
  have hh : e.inv.left ≫ fst D f.left (model D U b) ≫ fst D b.hom U =
      fst D (f.left ≫ b.hom) U := by
    calc
      _ = e.inv.left ≫ e.hom.left ≫ fst D (f.left ≫ b.hom) U := by
        exact congrArg (fun m => e.inv.left ≫ m)
          (PhilipponEtaleDirectImageSystem.flatten_fst D f.left b.hom U).symm
      _ = _ := by
        have hid : e.inv.left ≫ e.hom.left = 𝟙 _ :=
          congrArg (fun g => g.left) e.inv_hom_id
        rw [← Category.assoc, hid, Category.id_comp]
  change ((castChart D (Over.w f).symm U).left ≫ e.inv.left) ≫ _ ≫ _ = _
  rw [Category.assoc, hh, castChart_fst]

private theorem nested_ext {j k l : I} (a : j ⟶ k) (b : k ⟶ l) (U : (D.obj l).Etale)
    {V : (D.obj j).Etale} {f g : V ⟶ (chart D a).obj ((chart D b).obj U)}
    (h : f.left ≫ fst D a ((chart D b).obj U) ≫ fst D b U =
      g.left ≫ fst D a ((chart D b).obj U) ≫ fst D b U) : f = g := by
  apply (cancel_mono ((flatten D a b).hom.app U)).mp
  apply fst_ext D (a ≫ b) U
  change (f.left ≫ ((flatten D a b).hom.app U).left) ≫ fst D (a ≫ b) U =
    (g.left ≫ ((flatten D a b).hom.app U).left) ≫ fst D (a ≫ b) U
  simpa only [Category.assoc, PhilipponEtaleDirectImageSystem.flatten_fst] using h

theorem transition_id (U : (D.obj i).Etale) (a : Over i) :
    transition D U (𝟙 a) = (unitChart D a.left).inv.app (model D U a) := by
  apply nested_ext D (𝟙 a.left) a.hom U
  exact (transition_proj D U (𝟙 a)).trans
    (unitChart_inv_fst_assoc D a.left (model D U a) (fst D a.hom U)).symm

theorem transition_comp (U : (D.obj i).Etale) {a b c : Over i} (f : a ⟶ b) (g : b ⟶ c) :
    transition D U (f ≫ g) =
      transition D U f ≫ (chart D f.left).map (transition D U g) ≫
        (flatten D f.left g.left).hom.app (model D U c) := by
  apply nested_ext D (f.left ≫ g.left) c.hom U
  change (transition D U (f ≫ g)).left ≫ fst D (f.left ≫ g.left) (model D U c) ≫ fst D c.hom U =
    (transition D U f).left ≫ ((chart D f.left).map (transition D U g)).left ≫
      ((flatten D f.left g.left).hom.app (model D U c)).left ≫
        fst D (f.left ≫ g.left) (model D U c) ≫ fst D c.hom U
  rw [show (transition D U (f ≫ g)).left ≫ fst D (f.left ≫ g.left) (model D U c) ≫
      fst D c.hom U = fst D a.hom U from transition_proj D U (f ≫ g),
    flatten_fst_assoc, map_fst_assoc, transition_proj, transition_proj]

theorem transition_naturality {U V : (D.obj i).Etale} (s : U ⟶ V)
    {a b : Over i} (f : a ⟶ b) :
    (chart D a.hom).map s ≫ transition D V f =
      transition D U f ≫ (chart D f.left).map ((chart D b.hom).map s) := by
  apply nested_ext D f.left b.hom V
  change (((chart D a.hom).map s).left ≫ (transition D V f).left) ≫
      fst D f.left (model D V b) ≫ fst D b.hom V =
    ((transition D U f).left ≫ ((chart D f.left).map ((chart D b.hom).map s)).left) ≫
      fst D f.left (model D V b) ≫ fst D b.hom V
  simp only [Category.assoc, transition_proj, map_fst_assoc, transition_proj_assoc,
    PhilipponEtaleDirectImageSystem.map_fst]

end PhilipponEtaleStageCharts

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems
open PhilipponEtaleDirectImageSystem (chart unitChart flatten directImages)
open PhilipponEtaleStageCharts (model transition transition_id transition_comp transition_naturality)


namespace PhilipponEtaleStageSectionDiagram

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  (F : System (directImages D))

private abbrev coeff {i : I} (U : (D.obj i).Etale) := (F.obj i).obj.obj (op U)

/-- Evaluate the coefficient transition on a chart and its base change. -/
abbrev eval {i j : I} (a : i ⟶ j) (U : (D.obj j).Etale) :
    coeff D F U ⟶ coeff D F ((chart D a).obj U) :=
  (F.map a).hom.app (op U)

theorem eval_id (i : I) (U : (D.obj i).Etale) :
    eval D F (𝟙 i) U ≫ (F.obj i).obj.map ((unitChart D i).inv.app U).op = 𝟙 (coeff D F U) :=
  congrArg (fun f : F.obj i ⟶ F.obj i => f.hom.app (op U)) (F.map_identity i)

@[reassoc]
theorem eval_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (U : (D.obj k).Etale) :
    eval D F (a ≫ b) U ≫ (F.obj i).obj.map ((flatten D a b).hom.app U).op =
      eval D F b U ≫ eval D F a ((chart D b).obj U) :=
  congrArg (fun f => f.hom.app (op U)) (F.map_composition a b)

@[reassoc]
theorem eval_naturality {i j : I} (a : i ⟶ j) {U V : (D.obj j).Etale} (f : U ⟶ V) :
    (F.obj j).obj.map f.op ≫ eval D F a U =
      eval D F a V ≫ (F.obj i).obj.map ((chart D a).map f).op :=
  (F.map a).hom.naturality f.op

variable {i : I}

private abbrev atStage (U : (D.obj i).Etale) (a : Over i) :=
  coeff D F (model D U a)

private def mapSections (U : (D.obj i).Etale) {a b : Over i} (f : a ⟶ b) :
    atStage D F U b ⟶ atStage D F U a :=
  eval D F f.left (model D U b) ≫ (F.obj a.left).obj.map (transition D U f).op

private theorem mapSections_id (U : (D.obj i).Etale) (a : Over i) :
    mapSections D F U (𝟙 a) = 𝟙 (atStage D F U a) := by
  change eval D F (𝟙 a.left) (model D U a) ≫
    (F.obj a.left).obj.map (transition D U (𝟙 a)).op = _
  rw [transition_id D U a, eval_id]

private theorem mapSections_comp (U : (D.obj i).Etale) {a b c : Over i} (f : a ⟶ b) (g : b ⟶ c) :
    mapSections D F U (f ≫ g) = mapSections D F U g ≫ mapSections D F U f := by
  change eval D F (f.left ≫ g.left) (model D U c) ≫
    (F.obj a.left).obj.map (transition D U (f ≫ g)).op = _
  rw [transition_comp D U f g, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, eval_comp_assoc, mapSections, eval_naturality_assoc]

/-- The diagram of sections of a compatible family on the base changes of
a fixed stage chart. -/
def stageSections (U : (D.obj i).Etale) : (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj a := atStage D F U a.unop
  map f := mapSections D F U f.unop
  map_id a := mapSections_id D F U a.unop
  map_comp f g := mapSections_comp D F U g.unop f.unop

private theorem mapSections_naturality {U V : (D.obj i).Etale} (s : U ⟶ V)
    {a b : Over i} (f : a ⟶ b) :
    mapSections D F V f ≫ (F.obj a.left).obj.map ((chart D a.hom).map s).op =
      (F.obj b.left).obj.map ((chart D b.hom).map s).op ≫ mapSections D F U f := by
  dsimp only [mapSections]
  rw [eval_naturality_assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    ← op_comp, ← op_comp, transition_naturality]

private def stageSectionsMap {U V : (D.obj i).Etale} (s : U ⟶ V) :
    stageSections D F V ⟶ stageSections D F U where
  app a := (F.obj a.unop.left).obj.map ((chart D a.unop.hom).map s).op
  naturality {_ _} f := mapSections_naturality D F s f.unop

/-- The section diagram depends functorially on the chart at the chosen stage. -/
def sectionsFunctor (i : I) : (D.obj i).Etaleᵒᵖ ⥤ (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := stageSections D F U.unop
  map s := stageSectionsMap D F s.unop
  map_id U := by
    apply NatTrans.ext
    funext a
    change (F.obj a.unop.left).obj.map ((chart D a.unop.hom).map (𝟙 U.unop)).op = 𝟙 _
    rw [(chart D a.unop.hom).map_id, op_id]
    exact (F.obj a.unop.left).obj.map_id _
  map_comp s t := by
    apply NatTrans.ext
    funext a
    change (F.obj a.unop.left).obj.map ((chart D a.unop.hom).map (t.unop ≫ s.unop)).op =
      (F.obj a.unop.left).obj.map ((chart D a.unop.hom).map s.unop).op ≫
        (F.obj a.unop.left).obj.map ((chart D a.unop.hom).map t.unop).op
    rw [(chart D a.unop.hom).map_comp, op_comp, (F.obj a.unop.left).obj.map_comp]

end PhilipponEtaleStageSectionDiagram

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)


namespace PhilipponEtaleTotalStageSite

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})

/-- An étale chart together with the stage on which it is specified. -/
structure StageChart where
  index : I
  etale : (D.obj index).Etale

variable {D}

/-- A map of stage charts consists of a transition and a scheme map over
that transition. -/
@[ext]
structure StageHom (A B : StageChart D) where
  indexMap : A.index ⟶ B.index
  left : A.etale.left ⟶ B.etale.left
  over : left ≫ B.etale.hom = A.etale.hom ≫ D.map indexMap

instance : Category (StageChart D) where
  Hom := StageHom
  id A := ⟨𝟙 A.index, 𝟙 A.etale.left, by
    exact ((Category.id_comp A.etale.hom).trans (Category.comp_id A.etale.hom).symm).trans
      (congrArg (fun m => A.etale.hom ≫ m) (D.map_id A.index).symm)⟩
  comp f g := ⟨f.indexMap ≫ g.indexMap, f.left ≫ g.left, by
    rw [Category.assoc, g.over, ← Category.assoc, f.over, Category.assoc, Functor.map_comp]⟩
  id_comp f := StageHom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id f := StageHom.ext (Category.comp_id _) (Category.comp_id _)
  assoc f g h := StageHom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

@[simp]
theorem id_indexMap (A : StageChart D) : (𝟙 A : A ⟶ A).indexMap = 𝟙 A.index := rfl

@[simp]
theorem id_left (A : StageChart D) : (𝟙 A : A ⟶ A).left = 𝟙 A.etale.left := rfl

@[simp]
theorem comp_indexMap {A B C : StageChart D} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g : A ⟶ C).indexMap = f.indexMap ≫ g.indexMap := rfl

@[simp]
theorem comp_left {A B C : StageChart D} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g : A ⟶ C).left = f.left ≫ g.left := rfl

/-- Include the small étale site of one stage into the category of all
stage charts. -/
def atStage (i : I) : (D.obj i).Etale ⥤ StageChart D where
  obj U := ⟨i, U⟩
  map {U V} f := ⟨𝟙 i, f.left, by
    rw [D.map_id]
    exact f.w⟩
  map_id _ := rfl
  map_comp _ _ := StageHom.ext (Category.id_comp _).symm rfl

variable (c : Cone D)

/-- The obvious scheme morphism after pulling stage charts to the cone
point. -/
private def pullbackMap {A B : StageChart D} (f : A ⟶ B) :
    pullback A.etale.hom (c.π.app A.index) ⟶ pullback B.etale.hom (c.π.app B.index) :=
  pullback.lift
    (pullback.fst A.etale.hom (c.π.app A.index) ≫ f.left)
    (pullback.snd A.etale.hom (c.π.app A.index)) (by
      rw [Category.assoc, f.over, ← Category.assoc, pullback.condition, Category.assoc, c.w])

@[reassoc]
private theorem pullbackMap_fst {A B : StageChart D} (f : A ⟶ B) :
    pullbackMap c f ≫ pullback.fst B.etale.hom (c.π.app B.index) =
      pullback.fst A.etale.hom (c.π.app A.index) ≫ f.left :=
  pullback.lift_fst ..

@[reassoc]
private theorem pullbackMap_snd {A B : StageChart D} (f : A ⟶ B) :
    pullbackMap c f ≫ pullback.snd B.etale.hom (c.π.app B.index) =
      pullback.snd A.etale.hom (c.π.app A.index) :=
  pullback.lift_snd ..

/-- Pull stage charts and their maps to the cone point. -/
def toLimit : StageChart D ⥤ c.pt.Etale where
  obj A := (baseChange (c.π.app A.index)).obj A.etale
  map f := MorphismProperty.Over.homMk (pullbackMap c f) (pullbackMap_snd c f) trivial
  map_id A := by
    apply MorphismProperty.Over.Hom.ext
    change pullbackMap c (𝟙 A) = 𝟙 _
    apply pullback.hom_ext
    · rw [pullbackMap_fst, id_left, Category.id_comp]
      exact Category.comp_id _
    · rw [pullbackMap_snd, Category.id_comp]
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    change pullbackMap c (f ≫ g) = pullbackMap c f ≫ pullbackMap c g
    apply pullback.hom_ext
    · rw [pullbackMap_fst, comp_left, Category.assoc, pullbackMap_fst, pullbackMap_fst_assoc]
    · rw [pullbackMap_snd, Category.assoc, pullbackMap_snd, pullbackMap_snd]

@[reassoc]
theorem toLimit_map_fst {A B : StageChart D} (f : A ⟶ B) :
    ((toLimit c).map f).left ≫ pullback.fst B.etale.hom (c.π.app B.index) =
      pullback.fst A.etale.hom (c.π.app A.index) ≫ f.left :=
  pullbackMap_fst c f

/-- Equality of maps of pulled-back charts is detected by the projections
to the chart at the target stage. -/
theorem toLimit_map_ext {A B : StageChart D} {f g : A ⟶ B}
    (h : pullback.fst A.etale.hom (c.π.app A.index) ≫ f.left =
      pullback.fst A.etale.hom (c.π.app A.index) ≫ g.left) :
    (toLimit c).map f = (toLimit c).map g := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact (toLimit_map_fst c f).trans (h.trans (toLimit_map_fst c g).symm)
  · exact (pullbackMap_snd c f).trans (pullbackMap_snd c g).symm

/-- Pulling back the charts of a fixed stage is the usual étale base change. -/
def atStage_toLimit (i : I) : atStage (D := D) i ⋙ toLimit c ≅ baseChange (c.π.app i) := by
  refine NatIso.ofComponents (fun U => Iso.refl ((toLimit c).obj ((atStage (D := D) i).obj U))) ?_
  intro U V s
  simp only [Iso.refl_hom]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact toLimit_map_fst c ((atStage (D := D) i).map s) |>.trans (pullback.lift_fst ..).symm
  · exact (pullbackMap_snd c ((atStage (D := D) i).map s)).trans (pullback.lift_snd ..).symm

theorem atStage_toLimit_eq (i : I) :
    atStage (D := D) i ⋙ toLimit c = baseChange (c.π.app i) :=
  CategoryTheory.Functor.ext_of_iso (atStage_toLimit c i) (fun _ => rfl) (fun _ => rfl)

end PhilipponEtaleTotalStageSite

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleTotalStageSite (StageChart StageHom toLimit toLimit_map_fst)


namespace PhilipponEtaleChartLimitDiagram

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (A : StageChart D)

private abbrev pullbackAt := Over.pullback A.etale.hom ⋙ Over.forget A.etale.left

/-- The schemes obtained by pulling the chart back to all stages over its
index. -/
abbrev chartDiagram := Over.post (X := A.index) D ⋙ pullbackAt A

/-- A cone on the original diagram gives the corresponding cone of charts. -/
abbrev chartCone (c : Cone D) : Cone (chartDiagram A) :=
  (pullbackAt A).mapCone ((Over.conePost D A.index).obj c)

@[reassoc]
theorem chartMap_fst {j k : Over A.index} (a : j ⟶ k) :
    (chartDiagram A).map a ≫ pullback.fst (D.map k.hom) A.etale.hom =
      pullback.fst (D.map j.hom) A.etale.hom ≫ D.map a.left :=
  pullback.lift_fst ..

@[reassoc]
theorem chartMap_snd {j k : Over A.index} (a : j ⟶ k) :
    (chartDiagram A).map a ≫ pullback.snd (D.map k.hom) A.etale.hom =
      pullback.snd (D.map j.hom) A.etale.hom :=
  pullback.lift_snd ..

@[reassoc]
theorem chartProjection_fst (c : Cone D) (j : Over A.index) :
    (chartCone A c).π.app j ≫ pullback.fst (D.map j.hom) A.etale.hom =
      pullback.fst (c.π.app A.index) A.etale.hom ≫ c.π.app j.left :=
  pullback.lift_fst ..

@[reassoc]
theorem chartProjection_snd (c : Cone D) (j : Over A.index) :
    (chartCone A c).π.app j ≫ pullback.snd (D.map j.hom) A.etale.hom =
      pullback.snd (c.π.app A.index) A.etale.hom :=
  pullback.lift_snd ..

/-- The diagram of charts has the pulled-back cone as its limit. -/
def chartCone_isLimit [IsCofiltered I] (c : Cone D) (hc : IsLimit c) :
    IsLimit (chartCone A c) := by
  let : IsConnected (Over A.index) := IsCofiltered.isConnected (Over A.index)
  exact isLimitOfPreserves (pullbackAt A) (Over.isLimitConePost _ hc)

/-- Regard each base change of a fixed chart as a chart of the new stage. -/
def stageCharts : Over A.index ⥤ StageChart D where
  obj j := ⟨j.left, Scheme.Etale.mk (pullback.fst (D.map j.hom) A.etale.hom)⟩
  map a := ⟨a.left, (chartDiagram A).map a, chartMap_fst A a⟩
  map_id j := StageHom.ext rfl ((chartDiagram A).map_id j)
  map_comp a b := StageHom.ext rfl ((chartDiagram A).map_comp a b)

/-- The chart at an earlier stage maps to the original chart by its
second projection. -/
def toOriginal (j : Over A.index) : (stageCharts A).obj j ⟶ A :=
  ⟨j.hom, pullback.snd (D.map j.hom) A.etale.hom, pullback.condition.symm⟩

@[simp, reassoc]
theorem toOriginal_natural {j k : Over A.index} (a : j ⟶ k) :
    (stageCharts A).map a ≫ toOriginal A k = toOriginal A j :=
  StageHom.ext (Over.w a) (chartMap_snd A a)

/-- The chart after any stage base change has the same pullback to the
limit. The comparison is the pullback of its second projection. -/
def toLimitIso (c : Cone D) (j : Over A.index) :
    (toLimit c).obj ((stageCharts A).obj j) ≅ (toLimit c).obj A := by
  let d := D.map j.hom
  let p := c.π.app j.left
  let a := A.etale.hom
  let v := c.π.app A.index
  let e := pullbackSymmetry (pullback.fst d a) p ≪≫
    pullbackRightPullbackFstIso d a p ≪≫ pullback.congrHom (c.w j.hom) rfl ≪≫ pullbackSymmetry v a
  refine MorphismProperty.Over.isoMk e ?_
  change e.hom ≫ pullback.snd a v = pullback.snd (pullback.fst d a) p
  have hcast : (pullback.congrHom (c.w j.hom) (rfl : a = a)).hom ≫ pullback.fst v a =
      pullback.fst (p ≫ d) a := by
    change pullback.lift (pullback.fst (p ≫ d) a) (pullback.snd (p ≫ d) a) _ ≫
      pullback.fst v a = _
    exact pullback.lift_fst ..
  simp only [e, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
    hcast, pullbackRightPullbackFstIso_hom_fst, pullbackSymmetry_hom_comp_fst]

@[simp]
theorem toLimitIso_hom (c : Cone D) (j : Over A.index) :
    (toLimitIso A c j).hom = (toLimit c).map (toOriginal A j) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · rw [toLimit_map_fst]
    change ((pullbackSymmetry (pullback.fst (D.map j.hom) A.etale.hom) (c.π.app j.left) ≪≫
        pullbackRightPullbackFstIso (D.map j.hom) A.etale.hom (c.π.app j.left) ≪≫
        pullback.congrHom (c.w j.hom) rfl ≪≫
        pullbackSymmetry (c.π.app A.index) A.etale.hom).hom) ≫
          pullback.fst A.etale.hom (c.π.app A.index) = _
    simp [toOriginal]
    rfl
  · exact ((MorphismProperty.Over.w (toLimitIso A c j).hom).trans
      (MorphismProperty.Over.w ((toLimit c).map (toOriginal A j))).symm)

@[reassoc]
theorem toLimit_projection (c : Cone D) (j : Over A.index) :
    ((toLimit c).map (toOriginal A j)).left ≫
      (pullbackSymmetry (c.π.app A.index) A.etale.hom).inv ≫ (chartCone A c).π.app j =
    pullback.fst (pullback.fst (D.map j.hom) A.etale.hom) (c.π.app j.left) := by
  let g := (toLimit c).map (toOriginal A j)
  let e := pullbackSymmetry (c.π.app A.index) A.etale.hom
  apply pullback.hom_ext
  · have hg : g.left ≫ pullback.snd A.etale.hom (c.π.app A.index) =
        pullback.snd (pullback.fst (D.map j.hom) A.etale.hom) (c.π.app j.left) :=
      MorphismProperty.Over.w g
    change (g.left ≫ e.inv ≫ (chartCone A c).π.app j) ≫
      pullback.fst (D.map j.hom) A.etale.hom = _
    rw [Category.assoc, Category.assoc, chartProjection_fst A c j,
      show e.inv ≫ pullback.fst (c.π.app A.index) A.etale.hom ≫ c.π.app j.left =
        pullback.snd A.etale.hom (c.π.app A.index) ≫ c.π.app j.left from
          pullbackSymmetry_inv_comp_fst_assoc .., ← Category.assoc, hg, ← pullback.condition]
    rfl
  · change (g.left ≫ e.inv ≫ (chartCone A c).π.app j) ≫
      pullback.snd (D.map j.hom) A.etale.hom = _
    rw [Category.assoc, Category.assoc, chartProjection_snd,
      show e.inv ≫ pullback.snd (c.π.app A.index) A.etale.hom =
        pullback.fst A.etale.hom (c.π.app A.index) from pullbackSymmetry_inv_comp_snd ..]
    exact toLimit_map_fst c (toOriginal A j)

end PhilipponEtaleChartLimitDiagram

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleTotalStageSite (StageChart StageHom toLimit toLimit_map_fst)
open PhilipponEtaleChartLimitDiagram


namespace PhilipponEtaleStageMapDescent

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ Scheme.{u}} (c : Cone D) (hc : IsLimit c)
  [hStages : ∀ i, IsAffine (D.obj i)] (A B : StageChart D) [hA : IsAffine A.etale.left]

include hc hStages hA in
set_option maxHeartbeats 1200000 in
/-- A map between two pulled-back étale charts is represented over a
common stage when the source chart is affine. -/
theorem exists_stage_map (h : (toLimit c).obj A ⟶ (toLimit c).obj B) :
    ∃ (j : Over A.index) (g : (stageCharts A).obj j ⟶ B),
      (chartCone A c).π.app j ≫ g.left =
        (pullbackSymmetry (c.π.app A.index) A.etale.hom).hom ≫ h.left ≫
          pullback.fst B.etale.hom (c.π.app B.index) := by
  let t : Over A.index := Over.mk (IsCofiltered.minToLeft A.index B.index)
  let r : t.left ⟶ B.index := IsCofiltered.minToRight A.index B.index
  let E := Over.post (X := t) (chartDiagram A) ⋙ Over.forget ((chartDiagram A).obj t)
  let q : Cone E := (Over.forget ((chartDiagram A).obj t)).mapCone
    ((Over.conePost (chartDiagram A) t).obj (chartCone A c))
  let : IsConnected (Over t) := IsCofiltered.isConnected _
  have hq : IsLimit q := isLimitOfPreserves _ (Over.isLimitConePost t (chartCone_isLimit A c hc))
  let d (j : Over t) : E.obj j ⟶ D.obj j.left.left := pullback.fst (D.map j.left.hom) A.etale.hom
  let u (j : Over t) : j.left.left ⟶ B.index := j.hom.left ≫ r
  let s : E ⟶ (Functor.const (Over t)).obj (D.obj B.index) :=
    { app j := d j ≫ D.map (u j)
      naturality {j k} f := by
        have hIndex : f.left.left ≫ u k = u j := by
          change f.left.left ≫ k.hom.left ≫ r = j.hom.left ≫ r
          rw [← Category.assoc]
          exact congrArg (fun a : j.left ⟶ t => a.left ≫ r) (Over.w f)
        have hf : E.map f ≫ d k = d j ≫ D.map f.left.left :=
          chartMap_fst A f.left
        change E.map f ≫ d k ≫ D.map (u k) = (d j ≫ D.map (u j)) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, hf, Category.assoc, ← D.map_comp, hIndex] }
  let e := pullbackSymmetry (c.π.app A.index) A.etale.hom
  let aInf : q.pt ⟶ B.etale.left :=
    e.hom ≫ h.left ≫ pullback.fst B.etale.hom (c.π.app B.index)
  have hOver : aInf ≫ B.etale.hom =
      pullback.fst (c.π.app A.index) A.etale.hom ≫ c.π.app B.index := by
    have hb : h.left ≫ pullback.snd B.etale.hom (c.π.app B.index) =
        pullback.snd A.etale.hom (c.π.app A.index) := MorphismProperty.Over.w h
    calc
      _ = e.hom ≫ h.left ≫ pullback.fst B.etale.hom (c.π.app B.index) ≫ B.etale.hom := by
        simp only [aInf, Category.assoc]
      _ = e.hom ≫ (h.left ≫ pullback.snd B.etale.hom (c.π.app B.index)) ≫ c.π.app B.index := by
        rw [pullback.condition, Category.assoc]
      _ = _ := by
        rw [hb]
        exact pullbackSymmetry_hom_comp_snd_assoc ..
  have hqOver : q.π ≫ s = (Functor.const (Over t)).map (aInf ≫ B.etale.hom) := by
    ext j
    change (chartCone A c).π.app j.left ≫ d j ≫ D.map (u j) = aInf ≫ B.etale.hom
    change (chartCone A c).π.app j.left ≫
      pullback.fst (D.map j.left.hom) A.etale.hom ≫ D.map (u j) = _
    rw [chartProjection_fst_assoc, c.w, hOver]
  let (j : Over t) : IsAffine (E.obj j) := by
    let f : D.obj j.left.left ⟶ D.obj A.index := D.map j.left.hom
    let g : A.etale.left ⟶ D.obj A.index := A.etale.hom
    let : IsAffineHom f := isAffineHom_of_isAffine f
    exact inferInstanceAs (IsAffine (pullback f g))
  let (j : Over t) : CompactSpace (E.obj j) := inferInstance
  let (j : Over t) : QuasiSeparatedSpace (E.obj j) := inferInstance
  let {j k : Over t} (f : j ⟶ k) : IsAffineHom (E.map f) := inferInstance
  obtain ⟨j, g, hg, hgOver⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation E s B.etale.hom q hq aInf hqOver
  exact ⟨j.left, ⟨u j, g, hgOver⟩, hg⟩

include hc hStages hA in
/-- The descended map gives the original one after identifying the
two pullbacks of its source chart. -/
theorem exists_stage_factorization (h : (toLimit c).obj A ⟶ (toLimit c).obj B) :
    ∃ (j : Over A.index) (g : (stageCharts A).obj j ⟶ B),
      (toLimit c).map g = (toLimit c).map (toOriginal A j) ≫ h := by
  obtain ⟨j, g, hg⟩ := exists_stage_map c hc A B h
  refine ⟨j, g, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · let s := ((toLimit c).map (toOriginal A j)).left
    let e := pullbackSymmetry (c.π.app A.index) A.etale.hom
    change ((toLimit c).map g).left ≫ pullback.fst B.etale.hom (c.π.app B.index) =
      (s ≫ h.left) ≫ pullback.fst B.etale.hom (c.π.app B.index)
    rw [toLimit_map_fst c g]
    change pullback.fst (pullback.fst (D.map j.hom) A.etale.hom) (c.π.app j.left) ≫ g.left = _
    rw [← toLimit_projection A c j, Category.assoc, Category.assoc, hg]
    change s ≫ e.inv ≫ e.hom ≫ h.left ≫ pullback.fst B.etale.hom (c.π.app B.index) = _
    rw [e.inv_hom_id_assoc, Category.assoc]
  · exact (MorphismProperty.Over.w ((toLimit c).map g)).trans
      (MorphismProperty.Over.w ((toLimit c).map (toOriginal A j) ≫ h)).symm

include hc hStages hA in
set_option maxHeartbeats 1200000 in
private theorem exists_stage_eq_of_same_index {j : Over A.index}
    (f g : (stageCharts A).obj j ⟶ B) (hIndex : f.indexMap = g.indexMap)
    (hfg : (toLimit c).map f = (toLimit c).map g) :
    ∃ (k : Over A.index) (b : k ⟶ j),
      (stageCharts A).map b ≫ f = (stageCharts A).map b ≫ g := by
  let e := toLimitIso A c j
  let K := Scheme.Etale.forget c.pt ⋙ Over.forget c.pt
  let : IsIso e.hom.left := inferInstanceAs (IsIso (K.map e.hom))
  have hLimit : (chartCone A c).π.app j ≫ f.left = (chartCone A c).π.app j ≫ g.left := by
    let L := pullbackSymmetry (c.π.app A.index) A.etale.hom
    apply (cancel_epi (e.hom.left ≫ L.inv)).mp
    change (e.hom.left ≫ L.inv) ≫ (chartCone A c).π.app j ≫ f.left =
      (e.hom.left ≫ L.inv) ≫ (chartCone A c).π.app j ≫ g.left
    simp only [Category.assoc, e, L, toLimitIso_hom, toLimit_projection_assoc]
    exact (toLimit_map_fst c f).symm.trans
      ((congrArg (fun t => t.left ≫ pullback.fst B.etale.hom (c.π.app B.index)) hfg).trans
        (toLimit_map_fst c g))
  let E := Over.post (X := j) (chartDiagram A) ⋙ Over.forget ((chartDiagram A).obj j)
  let q : Cone E := (Over.forget ((chartDiagram A).obj j)).mapCone
    ((Over.conePost (chartDiagram A) j).obj (chartCone A c))
  let : IsConnected (Over j) := IsCofiltered.isConnected _
  have hq : IsLimit q := isLimitOfPreserves _ (Over.isLimitConePost j (chartCone_isLimit A c hc))
  let i₀ : Over j := Over.mk (𝟙 j)
  let s : E ⟶ (Functor.const (Over j)).obj (D.obj B.index) :=
    { app k := (chartDiagram A).map k.hom ≫ f.left ≫ B.etale.hom
      naturality {k l} b := by
        change (chartDiagram A).map b.left ≫ (chartDiagram A).map l.hom ≫ f.left ≫ B.etale.hom =
          ((chartDiagram A).map k.hom ≫ f.left ≫ B.etale.hom) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, ← (chartDiagram A).map_comp, Over.w b] }
  have hs₀ : s.app i₀ = f.left ≫ B.etale.hom := by
    change (chartDiagram A).map (𝟙 j) ≫ f.left ≫ B.etale.hom = _
    rw [(chartDiagram A).map_id, Category.id_comp]
  have hOver : f.left ≫ B.etale.hom = g.left ≫ B.etale.hom :=
    f.over.trans ((congrArg (fun a => ((stageCharts A).obj j).etale.hom ≫ D.map a) hIndex).trans
      g.over.symm)
  let (k : Over j) : IsAffine (E.obj k) := by
    let a : D.obj k.left.left ⟶ D.obj A.index := D.map k.left.hom
    let b : A.etale.left ⟶ D.obj A.index := A.etale.hom
    let : IsAffineHom a := isAffineHom_of_isAffine a
    exact inferInstanceAs (IsAffine (pullback a b))
  let (k : Over j) : CompactSpace (E.obj k) := inferInstance
  let (k : Over j) : QuasiSeparatedSpace (E.obj k) := inferInstance
  let {k l : Over j} (b : k ⟶ l) : IsAffineHom (E.map b) := inferInstance
  obtain ⟨k, b, hb⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    E s B.etale.hom q hq (i := i₀) f.left g.left hs₀ (hs₀.trans hOver) hLimit
  have hb' : b.left = k.hom := (Category.comp_id b.left).symm.trans (Over.w b)
  refine ⟨k.left, k.hom, StageHom.ext ?_ ?_⟩
  · exact congrArg (k.hom.left ≫ ·) hIndex
  · change (chartDiagram A).map k.hom ≫ f.left = (chartDiagram A).map k.hom ≫ g.left
    change (chartDiagram A).map b.left ≫ f.left = (chartDiagram A).map b.left ≫ g.left at hb
    simpa only [hb'] using hb

include hc hStages hA in
/-- Two maps with the same restriction to the limit agree after a
further base change of their source chart. -/
theorem exists_stage_eq {j : Over A.index} (f g : (stageCharts A).obj j ⟶ B)
    (hfg : (toLimit c).map f = (toLimit c).map g) :
    ∃ (k : Over A.index) (b : k ⟶ j),
      (stageCharts A).map b ≫ f = (stageCharts A).map b ≫ g := by
  let a := IsCofiltered.eqHom f.indexMap g.indexMap
  let l : Over A.index := Over.mk (a ≫ j.hom)
  let u : l ⟶ j := Over.homMk a rfl
  let f' := (stageCharts A).map u ≫ f
  let g' := (stageCharts A).map u ≫ g
  have hIndex : f'.indexMap = g'.indexMap := IsCofiltered.eq_condition _ _
  have he : (toLimit c).map f' = (toLimit c).map g' := by
    change (toLimit c).map ((stageCharts A).map u ≫ f) =
      (toLimit c).map ((stageCharts A).map u ≫ g)
    rw [(toLimit c).map_comp, (toLimit c).map_comp, hfg]
  obtain ⟨k, b, hb⟩ := exists_stage_eq_of_same_index c hc A B f' g' hIndex he
  refine ⟨k, b ≫ u, ?_⟩
  simpa only [f', g', (stageCharts A).map_comp, Category.assoc] using hb

end PhilipponEtaleStageMapDescent

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleTotalStageSite (StageChart toLimit)
open PhilipponEtaleChartLimitDiagram (stageCharts toOriginal toOriginal_natural toLimitIso toLimitIso_hom)


namespace PhilipponEtaleLimitChartIndex

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D) (A : StageChart D)

/-- The pointwise indexing category for colimits at the pullback of a
specified stage chart. -/
abbrev Index := CostructuredArrow (toLimit c).op (op ((toLimit c).obj A))

private theorem inv_comp_stageMap {j k : Over A.index} (a : j ⟶ k) :
    (toLimitIso A c j).inv ≫ (toLimit c).map ((stageCharts A).map a) =
      (toLimitIso A c k).inv := by
  apply (cancel_mono (toLimitIso A c k).hom).mp
  rw [Iso.inv_hom_id, Category.assoc, toLimitIso_hom, ← (toLimit c).map_comp,
    toOriginal_natural, ← toLimitIso_hom, Iso.inv_hom_id]

/-- Each base change of the specified chart gives a pointwise index, with
the transition maps induced from the original diagram. -/
def fromStages : (Over A.index)ᵒᵖ ⥤ Index c A where
  obj j := CostructuredArrow.mk (toLimitIso A c j.unop).inv.op
  map f := CostructuredArrow.homMk ((stageCharts A).map f.unop).op
    (Quiver.Hom.unop_inj (inv_comp_stageMap c A f.unop))
  map_id j := by
    apply CostructuredArrow.hom_ext
    change ((stageCharts A).map (𝟙 j.unop)).op = 𝟙 _
    rw [(stageCharts A).map_id, op_id]
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    change ((stageCharts A).map (g.unop ≫ f.unop)).op =
      ((stageCharts A).map f.unop).op ≫ ((stageCharts A).map g.unop).op
    rw [(stageCharts A).map_comp, op_comp]

/-- Every pointwise index maps into one from a stage of an affine chart. -/
theorem exists_arrow_to_stage [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
    [IsAffine A.etale.left] (hc : IsLimit c) (B : Index c A) :
    ∃ j : (Over A.index)ᵒᵖ, Nonempty (B ⟶ (fromStages c A).obj j) := by
  let h := B.hom.unop
  obtain ⟨j, g, hg⟩ := PhilipponEtaleStageMapDescent.exists_stage_factorization c hc A B.left.unop h
  refine ⟨op j, ⟨CostructuredArrow.homMk g.op ?_⟩⟩
  apply Quiver.Hom.unop_inj
  change (toLimitIso A c j).inv ≫ (toLimit c).map g = h
  rw [hg, ← toLimitIso_hom, Iso.inv_hom_id_assoc]

/-- At the pullback of an affine stage chart, its earlier base changes
are final in the pointwise colimit index. -/
theorem fromStages_final [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
    [IsAffine A.etale.left] (hc : IsLimit c) : (fromStages c A).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · exact exists_arrow_to_stage c A hc
  · intro B j f g
    let f' : (stageCharts A).obj j.unop ⟶ B.left.unop := f.left.unop
    let g' : (stageCharts A).obj j.unop ⟶ B.left.unop := g.left.unop
    have hf : (toLimitIso A c j.unop).inv ≫ (toLimit c).map f' = B.hom.unop :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w f)
    have hg : (toLimitIso A c j.unop).inv ≫ (toLimit c).map g' = B.hom.unop :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w g)
    have hfg : (toLimit c).map f' = (toLimit c).map g' :=
      (cancel_epi (toLimitIso A c j.unop).inv).mp (hf.trans hg.symm)
    obtain ⟨k, b, hb⟩ :=
      PhilipponEtaleStageMapDescent.exists_stage_eq c hc A B.left.unop f' g' hfg
    refine ⟨op k, b.op, ?_⟩
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    exact hb

/-- A colimit over the charts at the stages computes the pointwise
colimit at the pullback of the fixed chart. -/
def pointwiseColimit [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
    [IsAffine A.etale.left] (hc : IsLimit c)
    {B : Type*} [Category* B] (P : (StageChart D)ᵒᵖ ⥤ B)
    (d : ColimitCocone ((stageCharts A).op ⋙ P)) :
    ColimitCocone (CostructuredArrow.proj (toLimit c).op (op ((toLimit c).obj A)) ⋙ P) := by
  let : (fromStages c A).Final := fromStages_final c A hc
  exact Functor.Final.colimitCoconeOfComp (fromStages c A) d

end PhilipponEtaleLimitChartIndex

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open PhilipponCompatibleInjectiveSystems


namespace PhilipponCompatibleSystemCokernel

universe u v w

variable {I : Type u} [Category.{u} I]
  {C : I → Type v} [∀ i, Category.{w} (C i)] [∀ i, Abelian (C i)]
  {R : DirectImages C}

/-- A map of compatible families, with its commutation along every transition. -/
structure Hom (F G : System R) where
  app (i : I) : F.obj i ⟶ G.obj i
  naturality {i j : I} (a : i ⟶ j) :
    app j ≫ G.map a = F.map a ≫ (R.functor a).map (app i)

omit [∀ i, Abelian (C i)] in
@[ext]
theorem Hom.ext {F G : System R} {f g : Hom F G} (h : ∀ i, f.app i = g.app i) : f = g := by
  cases f
  cases g
  congr
  funext i
  exact h i

/-- Composition of maps of compatible families is taken at each stage. -/
instance : Category (System R) where
  Hom := Hom
  id F := ⟨fun i => 𝟙 (F.obj i), by simp⟩
  comp f g := ⟨fun i => f.app i ≫ g.app i, by
    intro i j a
    rw [Category.assoc, g.naturality, ← Category.assoc, f.naturality,
      Category.assoc, (R.functor a).map_comp]⟩
  id_comp f := Hom.ext (fun _ => Category.id_comp _)
  comp_id f := Hom.ext (fun _ => Category.comp_id _)
  assoc f g h := Hom.ext (fun _ => Category.assoc _ _ _)

@[simp]
theorem id_app (F : System R) (i : I) : (𝟙 F : Hom F F).app i = 𝟙 _ := rfl

@[simp]
theorem comp_app {F G H : System R} (f : F ⟶ G) (g : G ⟶ H) (i : I) :
    (f ≫ g : F ⟶ H).app i = f.app i ≫ g.app i := rfl

variable [∀ {i j : I} (a : i ⟶ j), (R.functor a).PreservesZeroMorphisms]
  {F G : System R} (η : Hom F G)

instance : HasZeroMorphisms (System R) where
  zero F G := ⟨fun i => 0, by intro i j a; rw [zero_comp, (R.functor a).map_zero, comp_zero]⟩
  comp_zero := by intros; exact Hom.ext (fun _ => comp_zero)
  zero_comp := by intros; exact Hom.ext (fun _ => zero_comp)

@[simp]
theorem zero_app (i : I) : (0 : F ⟶ G).app i = 0 := rfl

private def desc {i j : I} (a : i ⟶ j) :
    cokernel (η.app j) ⟶ (R.functor a).obj (cokernel (η.app i)) :=
  cokernel.desc (η.app j) (G.map a ≫ (R.functor a).map (cokernel.π (η.app i))) (by
    rw [← Category.assoc, η.naturality, Category.assoc, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, comp_zero])

@[reassoc]
private theorem π_desc {i j : I} (a : i ⟶ j) :
    cokernel.π (η.app j) ≫ desc η a =
      G.map a ≫ (R.functor a).map (cokernel.π (η.app i)) :=
  cokernel.π_desc ..

private theorem desc_identity (i : I) :
    desc η (𝟙 i) ≫ (R.identity i).hom.app (cokernel (η.app i)) = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (η.app i))).mp
  rw [Category.comp_id, π_desc_assoc]
  have hn : (R.functor (𝟙 i)).map (cokernel.π (η.app i)) ≫
      (R.identity i).hom.app (cokernel (η.app i)) =
      (R.identity i).hom.app (G.obj i) ≫ cokernel.π (η.app i) :=
    (R.identity i).hom.naturality (cokernel.π (η.app i))
  rw [hn, ← Category.assoc, G.map_identity, Category.id_comp]

private theorem desc_composition {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    desc η (a ≫ b) ≫ (R.composition a b).hom.app (cokernel (η.app i)) =
      desc η b ≫ (R.functor b).map (desc η a) := by
  apply (cancel_epi (cokernel.π (η.app k))).mp
  have hn : (R.functor (a ≫ b)).map (cokernel.π (η.app i)) ≫
      (R.composition a b).hom.app (cokernel (η.app i)) =
      (R.composition a b).hom.app (G.obj i) ≫
        (R.functor b).map ((R.functor a).map (cokernel.π (η.app i))) :=
    (R.composition a b).hom.naturality (cokernel.π (η.app i))
  rw [π_desc_assoc, π_desc_assoc, hn, ← Category.assoc, G.map_composition]
  simp only [Category.assoc, ← (R.functor b).map_comp, π_desc]

/-- Form the cokernel at every stage and give it its induced transition maps. -/
def cokernelSystem : System R where
  obj i := cokernel (η.app i)
  map := desc η
  map_identity := desc_identity η
  map_composition := desc_composition η

/-- The cokernel projections commute with the system's transition maps. -/
def cokernelProjection : Hom G (cokernelSystem η) where
  app i := cokernel.π (η.app i)
  naturality := π_desc η

end PhilipponCompatibleSystemCokernel

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems
open PhilipponEtaleDirectImageSystem (chart fst fst_ext map_fst_assoc unitChart
  unitChart_inv_fst flatten flatten_fst_assoc directImages)
open PhilipponEtaleStageSectionDiagram (eval eval_id eval_comp_assoc eval_naturality_assoc)
open PhilipponEtaleTotalStageSite (StageChart atStage toLimit)
open PhilipponEtaleChartLimitDiagram (stageCharts)
open PhilipponCompatibleSystemCokernel (Hom)


namespace PhilipponEtaleSystemPresheaf

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}

/-- Factor a map of stage charts through the base change of its target. -/
def intoBaseChange {A B : StageChart D} (f : A ⟶ B) :
    A.etale ⟶ (chart D f.indexMap).obj B.etale :=
  MorphismProperty.Over.homMk (pullback.lift f.left A.etale.hom f.over) (pullback.lift_snd ..) trivial

@[reassoc]
private theorem intoBaseChange_fst {A B : StageChart D} (f : A ⟶ B) :
    (intoBaseChange f).left ≫ fst D f.indexMap B.etale = f.left :=
  pullback.lift_fst ..

private theorem intoBaseChange_id (A : StageChart D) :
    intoBaseChange (𝟙 A) = (unitChart D A.index).inv.app A.etale := by
  apply fst_ext D (𝟙 A.index) A.etale
  exact (intoBaseChange_fst (𝟙 A)).trans (unitChart_inv_fst D A.index A.etale).symm

private theorem intoBaseChange_comp {A B C : StageChart D} (f : A ⟶ B) (g : B ⟶ C) :
    intoBaseChange (f ≫ g) =
      intoBaseChange f ≫ (chart D f.indexMap).map (intoBaseChange g) ≫
        (flatten D f.indexMap g.indexMap).hom.app C.etale := by
  apply fst_ext D (f.indexMap ≫ g.indexMap) C.etale
  change (intoBaseChange (f ≫ g)).left ≫ fst D (f.indexMap ≫ g.indexMap) C.etale =
    ((intoBaseChange f).left ≫ ((chart D f.indexMap).map (intoBaseChange g)).left ≫
      ((flatten D f.indexMap g.indexMap).hom.app C.etale).left) ≫
        fst D (f.indexMap ≫ g.indexMap) C.etale
  have h := intoBaseChange_fst (f ≫ g)
  simp only [Category.assoc, PhilipponEtaleDirectImageSystem.flatten_fst, map_fst_assoc,
    intoBaseChange_fst, intoBaseChange_fst_assoc]
  exact h

variable (F : System (directImages D))

private abbrev sectionGroup (A : StageChart D) := (F.obj A.index).obj.obj (op A.etale)

private def mapSections {A B : StageChart D} (f : A ⟶ B) :
    sectionGroup F B ⟶ sectionGroup F A :=
  eval D F f.indexMap B.etale ≫ (F.obj A.index).obj.map (intoBaseChange f).op

/-- A compatible coefficient system gives a presheaf on all stage charts. -/
def presheaf : (StageChart D)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj A := sectionGroup F A.unop
  map f := mapSections F f.unop
  map_id A := by
    change eval D F (𝟙 A.unop.index) A.unop.etale ≫
      (F.obj A.unop.index).obj.map (intoBaseChange (𝟙 A.unop)).op = 𝟙 _
    rw [intoBaseChange_id, eval_id]
  map_comp {A B C} f g := by
    change eval D F (g.unop.indexMap ≫ f.unop.indexMap) A.unop.etale ≫
      (F.obj C.unop.index).obj.map (intoBaseChange (g.unop ≫ f.unop)).op = _
    rw [intoBaseChange_comp, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc, eval_comp_assoc, mapSections, eval_naturality_assoc]

/-- The canonical map from a pulled-back chart to its original chart. -/
def cartesianMap {i : I} (A : StageChart D) (a : i ⟶ A.index) :
    (⟨i, (chart D a).obj A.etale⟩ : StageChart D) ⟶ A :=
  ⟨a, fst D a A.etale, pullback.condition⟩

theorem factor_through_cartesian {A B : StageChart D} (f : A ⟶ B) :
    (atStage A.index).map (intoBaseChange f) ≫ cartesianMap B f.indexMap = f :=
  PhilipponEtaleTotalStageSite.StageHom.ext (Category.id_comp _) (intoBaseChange_fst f)

/-- Restriction along a canonical stage pullback is the coefficient
transition evaluated at the original chart. -/
theorem map_cartesian {i : I} (A : StageChart D) (a : i ⟶ A.index) :
    (presheaf F).map (cartesianMap A a).op = eval D F a A.etale := by
  have e : intoBaseChange (cartesianMap A a) = 𝟙 _ := by
    apply fst_ext D a A.etale
    exact (intoBaseChange_fst (cartesianMap A a)).trans (Category.id_comp _).symm
  change eval D F a A.etale ≫ (F.obj i).obj.map (intoBaseChange (cartesianMap A a)).op = _
  rw [e, op_id, (F.obj i).obj.map_id, Category.comp_id]

/-- At a fixed stage, restriction of sections is the original sheaf's
restriction map. -/
theorem map_atStage {i : I} {U V : (D.obj i).Etale} (s : U ⟶ V) :
    (presheaf F).map ((atStage i).map s).op = (F.obj i).obj.map s.op := by
  change eval D F (𝟙 i) V ≫ (F.obj i).obj.map (intoBaseChange ((atStage i).map s)).op = _
  have h : intoBaseChange ((atStage i).map s) = s ≫ (unitChart D i).inv.app V := by
    apply fst_ext D (𝟙 i) V
    change (intoBaseChange ((atStage i).map s)).left ≫ fst D (𝟙 i) V =
      (s.left ≫ ((unitChart D i).inv.app V).left) ≫ fst D (𝟙 i) V
    have hp : (intoBaseChange ((atStage i).map s)).left ≫ fst D (𝟙 i) V = s.left :=
      intoBaseChange_fst ((atStage i).map s)
    rw [hp, Category.assoc, unitChart_inv_fst, Category.comp_id]
  rw [h, op_comp, Functor.map_comp, ← Category.assoc, eval_id, Category.id_comp]

/-- A map of coefficient systems induces the component maps on all stage
charts. -/
def presheafMap {F G : System (directImages D)} (η : Hom F G) :
    presheaf F ⟶ presheaf G where
  app A := (η.app A.unop.index).hom.app (op A.unop.etale)
  naturality {B A} s := by
    let f := s.unop
    let β := op B.unop.etale
    let α := op A.unop.etale
    let k := (intoBaseChange f).op
    change (eval D F f.indexMap B.unop.etale ≫ (F.obj A.unop.index).obj.map k) ≫
      (η.app A.unop.index).hom.app α =
      (η.app B.unop.index).hom.app β ≫
        eval D G f.indexMap B.unop.etale ≫ (G.obj A.unop.index).obj.map k
    have h := congrArg (fun t => t.hom.app β) (η.naturality f.indexMap)
    change (η.app B.unop.index).hom.app β ≫ eval D G f.indexMap B.unop.etale =
      eval D F f.indexMap B.unop.etale ≫ (η.app A.unop.index).hom.app _ at h
    rw [Category.assoc, (η.app A.unop.index).hom.naturality k,
      ← Category.assoc, ← Category.assoc, h]

/-- Compatible systems and their maps define presheaves on stage charts. -/
def presheafFunctor : System (directImages D) ⥤ (StageChart D)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj := presheaf
  map := presheafMap
  map_id _ := NatTrans.ext (funext fun _ => rfl)
  map_comp _ _ := NatTrans.ext (funext fun _ => rfl)

instance : (presheafFunctor (D := D)).PreservesZeroMorphisms where
  map_zero _ _ := NatTrans.ext (funext fun _ => rfl)

/-- The pointwise colimit of the coefficient system at the pullback of an
affine chart exists and is computed over the stages of that chart. -/
def colimitAt [IsCofiltered I] [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (A : StageChart D) [IsAffine A.etale.left] :
    ColimitCocone (CostructuredArrow.proj (toLimit c).op (op ((toLimit c).obj A)) ⋙ presheaf F) := by
  let P := (stageCharts A).op ⋙ presheaf F
  exact PhilipponEtaleLimitChartIndex.pointwiseColimit c A hc (presheaf F)
    ⟨colimit.cocone P, colimit.isColimit P⟩

end PhilipponEtaleSystemPresheaf

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (StageChart StageHom toLimit atStage toLimit_map_fst)
open PhilipponEtaleSystemPresheaf (presheaf map_atStage cartesianMap map_cartesian)


namespace PhilipponEtaleConeSystem

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D)

/-- Regard the cone point as an initial stage. -/
abbrev extended := WithInitial.lift D c.π.app (fun _ _ f => c.w f)

/-- The original stage charts are charts of the extended diagram. -/
def inclCharts : StageChart D ⥤ StageChart (extended c) where
  obj A := ⟨WithInitial.of A.index, A.etale⟩
  map f := ⟨WithInitial.incl.map f.indexMap, f.left, f.over⟩
  map_id _ := StageHom.ext rfl rfl
  map_comp _ _ := StageHom.ext rfl rfl

/-- The limit charts map naturally to the charts they came from. -/
def projection : toLimit c ⋙ atStage (D := extended c) WithInitial.star ⟶ inclCharts c where
  app A := ⟨WithInitial.homTo A.index, pullback.fst A.etale.hom (c.π.app A.index), pullback.condition⟩
  naturality {_ _} f := StageHom.ext rfl (toLimit_map_fst c f)

variable (F : System (directImages (extended c)))

/-- Restrict a system on the whole cone to the original diagram. -/
def restrict : System (directImages D) where
  obj i := F.obj (WithInitial.of i)
  map a := F.map (WithInitial.incl.map a)
  map_identity i := F.map_identity (WithInitial.of i)
  map_composition a b := F.map_composition (WithInitial.incl.map a) (WithInitial.incl.map b)

private def inclPresheafIso : presheaf (restrict c F) ≅ (inclCharts c).op ⋙ presheaf F := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro A B f
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private def pointPresheafIso :
    (atStage (D := extended c) WithInitial.star).op ⋙ presheaf F ≅ (F.obj WithInitial.star).obj := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro U V f
  have h := map_atStage F f.unop
  exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm)

/-- A compatible family on the cone supplies canonical section maps
from the stages to the cone point. -/
def projectionMap : presheaf (restrict c F) ⟶ (toLimit c).op ⋙ (F.obj WithInitial.star).obj := by
  let d : (inclCharts c).op ⟶ (toLimit c).op ⋙ (atStage (D := extended c) WithInitial.star).op :=
    NatTrans.op (projection c)
  exact (inclPresheafIso c F).hom ≫ Functor.whiskerRight d (presheaf F) ≫
    Functor.whiskerLeft (toLimit c).op (pointPresheafIso c F).hom

/-- On a stage chart the comparison evaluates the transition to the cone point. -/
theorem projectionMap_app (A : StageChart D) :
    (projectionMap c F).app (op A) = (F.map (WithInitial.homTo A.index)).hom.app (op A.etale) := by
  have e : (projection c).app A =
      cartesianMap ((inclCharts c).obj A) (WithInitial.homTo A.index) := rfl
  change 𝟙 _ ≫ (presheaf F).map ((projection c).app A).op ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id, e]
  exact map_cartesian F ((inclCharts c).obj A) (WithInitial.homTo A.index)

end PhilipponEtaleConeSystem

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages flatten fst_ext flatten_fst)
open PhilipponEtaleTotalStageSite (StageChart toLimit atStage atStage_toLimit toLimit_map_fst)
open PhilipponEtaleSystemPresheaf (presheaf map_atStage cartesianMap map_cartesian)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConeSystem (extended)
open PhilipponEtaleBaseChangeComparison (baseChange)


namespace PhilipponEtaleLimitTestMaps

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D)
  (F : System (directImages D)) (H : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})

private abbrev stage (i : I) (U : (D.obj i).Etale) : StageChart D := ⟨i, U⟩

private theorem map_cartesian_toLimit {i j : I} (a : i ⟶ j) (V : (D.obj j).Etale) :
    (toLimit c).map (cartesianMap (stage j V) a) =
      (flatten (extended c) (WithInitial.homTo i) (WithInitial.incl.map a)).hom.app V := by
  apply fst_ext (extended c) (WithInitial.homTo j) V
  have h := toLimit_map_fst c (cartesianMap (stage j V) a)
  exact h.trans (flatten_fst (extended c) (WithInitial.homTo i) (WithInitial.incl.map a) V).symm

variable (η : presheaf F ⟶ (toLimit c).op ⋙ H.obj)

/-- A natural map into a test sheaf on the limit restricts at each stage
to a map into its direct image. -/
def stageMap (i : I) : F.obj i ⟶ (pushforward (c.π.app i)).obj H :=
  ⟨{ app := fun V => η.app (op (stage i V.unop))
     naturality := by
       intro V U f
       have h := η.naturality ((atStage i).map f.unop).op
       rw [map_atStage] at h
       let K := atStage (D := D) i ⋙ toLimit c
       change (F.obj i).obj.map f ≫ η.app (op (stage i U.unop)) =
         η.app (op (stage i V.unop)) ≫ H.obj.map ((baseChange (c.π.app i)).map f.unop).op
       have hh : K.map f.unop = (baseChange (c.π.app i)).map f.unop := by
         have he := (atStage_toLimit c i).hom.naturality f.unop
         change K.map f.unop ≫ 𝟙 _ = 𝟙 _ ≫ (baseChange (c.π.app i)).map f.unop at he
         simpa only [Category.comp_id, Category.id_comp] using he
       have he := congrArg (fun (m : K.obj U.unop ⟶ K.obj V.unop) =>
         η.app (op (stage i V.unop)) ≫ H.obj.map m.op) hh
       exact h.trans he }⟩

/-- These stage maps commute with the direct-image comparisons from the cone. -/
theorem naturality {i j : I} (a : i ⟶ j) :
    stageMap c F H η j ≫
        ((directImages (extended c)).composition (WithInitial.homTo i) (WithInitial.incl.map a)).hom.app H =
      F.map a ≫ ((directImages D).functor a).map (stageMap c F H η i) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let v := V.unop
  let a' := cartesianMap (stage j v) a
  have h := η.naturality (cartesianMap (stage j v) a).op
  rw [map_cartesian] at h
  have e := map_cartesian_toLimit c a v
  change (stageMap c F H η j).hom.app (op v) ≫
      H.obj.map ((flatten (extended c) (WithInitial.homTo i) (WithInitial.incl.map a)).hom.app v).op =
    (F.map a).hom.app (op v) ≫
      (stageMap c F H η i).hom.app (op ((PhilipponEtaleDirectImageSystem.chart D a).obj v))
  let T := stage i ((PhilipponEtaleDirectImageSystem.chart D a).obj v)
  have he := congrArg (fun (u : (toLimit c).obj T ⟶ (toLimit c).obj (stage j v)) =>
      (stageMap c F H η j).hom.app (op v) ≫ H.obj.map u.op) e
  exact he.symm.trans h.symm

/-- Natural maps on the total stage site are determined by their stage maps. -/
theorem ext {ζ : presheaf F ⟶ (toLimit c).op ⋙ H.obj}
    (h : ∀ i, stageMap c F H η i = stageMap c F H ζ i) : η = ζ := by
  apply NatTrans.ext
  funext V
  exact congrArg (fun p => p.hom.app (op V.unop.etale)) (h V.unop.index)

end PhilipponEtaleLimitTestMaps

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open PhilipponCompatibleInjectiveSystems


namespace PhilipponCompatibleTerminalPullback

universe u v w

variable {I : Type u} [Category.{u} I]
  {C : WithTerminal I → Type v} [∀ i, Category.{w} (C i)] (R : DirectImages C)

private abbrev inc := WithTerminal.incl (C := I)

/-- Restrict the coherent direct images to the original category. -/
def restrict : DirectImages (fun i : I => C (WithTerminal.of i)) where
  functor a := R.functor (inc.map a)
  identity i := R.identity (WithTerminal.of i)
  composition a b := R.composition (inc.map a) (inc.map b)
  comp_identity a A := R.comp_identity (inc.map a) A
  comp_assoc a b d A := R.comp_assoc (inc.map a) (inc.map b) (inc.map d) A

private abbrev right (i : I) : C (WithTerminal.of i) ⥤ C WithTerminal.star :=
  R.functor (WithTerminal.homFrom i)

/-- The direct image to the terminal stage factors along any transition. -/
def toTerminal {i j : I} (a : i ⟶ j) :
    right R i ≅ (restrict R).functor a ⋙ right R j :=
  R.composition (inc.map a) (WithTerminal.homFrom j)

variable {L : ∀ i : I, C WithTerminal.star ⥤ C (WithTerminal.of i)}
  (adj : ∀ i : I, L i ⊣ right R i) (P : C WithTerminal.star)

variable (L) in
private abbrev obj (i : I) := (L i).obj P

private def pullMap {i j : I} (a : i ⟶ j) :
    obj L P j ⟶ ((restrict R).functor a).obj (obj L P i) :=
  ((adj j).homEquiv _ _).symm ((adj i).unit.app P ≫ (toTerminal R a).hom.app (obj L P i))

@[reassoc]
private theorem unit_pullMap {i j : I} (a : i ⟶ j) :
    (adj j).unit.app P ≫ (right R j).map (pullMap R adj P a) =
      (adj i).unit.app P ≫ (toTerminal R a).hom.app (obj L P i) := by
  calc
    _ = (adj j).homEquiv _ _ (pullMap R adj P a) := (Adjunction.homEquiv_unit ..).symm
    _ = _ := ((adj j).homEquiv _ _).apply_symm_apply _

private theorem assoc_toTerminal {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (A : C (WithTerminal.of i)) :
    (toTerminal R (a ≫ b)).hom.app A ≫
        (right R k).map (((restrict R).composition a b).hom.app A) =
      (toTerminal R a).hom.app A ≫ (toTerminal R b).hom.app (((restrict R).functor a).obj A) := by
  have h := R.comp_assoc (inc.map a) (inc.map b) (WithTerminal.homFrom k) A
  have hz : eqToHom (congrArg (fun d => (R.functor d).obj A)
      (Category.assoc (inc.map a) (inc.map b) (WithTerminal.homFrom k))) = 𝟙 _ := by
    have he : Category.assoc (inc.map a) (inc.map b) (WithTerminal.homFrom k) = rfl :=
      Subsingleton.elim _ _
    rw [he]
    rfl
  simp only [hz, Category.id_comp] at h
  exact h

variable (hUnit : ∀ (i : I) (A : C (WithTerminal.of i)),
    (toTerminal R (𝟙 i)).hom.app A ≫ (right R i).map ((R.identity (WithTerminal.of i)).hom.app A) = 𝟙 _)

include hUnit in
private theorem pullMap_identity (i : I) :
    pullMap R adj P (𝟙 i) ≫ ((restrict R).identity i).hom.app (obj L P i) = 𝟙 _ := by
  apply ((adj i).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (adj i).unit.app P ≫ (right R i).map
      (pullMap R adj P (𝟙 i) ≫ (R.identity (WithTerminal.of i)).hom.app (obj L P i)) =
    (adj i).unit.app P ≫ (right R i).map (𝟙 (obj L P i))
  rw [(right R i).map_comp]
  let e := (R.identity (WithTerminal.of i)).hom.app (obj L P i)
  calc
    _ = ((adj i).unit.app P ≫ (right R i).map (pullMap R adj P (𝟙 i))) ≫ (right R i).map e :=
      (Category.assoc _ _ _).symm
    _ = ((adj i).unit.app P ≫ (toTerminal R (𝟙 i)).hom.app (obj L P i)) ≫ (right R i).map e :=
      congrArg (fun m => m ≫ (right R i).map e) (unit_pullMap R adj P (𝟙 i))
    _ = _ := by
      rw [Category.assoc, hUnit i (obj L P i), (right R i).map_id]

private theorem pullMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    pullMap R adj P (a ≫ b) ≫ ((restrict R).composition a b).hom.app (obj L P i) =
      pullMap R adj P b ≫ ((restrict R).functor b).map (pullMap R adj P a) := by
  apply ((adj k).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, unit_pullMap]
  have hn := (toTerminal R b).hom.naturality (pullMap R adj P a)
  change (right R j).map (pullMap R adj P a) ≫ _ = _ ≫
    (right R k).map (((restrict R).functor b).map (pullMap R adj P a)) at hn
  simp only [Category.assoc, ← hn, unit_pullMap_assoc, assoc_toTerminal]

/-- The inverse images of a coefficient on the terminal object form
a compatible system. -/
def system : System (restrict R) where
  obj := obj L P
  map := pullMap R adj P
  map_identity := pullMap_identity R adj P hUnit
  map_composition := pullMap_comp R adj P

/-- The inverse-image units characterize the transition maps of the system. -/
@[reassoc]
theorem system_unit {i j : I} (a : i ⟶ j) :
    (adj j).unit.app P ≫ (right R j).map ((system R adj P hUnit).map a) =
      (adj i).unit.app P ≫ (toTerminal R a).hom.app (obj L P i) :=
  unit_pullMap R adj P a

end PhilipponCompatibleTerminalPullback

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages directImages_identity_comp)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleClosedPushforward (pushforward)


namespace PhilipponEtalePullbackSystem

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) {X : Scheme.{u}}
  (p : ∀ i, D.obj i ⟶ X) (hp : ∀ (i j : I) (a : i ⟶ j), D.map a ≫ p j = p i)

/-- Adjoin the fixed base scheme as a terminal stage. -/
abbrev extended := WithTerminal.lift D p hp

private abbrev E := directImages (extended D p hp)

/-- The direct-image comparison for a transition over a fixed base. -/
def toBase {i j : I} (a : i ⟶ j) :
    pushforward (p i) ≅ (directImages D).functor a ⋙ pushforward (p j) :=
  PhilipponCompatibleTerminalPullback.toTerminal (E D p hp) a

private theorem left_unit (i : I) (F : Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u}) :
    (toBase D p hp (𝟙 i)).hom.app F ≫
      (pushforward (p i)).map (((directImages D).identity i).hom.app F) = 𝟙 _ := by
  let a := WithTerminal.homFrom i
  have h := directImages_identity_comp (extended D p hp) a F
  simp only [eqToHom_refl] at h
  exact h

variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- Inverse images of a fixed small étale sheaf give a compatible system
on any diagram over the base. -/
def pullbackSystem : System (directImages D) :=
  PhilipponCompatibleTerminalPullback.system (E D p hp) (fun i => pullbackAdjunction (p i)) F
    (left_unit D p hp)

/-- On objects the compatible system is the original sheaf's inverse image. -/
theorem pullbackSystem_obj (i : I) : (pullbackSystem D p hp F).obj i = (pullbackSheaves (p i)).obj F :=
  rfl

/-- The transition maps preserve the inverse-image units over the base. -/
@[reassoc]
theorem system_unit {i j : I} (a : i ⟶ j) :
    (pullbackAdjunction (p j)).unit.app F ≫ (pushforward (p j)).map ((pullbackSystem D p hp F).map a) =
      (pullbackAdjunction (p i)).unit.app F ≫
        (toBase D p hp a).hom.app ((pullbackSystem D p hp F).obj i) :=
  PhilipponCompatibleTerminalPullback.system_unit (E D p hp) (fun i => pullbackAdjunction (p i))
    F (left_unit D p hp) a

end PhilipponEtalePullbackSystem

end

end


