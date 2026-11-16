-- Prove2me | Definitions.Def_RPLib_S4_EtShHom
-- name    : RPLib_S4_EtShHom
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:26:55.599352+00:00
-- url     : https://prove2.me/theorems/ab97529b-8792-494d-9ed9-4395eb10d868
-- title:
--   The internal Hom of etale sheaves
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For $F, G \in \mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$, $\mathcal{H}om(F, G)$ is the sheaf $V \mapsto \mathrm{Hom}(F|_V, G|_V)$ (morphisms of the restrictions to the slice over $V$). These Hom sets are small, because the slice of the small etale site of $X$ over $V$ is equivalent to the small etale site of $V$ and etale sheaves on $V$ form a Grothendieck abelian category. The dual is $F^\vee = \mathcal{H}om(F, \Lambda_X)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose IV, Section 12; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShRes

/-!
# S4-EtSheaves, part 7: the internal Hom of etale sheaves

For etale sheaves `F`, `G` of `Λ`-modules on `X`, `homSh F G` is the sheaf `V ↦ Hom(F|_V, G|_V)`
(Mathlib's `presheafHom`: morphisms of the restrictions to `Over V`), shrunk to `Type u`. These hom
sets are small because `Over V ≌ V.left.Etale` (`overOf`) and etale sheaves on `V.left` form a
Grothendieck abelian category. `dualSh F = Hom(F, Λ_X)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

/-- Whiskering along an equivalence `Φ : D ⥤ Over V` identifies `Hom(P|_V, Q|_V)` with natural
transformations between the restrictions along `Φ ⋙ Over.forget V`. -/
def presheafHomEquiv {C D A : Type*} [Category* C] [Category* D] [Category* A] (P Q : Cᵒᵖ ⥤ A)
    {V : C} (Φ : D ⥤ Over V) [Φ.IsEquivalence] :
    ((Over.forget V).op ⋙ P ⟶ (Over.forget V).op ⋙ Q) ≃
      ((Φ ⋙ Over.forget V).op ⋙ P ⟶ (Φ ⋙ Over.forget V).op ⋙ Q) :=
  (Φ.asEquivalence.op.congrLeft (E := A)).fullyFaithfulInverse.homEquiv

variable {X : Scheme.{u}}

instance etaleHom (V : X.Etale) : Etale V.hom := V.prop

/-- An etale `V.left`-scheme, viewed as an object of `X.Etale` over `V`. -/
def overOf (V : X.Etale) : V.left.Etale ⥤ Over V where
  obj W := Over.mk (MorphismProperty.Over.homMk W.hom rfl trivial : (etComp V.hom).obj W ⟶ V)
  map φ := Over.homMk ((etComp V.hom).map φ)
    (MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w φ))
  map_id W := Over.OverMorphism.ext ((etComp V.hom).map_id W)
  map_comp φ ψ := Over.OverMorphism.ext ((etComp V.hom).map_comp φ ψ)

instance (V : X.Etale) : (overOf V).Faithful where
  map_injective {_ _} _ _ h := MorphismProperty.Over.Hom.ext (congrArg (fun f => f.left.left) h)

instance (V : X.Etale) : (overOf V).Full where
  map_surjective {_ _} ψ := ⟨MorphismProperty.Over.homMk ψ.left.left
    (congrArg (fun f => f.left) (Over.w ψ)) trivial,
    Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext rfl)⟩

instance (V : X.Etale) : (overOf V).EssSurj where
  mem_essImage T := by
    have h : T.hom.left ≫ (etId V.left).hom ≫ V.hom = T.left.hom := by
      change T.hom.left ≫ 𝟙 V.left ≫ V.hom = T.left.hom
      rw [Category.id_comp]
      exact MorphismProperty.Over.w T.hom
    refine ⟨etLift V.hom (W := etId V.left) T.left T.hom.left h, ⟨Over.isoMk
      (MorphismProperty.Over.isoMk (Iso.refl _) ?_) ?_⟩⟩
    · exact (Category.id_comp _).trans h.symm
    · exact MorphismProperty.Over.Hom.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

instance (V : X.Etale) : (overOf V).IsEquivalence where

variable {Λ : Type u} [CommRing Λ] (F G : EtSh Λ X)

/-- Sections of `Hom(F, G)` over `V`: morphisms of the restrictions of `F`, `G` to `Over V`. -/
abbrev HomOver (V : X.Etale) := (Over.forget V).op ⋙ F.obj ⟶ (Over.forget V).op ⋙ G.obj

set_option backward.isDefEq.respectTransparency false in
/-- `HomOver F G V ≃ Hom(F|_V, G|_V)`, morphisms of etale sheaves on `V.left`. -/
def homOverEquiv (V : X.Etale) :
    HomOver F G V ≃ ((res V.hom Λ).obj F ⟶ (res V.hom Λ).obj G) :=
  (presheafHomEquiv F.obj G.obj (overOf V)).trans
    { toFun := fun α => ⟨α⟩
      invFun := fun β => β.hom
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance (V : X.Etale) : Small.{u} (HomOver F G V) := by
  have h : IsGrothendieckAbelian.{u} (EtSh Λ V.left) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology V.left (ModuleCat.{u} Λ)
  have : LocallySmall.{u} (EtSh Λ V.left) := h.locallySmall
  exact (small_congr (homOverEquiv F G V)).2 (@LocallySmall.hom_small _ _ this _ _)

/-- Restriction of `HomOver` along `f : V' ⟶ V` (the map of `presheafHom`), as a linear map. -/
def homOverMap {V V' : X.Etale} (f : V' ⟶ V) : HomOver F G V →ₗ[Λ] HomOver F G V' where
  toFun α := Functor.whiskerLeft (Over.map f).op α
  map_add' _ _ := NatTrans.ext (funext fun _ => rfl)
  map_smul' _ _ := NatTrans.ext (funext fun _ => rfl)

theorem homOverMap_id (V : X.Etale) (α : HomOver F G V) : homOverMap F G (𝟙 V) α = α :=
  ConcreteCategory.congr_hom ((presheafHom F.obj G.obj).map_id (op V)) α

theorem homOverMap_comp {V V' V'' : X.Etale} (f : V' ⟶ V) (g : V'' ⟶ V') (α : HomOver F G V) :
    homOverMap F G (g ≫ f) α = homOverMap F G g (homOverMap F G f α) :=
  ConcreteCategory.congr_hom ((presheafHom F.obj G.obj).map_comp f.op g.op) α

/-- A linear map transported to the `Shrink`s. -/
def shrinkMap {A B : Type*} [AddCommGroup A] [Module Λ A] [Small.{u} A] [AddCommGroup B]
    [Module Λ B] [Small.{u} B] (φ : A →ₗ[Λ] B) : Shrink.{u} A →ₗ[Λ] Shrink.{u} B :=
  (Shrink.linearEquiv Λ B).symm.toLinearMap ∘ₗ φ ∘ₗ (Shrink.linearEquiv Λ A).toLinearMap

theorem shrinkMap_apply {A B : Type*} [AddCommGroup A] [Module Λ A] [Small.{u} A] [AddCommGroup B]
    [Module Λ B] [Small.{u} B] (φ : A →ₗ[Λ] B) (x : Shrink.{u} A) :
    shrinkMap φ x = (Shrink.linearEquiv Λ B).symm (φ (Shrink.linearEquiv Λ A x)) := rfl

/-- `forget ⋙ uliftFunctor` reflects limits indexed by large categories (`Type (u+1)`): such a
limit of `Λ`-modules exists once its sections are `u`-small, which a limit cone in `Type (u+1)`
guarantees. This replaces `isSheaf_iff_isSheaf_forget` on the large etale site. -/
instance reflectsLimit_forgetUlift {J : Type (u + 1)} [Category.{u} J] (K : J ⥤ ModuleCat.{u} Λ) :
    ReflectsLimit K (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u}) where
  reflects {c} hc := by
    have hp : Small.{u} ((forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u}).mapCone c).pt :=
      small_ulift _
    have : Small.{u} (K ⋙ forget (ModuleCat.{u} Λ)).sections :=
      @small_map _ _ hp ((Types.sectionsEquiv (K ⋙ forget (ModuleCat.{u} Λ))).trans
        (Types.isLimitEquivSections hc).symm)
    have : PreservesLimit K (forget (ModuleCat.{u} Λ)) :=
      preservesLimit_of_preserves_limit_cone (ModuleCat.HasLimits.limitConeIsLimit K)
        (Types.Small.limitConeIsLimit (K ⋙ forget _))
    have := reflectsLimit_of_reflectsIsomorphisms K
      (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})
    exact ⟨isLimitOfReflects _ hc⟩

instance reflectsLimitsOfShape_forgetUlift (J : Type (u + 1)) [Category.{u} J] :
    ReflectsLimitsOfShape J (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u}) where

instance reflectsLimitsOfSize_forgetUlift :
    ReflectsLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u}) where

/-- The internal Hom presheaf, with values shrunk to `Type u`. -/
def homPre : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj V := ModuleCat.of Λ (Shrink.{u} (HomOver F G V.unop))
  map f := ModuleCat.ofHom (shrinkMap (homOverMap F G f.unop))
  map_id V := ModuleCat.hom_ext (LinearMap.ext fun x => by
    change shrinkMap (homOverMap F G (𝟙 V.unop)) x = x
    rw [shrinkMap_apply, homOverMap_id]
    exact (Shrink.linearEquiv Λ _).symm_apply_apply x)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x => by
    change shrinkMap (homOverMap F G (g.unop ≫ f.unop)) x =
      shrinkMap (homOverMap F G g.unop) (shrinkMap (homOverMap F G f.unop) x)
    rw [shrinkMap_apply, shrinkMap_apply, shrinkMap_apply, homOverMap_comp,
      LinearEquiv.apply_symm_apply])

theorem isSheaf_homPre : Presheaf.IsSheaf X.smallEtaleTopology (homPre F G) := by
  have key : Presieve.IsSheaf X.smallEtaleTopology
      (homPre F G ⋙ forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u}) := by
    refine (Presieve.isSheaf_iff_of_nat_equiv (P₂ := presheafHom F.obj G.obj)
      (fun ⦃V⦄ => (Equiv.ulift.trans (equivShrink (HomOver F G V)).symm)) ?_).2
      ((isSheaf_iff_isSheaf_of_type (J := X.smallEtaleTopology)
        (P := presheafHom F.obj G.obj)).1 (Presheaf.IsSheaf.hom F.obj G.obj G.property))
    intro V V' f x
    change (equivShrink (HomOver F G V)).symm (equivShrink (HomOver F G V)
      (homOverMap F G f ((equivShrink (HomOver F G V')).symm x.down))) =
        homOverMap F G f ((equivShrink (HomOver F G V')).symm x.down)
    exact Equiv.symm_apply_apply _ _
  exact Presheaf.isSheaf_of_isSheaf_comp X.smallEtaleTopology (homPre F G)
    (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})
    ((isSheaf_iff_isSheaf_of_type (J := X.smallEtaleTopology)
      (P := homPre F G ⋙ forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})).2 key)

/-- **The internal Hom** `Hom(F, G)` of etale sheaves: its sections over `V` are `Hom(F|_V, G|_V)`. -/
def homSh : EtSh Λ X := ⟨homPre F G, isSheaf_homPre F G⟩

/-- **The dual** `F^∨ = Hom(F, Λ_X)`. -/
abbrev dualSh : EtSh Λ X := homSh F (unitSh Λ X)

/-- Sections of `Hom(F, G)` over `V` are `Hom(F|_V, G|_V)`. -/
def homShSec (V : X.Etale) : (homSh F G).obj.obj (op V) ≃ₗ[Λ] HomOver F G V :=
  Shrink.linearEquiv Λ _

end RamanujanPetersson.EtSheaves


