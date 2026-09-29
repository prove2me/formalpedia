-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesRestrictOpen
-- name    : AlgebraicGeometry_ModulesRestrictOpen
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/417e92ff-3ba7-511f-a04f-a6223bdc68bb
-- title:
--   Restricting presheaves and sheaves of modules to an open subscheme
-- statement:
--   The first half works at the level of presheaves of modules over a presheaf of rings. For functors $F, G : C \to D$, presheaves of rings $T$ on $C$ and $S$ on $D$, and a scalar map $\varphi : T \to G^{\mathrm{op}} \cdot S$, `pushforwardNatTrans φ α` attaches to a natural transformation $\alpha : F \to G$ a natural transformation from the pushforward along $G$ determined by $\varphi$ to the pushforward along $F$ determined by $\varphi$ composed with $S(\alpha)$; on a presheaf of modules $M$ and an object $U$ it is the transition map $M(GU) \to M(FU)$ induced by $\alpha_U$, viewed through restriction of scalars, and the accompanying simp lemma records exactly this on elements. `pushforwardCongr` turns an equality $\varphi = \psi$ of scalar maps into an isomorphism of the two pushforward functors, acting as the identity on sections. `pushforwardPushforwardAdj` is the main presheaf-level construction: given an adjunction $F \dashv G$ with $F : C \to D$, $G : D \to C$, scalar maps $\varphi : S \to F^{\mathrm{op}} \cdot R$ and $\psi : R \to G^{\mathrm{op}} \cdot S$, and two compatibility hypotheses expressing that the counit and unit of $F \dashv G$ are compatible with $\varphi$ and $\psi$, it produces an adjunction `pushforward φ ⊣ pushforward ψ`; the two lemmas following it give its unit and counit on sections as the maps induced by the counit, respectively unit, of the adjunction.
--
--   The second half specialises this to an open $U$ of a scheme $X$ with inclusion $j = U.\iota$. Since $\mathcal{O}_U(V) = \mathcal{O}_X(j(V))$, the scalar map `restrictPresheafRingHom` is the identity, and `restrictPresheaf U` is the pushforward of presheaves of modules along the functor $V \mapsto j(V)$ on opens: it sends $P$ to $V \mapsto P(j(V))$, an equality of underlying types recorded in `restrictPresheaf_obj_obj`. `restrictPresheaf₀` is the same functor described without the (identity) restriction of scalars, identified with it by a reflexive isomorphism. Applying the presheaf adjunction to the adjunction between the image and preimage functors of the open embedding yields `restrictPresheafAdj`, the adjunction between restriction to $U$ and the presheaf direct image along $j$; uniqueness of left adjoints then gives `pullbackPresheafIsoRestrictPresheaf`, identifying restriction with the inverse image of presheaves of modules along $j$. Whiskering this with Mathlib's comparison of sheafification and pullback gives `sheafificationCompPullbackIso`, the statement that sheafification commutes with restriction to $U$: $(P^{\#})|_U \cong (P|_U)^{\#}$, naturally in $P$. On sheaves, `restrictOpen U`: $X.\mathrm{Modules} \to U.\mathrm{Modules}$ is the corresponding pushforward of sheaves of modules, whose underlying presheaf is `restrictPresheaf U` applied to the underlying presheaf, and it is identified with the restriction functor and with the pullback along $j$ by `restrictOpenIsoRestrictFunctor` and `restrictOpenIsoPullback`.
--
--   **Relation to Mathlib.** `pushforwardPushforwardAdj` and its auxiliary constructions are the presheaf-of-modules analogue of Mathlib's adjunction between pushforwards of sheaves of modules; the scheme-level definitions are phrased so as to be compared, by the isomorphisms constructed here, with Mathlib's restriction and pullback functors for sheaves of modules on schemes and with Mathlib's compatibility of sheafification with pullback.
--
--   **Where it is used.** Restriction to an open and its compatibility with sheafification allow constructions of sheaves of modules performed section by section and then sheafified (tensor products, symmetric and exterior powers) to be computed after restriction to an open, so that local properties such as being invertible or locally free of given rank can be verified on a cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesRestrictOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor

namespace PresheafOfModules

section NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G H : C ⥤ D} {T : Cᵒᵖ ⥤ RingCat.{u}} {S : Dᵒᵖ ⥤ RingCat.{u}}
  (φ : T ⟶ G.op ⋙ S)

set_option backward.isDefEq.respectTransparency false in

noncomputable def pushforwardNatTrans (α : F ⟶ G) :
    pushforward.{v} φ ⟶ pushforward.{v} (F := F) (φ ≫ whiskerRight (NatTrans.op α) S) where
  app M :=
  { app U := (ModuleCat.restrictScalars (φ.app U).hom).map (M.map (α.app U.unop).op)
    naturality {U V} i := by
      ext x
      dsimp
      change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app V.unop).op) _ =
        (M.presheaf.map (α.app U.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext U x
    exact congr($(f.naturality (α.app U.unop).op) x).symm

@[simp] lemma pushforwardNatTrans_app_app_apply (α : F ⟶ G) (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardNatTrans φ α).app M).app U x = M.map (α.app U.unop).op x := rfl

noncomputable def pushforwardCongr {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun M ↦ isoMk (fun U ↦ (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ ↦ by subst e; rfl) fun _ ↦ by subst e; rfl

@[simp] lemma pushforwardCongr_hom_app_app_apply {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ)
    (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardCongr e).hom.app M).app U x = x := by subst e; rfl

@[simp] lemma pushforwardCongr_inv_app_app_apply {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ)
    (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardCongr e).inv.app M).app U x = x := by subst e; rfl

end NatTrans

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (adj : F ⊣ G) (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
  (H₁ : whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)

set_option backward.isDefEq.respectTransparency false in

noncomputable def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit :=
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components X := by
    ext U x
    change (X.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      X.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    dsimp only [id_obj]
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components]
    simp
  right_triangle_components X := by
    ext U x
    change (X.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      X.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
    simp

lemma pushforwardPushforwardAdj_unit_app_app_apply (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).app U x =
      M.map (adj.counit.app U.unop).op x := rfl

lemma pushforwardPushforwardAdj_counit_app_app_apply (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).app U x =
      M.map (adj.unit.app U.unop).op x := rfl

end Adjunction

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}} (U : X.Opens)

noncomputable def restrictPresheafRingHom :
    (U : Scheme.{u}).ringCatSheaf.obj ⟶ U.ι.opensFunctor.op ⋙ X.ringCatSheaf.obj := 𝟙 _

noncomputable def restrictPresheaf : X.PresheafOfModules ⥤ (U : Scheme.{u}).PresheafOfModules :=
  PresheafOfModules.pushforward.{u} (restrictPresheafRingHom U)

noncomputable def restrictPresheaf₀ : X.PresheafOfModules ⥤ (U : Scheme.{u}).PresheafOfModules :=
  PresheafOfModules.pushforward₀.{u} U.ι.opensFunctor X.ringCatSheaf.obj

noncomputable def restrictPresheafIsoRestrictPresheaf₀ : restrictPresheaf U ≅ restrictPresheaf₀ U := Iso.refl _

lemma restrictPresheaf_obj_obj (P : X.PresheafOfModules) (V : (U : Scheme.{u}).Opensᵒᵖ) :
    (((restrictPresheaf U).obj P).obj V : Type u) = P.obj (Opposite.op (U.ι ''ᵁ V.unop)) := rfl

noncomputable def restrictPresheafAdj :
    restrictPresheaf U ⊣ PresheafOfModules.pushforward.{u} U.ι.toRingCatSheafHom.hom := by
  refine PresheafOfModules.pushforwardPushforwardAdj
    (by exact U.ι.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext V x; rfl
  · ext V x
    change (X.presheaf.map _ ≫ X.presheaf.map _) x = x
    rw [← Functor.map_comp]
    exact congr($(X.presheaf.map_id _) x)

noncomputable def pullbackPresheafIsoRestrictPresheaf :
    PresheafOfModules.pullback.{u} U.ι.toRingCatSheafHom.hom ≅ restrictPresheaf U :=
  Adjunction.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction _)
    (restrictPresheafAdj U)

noncomputable def sheafificationCompPullbackIso :
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙ Modules.pullback U.ι ≅
      restrictPresheaf U ⋙ PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj) :=
  SheafOfModules.sheafificationCompPullback U.ι.toRingCatSheafHom ≪≫
    isoWhiskerRight (pullbackPresheafIsoRestrictPresheaf U) _

noncomputable def restrictOpen : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward.{u} (F := U.ι.opensFunctor) ⟨restrictPresheafRingHom U⟩

lemma restrictOpen_obj_val (M : X.Modules) :
    ((restrictOpen U).obj M).val = (restrictPresheaf U).obj M.val := rfl

noncomputable def restrictOpenIsoRestrictFunctor : restrictOpen U ≅ Modules.restrictFunctor U.ι :=
  SheafOfModules.pushforwardCongr (by
    ext V x
    change x = (U.ι.appIso V.unop).inv x
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl)

noncomputable def restrictOpenIsoPullback : restrictOpen U ≅ Modules.pullback U.ι :=
  restrictOpenIsoRestrictFunctor U ≪≫ Modules.restrictFunctorIsoPullback U.ι

end AlgebraicGeometry.Scheme.Modules


