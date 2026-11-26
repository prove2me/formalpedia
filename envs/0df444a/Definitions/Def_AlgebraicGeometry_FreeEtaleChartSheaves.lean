-- Prove2me | Definitions.Def_AlgebraicGeometry_FreeEtaleChartSheaves
-- name    : AlgebraicGeometry_FreeEtaleChartSheaves
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T23:57:54.764215+00:00
-- url     : https://prove2.me/theorems/86b5e441-273f-4a62-9148-b0731db9b919
-- title:
--   Free sheaves on affine étale charts
-- statement:
--   Free sheaves on étale charts commute with base change and admit explicit chart maps.
-- source:
--   Stacks Project, 59.73.2 (https://stacks.math.columbia.edu/tag/03SA) and 59.74.4 (https://stacks.math.columbia.edu/tag/09Z7).

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitGlobalSections
import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleDirectImageSectionGerms
import Definitions.Def_AlgebraicGeometry_IntegralFiniteSurjectiveDiagram
import Mathlib.CategoryTheory.Generator.Presheaf
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Sites.ConstantSheaf

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleClosedPushforward (pushforward)

namespace PhilipponEtaleBoundedFiniteModelReduction

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- A sheaf embeds in the direct image of a bounded finite constant
sheaf along a finite morphism of finite presentation. -/
def boundedFiniteModel (X : Scheme.{u}) (N : ℕ) : ObjectProperty (Ab X) := fun F =>
  ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : LocallyOfFinitePresentation p)
    (M : AddCommGrpCat.{u}) (_ : Finite M), N • 𝟙 M = 0 ∧
      ∃ m : F ⟶ (pushforward p).obj ((constantSheaf Y.smallEtaleTopology
        AddCommGrpCat.{u}).obj M), Mono m

end PhilipponEtaleBoundedFiniteModelReduction

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponFreeYonedaMaps

universe v v' u u'

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [HasCoproducts.{v} A]

/-- The map of free representables induced by a map of representing
objects and a map of coefficients. -/
def mapFreeYoneda {U V : C} {M N : A} (a : U ⟶ V) (m : M ⟶ N) :
    Presheaf.freeYoneda U M ⟶ Presheaf.freeYoneda V N :=
  Presheaf.freeYonedaHomEquiv.symm
    (m ≫ Sigma.ι (fun (_ : (yoneda.obj V).obj (op U)) => N) a)

@[reassoc]
theorem ι_mapFreeYoneda_app {U V W : C} {M N : A} (a : U ⟶ V) (m : M ⟶ N) (b : W ⟶ U) :
    Sigma.ι (fun (_ : (yoneda.obj U).obj (op W)) => M) b ≫ (mapFreeYoneda a m).app (op W) =
      m ≫ Sigma.ι (fun (_ : (yoneda.obj V).obj (op W)) => N) (b ≫ a) := by
  change Sigma.ι _ b ≫ Sigma.desc _ = _
  rw [Sigma.ι_desc]
  change (m ≫ Sigma.ι (fun (_ : (yoneda.obj V).obj (op U)) => N) a) ≫ Sigma.map'
    (f := fun (_ : (yoneda.obj V).obj (op U)) => N)
    (g := fun (_ : (yoneda.obj V).obj (op W)) => N)
    ((yoneda.obj V).map b.op) (fun _ => 𝟙 N) = _
  rw [Category.assoc, Sigma.ι_comp_map']
  change m ≫ 𝟙 N ≫ Sigma.ι (fun (_ : (yoneda.obj V).obj (op W)) => N) (b ≫ a) = _
  rw [Category.id_comp]

/-- Under the free-representable adjunction, precomposition restricts
along the chart map and precomposes with the coefficient map. -/
theorem homEquiv_mapFreeYoneda_comp {U V : C} {M N : A} (a : U ⟶ V) (m : M ⟶ N)
    {F : Cᵒᵖ ⥤ A} (k : Presheaf.freeYoneda V N ⟶ F) :
    Presheaf.freeYonedaHomEquiv (mapFreeYoneda a m ≫ k) =
      m ≫ Presheaf.freeYonedaHomEquiv k ≫ F.map a.op := by
  rw [Presheaf.freeYonedaHomEquiv_comp, mapFreeYoneda, Equiv.apply_symm_apply]
  let B (W : C) (_ : (yoneda.obj V).obj (op W)) := N
  have h := congrArg (fun t => Sigma.ι (B V) (𝟙 V) ≫ t) (k.naturality a.op)
  change Sigma.ι (B V) (𝟙 V) ≫
      Sigma.map' ((yoneda.obj V).map a.op) (fun _ => 𝟙 N) ≫ k.app (op U) =
    Sigma.ι (B V) (𝟙 V) ≫ k.app (op V) ≫ F.map a.op at h
  simp only [Sigma.ι_comp_map'_assoc] at h
  change 𝟙 N ≫ Sigma.ι (B U) (a ≫ 𝟙 V) ≫ k.app (op U) = _ at h
  rw [Category.id_comp, Category.comp_id] at h
  rw [Category.assoc]
  change m ≫ Sigma.ι (B U) a ≫ k.app (op U) =
    m ≫ (Sigma.ι (B V) (𝟙 V) ≫ k.app (op V)) ≫ F.map a.op
  rw [Category.assoc (Sigma.ι (B V) (𝟙 V))]
  exact congrArg (m ≫ ·) h

end PhilipponFreeYonedaMaps

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 650000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponFreeYonedaMaps (mapFreeYoneda homEquiv_mapFreeYoneda_comp)


namespace PhilipponFreeEtaleSheaf

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- The sheaf freely generated by an étale chart with coefficients M. -/
def freeSheaf {X : Scheme.{u}} (U : X.Etale) (M : AddCommGrpCat.{u}) : Ab X :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (Presheaf.freeYoneda U M)

/-- Maps from a free étale sheaf are coefficient-valued maps into the
target's sections over the generating chart. -/
def homEquiv {X : Scheme.{u}} (U : X.Etale) (M : AddCommGrpCat.{u}) (F : Ab X) :
    (freeSheaf U M ⟶ F) ≃ (M ⟶ F.obj.obj (op U)) :=
  ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}).homEquiv
    (Presheaf.freeYoneda U M) F).trans Presheaf.freeYonedaHomEquiv

@[reassoc]
theorem homEquiv_comp {X : Scheme.{u}} (U : X.Etale) (M : AddCommGrpCat.{u}) {F G : Ab X}
    (a : freeSheaf U M ⟶ F) (b : F ⟶ G) :
    homEquiv U M G (a ≫ b) = homEquiv U M F a ≫ b.hom.app (op U) := by
  let P := Presheaf.freeYoneda U M
  let A := sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}
  have h : A.homEquiv P G (a ≫ b) = A.homEquiv P F a ≫ b.hom :=
    A.homEquiv_naturality_right a b
  exact (congrArg (fun k => Presheaf.freeYonedaHomEquiv k) h).trans
    (Presheaf.freeYonedaHomEquiv_comp (A.homEquiv P F a) b.hom)

/-- The map on free sheaves induced by a chart map and a coefficient map. -/
def mapFreeSheaf {X : Scheme.{u}} {U V : X.Etale} {M N : AddCommGrpCat.{u}}
    (a : U ⟶ V) (m : M ⟶ N) : freeSheaf U M ⟶ freeSheaf V N :=
  (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map (mapFreeYoneda a m)

theorem homEquiv_mapFreeSheaf_comp {X : Scheme.{u}} {U V : X.Etale} {M N : AddCommGrpCat.{u}}
    (a : U ⟶ V) (m : M ⟶ N) {F : Ab X} (k : freeSheaf V N ⟶ F) :
    homEquiv U M F (mapFreeSheaf a m ≫ k) = m ≫ homEquiv V N F k ≫ F.obj.map a.op := by
  let A := sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u}
  let L := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  change Presheaf.freeYonedaHomEquiv (A.homEquiv _ F (L.map (mapFreeYoneda a m) ≫ k)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact homEquiv_mapFreeYoneda_comp a m (A.homEquiv _ F k)

@[simp]
theorem mapFreeSheaf_id {X : Scheme.{u}} (U : X.Etale) (M : AddCommGrpCat.{u}) :
    mapFreeSheaf (𝟙 U) (𝟙 M) = 𝟙 (freeSheaf U M) := by
  apply (homEquiv U M (freeSheaf U M)).injective
  rw [← Category.comp_id (mapFreeSheaf (𝟙 U) (𝟙 M)), homEquiv_mapFreeSheaf_comp,
    Category.id_comp, op_id, (freeSheaf U M).obj.map_id (op U), Category.comp_id]

@[reassoc]
theorem mapFreeSheaf_comp {X : Scheme.{u}} {U V W : X.Etale} {M N P : AddCommGrpCat.{u}}
    (a : U ⟶ V) (b : V ⟶ W) (m : M ⟶ N) (n : N ⟶ P) :
    mapFreeSheaf a m ≫ mapFreeSheaf b n = mapFreeSheaf (a ≫ b) (m ≫ n) := by
  apply (homEquiv U M (freeSheaf W P)).injective
  rw [homEquiv_mapFreeSheaf_comp, ← Category.comp_id (mapFreeSheaf b n),
    homEquiv_mapFreeSheaf_comp, ← Category.comp_id (mapFreeSheaf (a ≫ b) (m ≫ n)),
    homEquiv_mapFreeSheaf_comp, op_comp, Functor.map_comp]
  simp only [Category.assoc]

private def pullbackHomEquiv {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Etale)
    (M : AddCommGrpCat.{u}) (G : Ab Y) : ((pullbackSheaves f).obj (freeSheaf U M) ⟶ G) ≃
      (M ⟶ G.obj.obj (op ((baseChange f).obj U))) :=
  ((pullbackAdjunction f).homEquiv (freeSheaf U M) G).trans (homEquiv U M ((pushforward f).obj G))

private theorem pullbackHomEquiv_comp {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Etale)
    (M : AddCommGrpCat.{u}) {G H : Ab Y} (k : (pullbackSheaves f).obj (freeSheaf U M) ⟶ G)
    (a : G ⟶ H) : pullbackHomEquiv f U M H (k ≫ a) =
      pullbackHomEquiv f U M G k ≫ a.hom.app (op ((baseChange f).obj U)) := by
  dsimp only [pullbackHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  exact homEquiv_comp U M _ ((pushforward f).map a)

/-- Pullback of a free étale sheaf is the free sheaf of the base-changed chart. -/
def pullbackFreeSheafIso {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Etale) (M : AddCommGrpCat.{u}) :
    (pullbackSheaves f).obj (freeSheaf U M) ≅ freeSheaf ((baseChange f).obj U) M := by
  let V := (baseChange f).obj U
  let P := (pullbackSheaves f).obj (freeSheaf U M)
  let Q := freeSheaf V M
  let α := pullbackHomEquiv f U M
  let β := homEquiv V M
  let u : P ⟶ Q := (α Q).symm (β Q (𝟙 Q))
  let v : Q ⟶ P := (β P).symm (α P (𝟙 P))
  have hu : α Q u = β Q (𝟙 Q) := Equiv.apply_symm_apply _ _
  have hv : β P v = α P (𝟙 P) := Equiv.apply_symm_apply _ _
  refine ⟨u, v, (α P).injective ?_, (β Q).injective ?_⟩
  · change pullbackHomEquiv f U M P (u ≫ v) = α P (𝟙 P)
    rw [pullbackHomEquiv_comp, show pullbackHomEquiv f U M Q u = β Q (𝟙 Q) from hu]
    exact (homEquiv_comp V M (𝟙 Q) v).symm.trans
      ((congrArg (homEquiv V M P) (Category.id_comp v)).trans hv)
  · change homEquiv V M Q (v ≫ u) = β Q (𝟙 Q)
    rw [homEquiv_comp, show homEquiv V M P v = α P (𝟙 P) from hv]
    exact (pullbackHomEquiv_comp f U M (𝟙 P) u).symm.trans
      ((congrArg (pullbackHomEquiv f U M Q) (Category.id_comp u)).trans hu)

private theorem pullbackHomEquiv_iso_comp {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Etale)
    (M : AddCommGrpCat.{u}) {G : Ab Y} (k : freeSheaf ((baseChange f).obj U) M ⟶ G) :
    pullbackHomEquiv f U M G ((pullbackFreeSheafIso f U M).hom ≫ k) =
      homEquiv ((baseChange f).obj U) M G k := by
  rw [pullbackHomEquiv_comp]
  change (pullbackHomEquiv f U M _ ((pullbackHomEquiv f U M _).symm (homEquiv _ M _ (𝟙 _)))) ≫
    k.hom.app _ = _
  rw [Equiv.apply_symm_apply, ← homEquiv_comp, Category.id_comp]

/-- The free-sheaf pullback isomorphism respects both chart maps and
coefficient maps. -/
theorem pullbackFreeSheafIso_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) {U V : X.Etale}
    {M N : AddCommGrpCat.{u}} (a : U ⟶ V) (m : M ⟶ N) :
    (pullbackSheaves f).map (mapFreeSheaf a m) ≫ (pullbackFreeSheafIso f V N).hom =
      (pullbackFreeSheafIso f U M).hom ≫ mapFreeSheaf ((baseChange f).map a) m := by
  apply (pullbackHomEquiv f U M _).injective
  rw [pullbackHomEquiv_iso_comp]
  have h₁ : ∀ {G : Ab Y} (k : (pullbackSheaves f).obj (freeSheaf V N) ⟶ G),
      pullbackHomEquiv f U M G ((pullbackSheaves f).map (mapFreeSheaf a m) ≫ k) =
        m ≫ pullbackHomEquiv f V N G k ≫ G.obj.map ((baseChange f).map a).op := by
    intro G k
    dsimp only [pullbackHomEquiv, Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left]
    exact homEquiv_mapFreeSheaf_comp a m _
  rw [h₁, ← Category.comp_id (pullbackFreeSheafIso f V N).hom, pullbackHomEquiv_iso_comp]
  rw [← Category.comp_id (mapFreeSheaf ((baseChange f).map a) m), homEquiv_mapFreeSheaf_comp]

/-- Isomorphic étale charts give isomorphic free coefficient sheaves. -/
def freeSheafIsoOfChartIso {X : Scheme.{u}} {U V : X.Etale}
    (b : U ≅ V) (M : AddCommGrpCat.{u}) : freeSheaf U M ≅ freeSheaf V M where
  hom := mapFreeSheaf b.hom (𝟙 M)
  inv := mapFreeSheaf b.inv (𝟙 M)
  hom_inv_id := by rw [mapFreeSheaf_comp, b.hom_inv_id, Category.id_comp, mapFreeSheaf_id]
  inv_hom_id := by rw [mapFreeSheaf_comp, b.inv_hom_id, Category.id_comp, mapFreeSheaf_id]

/-- A commutative square of chart morphisms with vertical isomorphisms
induces a commutative square of free sheaves. -/
theorem freeSheafIsoOfChartIso_naturality {X : Scheme.{u}} {U V U' V' : X.Etale}
    {M N : AddCommGrpCat.{u}} (e : U ≅ U') (e' : V ≅ V') (a : U ⟶ V) (b : U' ⟶ V')
    (m : M ⟶ N) (h : a ≫ e'.hom = e.hom ≫ b) :
    mapFreeSheaf a m ≫ (freeSheafIsoOfChartIso e' N).hom =
      (freeSheafIsoOfChartIso e M).hom ≫ mapFreeSheaf b m := by
  change mapFreeSheaf a m ≫ mapFreeSheaf e'.hom (𝟙 N) =
    mapFreeSheaf e.hom (𝟙 M) ≫ mapFreeSheaf b m
  rw [mapFreeSheaf_comp, mapFreeSheaf_comp, h, Category.comp_id, Category.id_comp]

/-- The free sheaf of the terminal chart is the constant coefficient sheaf. -/
def freeSheafTerminalIso (X : Scheme.{u}) (M : AddCommGrpCat.{u}) :
    freeSheaf (Scheme.Etale.mk (𝟙 X)) M ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M := by
  let T := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T :=
    IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let A := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT
  let e : coyoneda.obj (op (freeSheaf T M)) ≅ coyoneda.obj (op (C.obj M)) :=
    NatIso.ofComponents (fun G => ((homEquiv T M G).trans (A.homEquiv M G).symm).toIso) (by
      intro G H a
      apply ConcreteCategory.hom_ext
      intro h
      change (A.homEquiv M H).symm (homEquiv T M H (h ≫ a)) =
        (A.homEquiv M G).symm (homEquiv T M G h) ≫ a
      apply (A.homEquiv M H).injective
      rw [Equiv.apply_symm_apply, homEquiv_comp, A.homEquiv_naturality_right]
      change _ = (A.homEquiv M G) ((A.homEquiv M G).symm (homEquiv T M G h)) ≫ a.hom.app (op T)
      rw [Equiv.apply_symm_apply])
  exact (Coyoneda.fullyFaithful.preimageIso e).unop.symm

end PhilipponFreeEtaleSheaf

end

end


