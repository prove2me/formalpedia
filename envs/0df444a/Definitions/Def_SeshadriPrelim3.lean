-- Prove2me | Definitions.Def_SeshadriPrelim3
-- name    : SeshadriPrelim3
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T14:38:00.64668+00:00
-- url     : https://prove2.me/theorems/74a0aaad-5f4b-4913-b3bb-3081d947a3ae
-- title:
--   Maximal Seshadri constants: supporting development, part 3
-- statement:
--   Part 3 of 6 of the supporting Lean development for the maximal Seshadri constants theorem. It holds the definitions that the statements of the published child theorems refer to, in source order, together with the proved lemmas that their bodies and type class instances rely on. No result is assumed: every lemma here has a proof. Source modules: `Analytic.TaylorCoefficients`, `Blowup.ReesAlgebra`, `Cohomology.ExtCokernel`, `Cohomology.LaurentPlane`, `Cohomology.PlaneCechLinear`, `Cohomology.PlaneFreeCech`, `Cohomology.SheafExactness`, `Definitions`, `Interpolation.CompressionRanks`, `Interpolation.Moments`, `Nodal.NodalIntersection`, `Sheaves.Frames`, `Sheaves.LinePullback`, `Sheaves.OpenBaseChange`, `Sheaves.OpenPullbackUnit`, `Sheaves.SectionPullback`, `Sheaves.TensorFrames`.
--
--   **Formalization Note** Definitions of this development carry proof fields, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/AlgebraicGeometry/Seshadri` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`. Edits for the port: in `TildeExact.map_mono`, a block of 1 source line(s) is replaced by 2 line(s) (visible by diffing against upstream).
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim2

set_option linter.all false

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y Z : Scheme.{u}}
def O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def endValue (f : O X ⟶ O X) : Γ(X, ⊤) := f.app ⊤ (1 : Γ(X, ⊤))

lemma end_apply (f : O X ⟶ O X) (U : X.Opens) (a : Γ(X, U)) :
    f.app U a = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) := by
  have h := f.app_smul (r := a) (x := (1 : Γ(X, U)))
  change f.app U (a * 1 : Γ(X, U)) = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) at h
  simpa only [mul_one] using h

@[simp] lemma endValue_id : endValue (𝟙 (O X)) = 1 := rfl

lemma endValue_comp (f g : O X ⟶ O X) :
    endValue (f ≫ g) = endValue f * endValue g := by
  exact end_apply g ⊤ (endValue f)

def frameChange {M : X.Modules} (e f : M ≅ O X) : Γ(X, ⊤)ˣ where
  val := endValue (e.inv ≫ f.hom)
  inv := endValue (f.inv ≫ e.hom)
  val_inv := by rw [← endValue_comp]; simp
  inv_val := by rw [← endValue_comp]; simp

def coefficient {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) : Γ(X, ⊤) :=
  endValue (s ≫ e.hom)

lemma coefficient_change {M : X.Modules} (e f : M ≅ O X) (s : O X ⟶ M) :
    coefficient f s = (frameChange e f : Γ(X, ⊤)) * coefficient e s := by
  change endValue (s ≫ f.hom) = endValue (e.inv ≫ f.hom) * endValue (s ≫ e.hom)
  rw [mul_comm, ← endValue_comp]
  simp

lemma coefficient_frame {M : X.Modules} (e : M ≅ O X) : coefficient e e.inv = 1 := by
  simp [coefficient]

def restrictSection (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (s : O X ⟶ M) : O Y ⟶ M.restrict φ :=
  (Scheme.Modules.restrictUnitIso φ).inv ≫ (Scheme.Modules.restrictFunctor φ).map s

def restrictFrame (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) : M.restrict φ ≅ O Y :=
  (Scheme.Modules.restrictFunctor φ).mapIso e ≪≫ Scheme.Modules.restrictUnitIso φ

lemma end_naturality (f : O X ⟶ O X) (U : X.Opens) :
    f.app U (1 : Γ(X, U)) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) := by
  have h := CategoryTheory.congr_fun (f.mapPresheaf.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change f.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))) =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) at h
  simpa only [map_one] using h

lemma endValue_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] (f : O X ⟶ O X) :
    endValue (restrictSection φ f ≫ (Scheme.Modules.restrictUnitIso φ).hom) =
      φ.appTop (endValue f) := by
  change (φ.appIso ⊤).hom (f.app (φ ''ᵁ ⊤) ((φ.appIso ⊤).inv 1)) = _
  rw [map_one, end_naturality]
  change (X.presheaf.map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
    (φ.appIso ⊤).hom) (endValue f) = _
  rw [Scheme.Hom.appIso_hom']
  simp only [Scheme.Hom.appTop, Scheme.Hom.appLE,
    Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  congr 1
  rw [show ((Opens.map φ.base).map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op.unop).op ≫
      (homOfLE (show (⊤ : Y.Opens) ≤ φ ⁻¹ᵁ (φ ''ᵁ ⊤) from by intro x _; exact ⟨x, Set.mem_univ _, rfl⟩)).op = 𝟙 _ from Subsingleton.elim _ _]
  change ConcreteCategory.hom (φ.app ⊤ ≫ Y.presheaf.map (𝟙 (Opposite.op ⊤))) =
    ConcreteCategory.hom (φ.app ⊤)
  exact congrArg ConcreteCategory.hom
    ((congrArg (fun morphism => φ.app ⊤ ≫ morphism) (Y.presheaf.map_id _)).trans
      (Category.comp_id _))

lemma coefficient_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (restrictFrame φ e) (restrictSection φ s) = φ.appTop (coefficient e s) := by
  let restriction := Scheme.Modules.restrictFunctor φ
  let unitIso := Scheme.Modules.restrictUnitIso φ
  have composition :
      (unitIso.inv ≫ restriction.map s) ≫ restriction.map e.hom ≫ unitIso.hom =
        (unitIso.inv ≫ restriction.map (s ≫ e.hom)) ≫ unitIso.hom := by
    calc
      _ = unitIso.inv ≫ (restriction.map s ≫ restriction.map e.hom) ≫ unitIso.hom :=
        (Category.assoc _ _ _).trans
          (congrArg (fun morphism => unitIso.inv ≫ morphism)
            (Category.assoc _ _ _).symm)
      _ = unitIso.inv ≫ restriction.map (s ≫ e.hom) ≫ unitIso.hom :=
        congrArg (fun morphism => unitIso.inv ≫ morphism ≫ unitIso.hom)
          (restriction.map_comp s e.hom).symm
      _ = _ := (Category.assoc _ _ _).symm
  exact (congrArg endValue composition).trans (endValue_restrict φ (s ≫ e.hom))

lemma restrictUnit_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] :
    (Scheme.Modules.restrictUnitIso (φ ≫ ψ)).inv ≫
      (Scheme.Modules.restrictFunctorComp φ ψ).hom.app (O Z) =
    (Scheme.Modules.restrictUnitIso φ).inv ≫
      (Scheme.Modules.restrictFunctor φ).map (Scheme.Modules.restrictUnitIso ψ).inv := by
  ext U a
  change Z.presheaf.map (eqToHom (show ψ ''ᵁ (φ ''ᵁ U) = (φ ≫ ψ) ''ᵁ U from by simp)).op
    ((φ ≫ ψ).appIso U |>.inv |>.hom |>.toFun <| a) =
      (ψ.appIso (φ ''ᵁ U)).inv ((φ.appIso U).inv a)
  rw [Scheme.Hom.comp_appIso]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv]
  change ( (φ.appIso U).inv ≫ (ψ.appIso (φ ''ᵁ U)).inv ≫
    Z.presheaf.map _ ≫ Z.presheaf.map _) a = _
  rw [← CategoryTheory.Functor.map_comp]
  simp
  rfl

lemma restrictSection_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules} (s : O Z ⟶ M) :
    restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M =
      restrictSection φ (restrictSection ψ s) := by
  let first := Scheme.Modules.restrictFunctor φ
  let second := Scheme.Modules.restrictFunctor ψ
  let combined := Scheme.Modules.restrictFunctor (φ ≫ ψ)
  let comparison := (Scheme.Modules.restrictFunctorComp φ ψ).hom
  let unitIso := Scheme.Modules.restrictUnitIso (φ ≫ ψ)
  calc
    _ = unitIso.inv ≫ combined.map s ≫ comparison.app M := Category.assoc _ _ _
    _ = unitIso.inv ≫ comparison.app (O Z) ≫ (second ⋙ first).map s :=
      congrArg (fun morphism => unitIso.inv ≫ morphism) (comparison.naturality s)
    _ = (unitIso.inv ≫ comparison.app (O Z)) ≫ (second ⋙ first).map s :=
      (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.restrictUnitIso φ).inv ≫
        first.map (Scheme.Modules.restrictUnitIso ψ).inv) ≫ (second ⋙ first).map s :=
      congrArg (fun morphism => morphism ≫ (second ⋙ first).map s)
        (restrictUnit_comp φ ψ)
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun morphism => (Scheme.Modules.restrictUnitIso φ).inv ≫ morphism)
        (first.map_comp (Scheme.Modules.restrictUnitIso ψ).inv (second.map s)).symm)

lemma coefficient_transport {M N : X.Modules} (e : M ≅ N) (f : N ≅ O X)
    (s : O X ⟶ M) : coefficient (e ≪≫ f) s = coefficient f (s ≫ e.hom) := by
  simp only [coefficient, Iso.trans_hom, Category.assoc]

lemma coefficient_restrict_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules}
    (e : M.restrict ψ ≅ O X) (s : O Z ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctorComp φ ψ).app M ≪≫ restrictFrame φ e)
      (restrictSection (φ ≫ ψ) s) = φ.appTop (coefficient e (restrictSection ψ s)) := by
  rw [coefficient_transport]
  change coefficient (restrictFrame φ e)
    (restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M) = _
  rw [restrictSection_comp, coefficient_restrict]

lemma restrictSection_congr {φ ψ : Y ⟶ X} (h : φ = ψ)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : X.Modules} (s : O X ⟶ M) :
    restrictSection φ s ≫ (Scheme.Modules.restrictFunctorCongr h).hom.app M =
      restrictSection ψ s := by
  subst ψ
  have H : (Scheme.Modules.restrictFunctorCongr (show φ = φ from rfl)).hom.app M = 𝟙 _ := by
    ext U a
    simp
    rfl
  rw [H, Category.comp_id]

lemma overlap_coefficients {W : Scheme.{u}} (φ : Y ⟶ X) (ψ : Z ⟶ X)
    (a : W ⟶ Y) (b : W ⟶ Z) [IsOpenImmersion φ] [IsOpenImmersion ψ]
    [IsOpenImmersion a] [IsOpenImmersion b] (h : a ≫ φ = b ≫ ψ)
    {M : X.Modules} (e : M.restrict φ ≅ O Y) (f : M.restrict ψ ≅ O Z) :
    ∃ c : Γ(W, ⊤)ˣ, ∀ s : O X ⟶ M,
      b.appTop (coefficient f (restrictSection ψ s)) =
      (c : Γ(W, ⊤)) * a.appTop (coefficient e (restrictSection φ s)) := by
  let E : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorComp a φ).app M ≪≫ restrictFrame a e
  let F : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      (Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f
  refine ⟨frameChange E F, fun s => ?_⟩
  have H := coefficient_change E F (restrictSection (a ≫ φ) s)
  have hE : coefficient E (restrictSection (a ≫ φ) s) =
      a.appTop (coefficient e (restrictSection φ s)) := coefficient_restrict_comp a φ e s
  have hF : coefficient F (restrictSection (a ≫ φ) s) =
      b.appTop (coefficient f (restrictSection ψ s)) := by
    change coefficient ((Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      ((Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f)) _ = _
    rw [coefficient_transport]
    change coefficient _ (restrictSection (a ≫ φ) s ≫
      (Scheme.Modules.restrictFunctorCongr h).hom.app M) = _
    rw [restrictSection_congr]
    exact coefficient_restrict_comp b ψ f s
  rwa [hE, hF] at H

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

def scalarEnd (r : Γ(X, ⊤)) : O X ⟶ O X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma endValue_scalarEnd (r : Γ(X, ⊤)) : endValue (scalarEnd r) = r := by
  change X.presheaf.map (𝟙 _) r * 1 = r
  simp

end
end MaximalSeshadri.Frames

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {X Y : Scheme.{0}}

instance opensMap_final (f : Y ⟶ X) : (Opens.map f.base).Final := by
  let : PreservesLimit (Functor.empty.{0} X.Opens) (Opens.map f.base) := by
    apply preservesLimit_of_preserves_limit_cone (isTerminalTop (α := X.Opens))
    exact (isLimitMapConeEmptyConeEquiv (Opens.map f.base) (⊤ : X.Opens)).symm isTerminalTop
  infer_instance

def pullbackRestrictIso (f : Y ⟶ X) (L : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (L.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
  (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L ≪≫
  (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L ≪≫
  ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app L).symm ≪≫
  (Scheme.Modules.pullback (f ∣_ U)).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm

def LineBundle.pullback (L : LineBundle X) (f : Y ⟶ X) : LineBundle Y where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyRankOne y := by
    obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
    refine ⟨f ⁻¹ᵁ U,hy,⟨pullbackRestrictIso f L.sheaf U ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫ ?_⟩⟩
    letI : (Opens.map (f ∣_ U).base).Final := opensMap_final (f ∣_ U)
    letI : (SheafOfModules.pushforward (f ∣_ U).toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward (f ∣_ U)).IsRightAdjoint
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
        (F := Opens.map (f ∣_ U).base) (f ∣_ U).toRingCatSheafHom) :=
      SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
        (F := Opens.map (f ∣_ U).base) (f ∣_ U).toRingCatSheafHom
    let unitIso :=
      asIso (C := SheafOfModules (f ⁻¹ᵁ U).toScheme.ringCatSheaf)
        (SheafOfModules.pullbackObjUnitToUnit (F := Opens.map (f ∣_ U).base)
        (f ∣_ U).toRingCatSheafHom)
    exact
      { hom := unitIso.hom
        inv := unitIso.inv
        hom_inv_id := unitIso.hom_inv_id
        inv_hom_id := unitIso.inv_hom_id }

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.ExtCokernel
noncomputable section
open CategoryTheory CategoryTheory.Abelian
universe w v u t
variable {K : Type t} [CommRing K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C] {S : ShortComplex C}

def quotientEquiv (hS : S.ShortExact) (M : C)
    (hvan : ∀ x : Ext S.X₂ M 1, x = 0) :
    ((S.X₁ ⟶ M) ⧸ (LinearMap.range
      (Linear.leftComp K M S.f))) ≃ₗ[K] Ext S.X₃ M 1 := by
  let d : (S.X₁ ⟶ M) →ₗ[K] Ext S.X₃ M 1 :=
    (hS.extClass.precompOfLinear K M (add_zero 1)).comp Ext.linearEquiv₀.symm.toLinearMap
  have hd : Function.Surjective d := by
    intro x
    obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ hS M x (hvan _) (n₀ := 0) rfl
    refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
    change hS.extClass.comp (Ext.mk₀ (Ext.linearEquiv₀ (R := K) y)) (add_zero 1) = x
    rwa [Ext.mk₀_linearEquiv₀_apply]
  have hk : LinearMap.range (Linear.leftComp K M S.f) = d.ker := by
    ext f
    constructor
    · rintro ⟨g,rfl⟩
      change hS.extClass.comp (Ext.mk₀ (S.f ≫ g)) (add_zero 1) = 0
      rw [← Ext.mk₀_comp_mk₀]
      exact ShortComplex.ShortExact.extClass_comp_assoc hS _
    · intro hf
      change hS.extClass.comp (Ext.mk₀ f) (add_zero 1) = 0 at hf
      obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS M (Ext.mk₀ f) rfl hf
      refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
      apply (Ext.linearEquiv₀ (R := K)).symm.injective
      change Ext.mk₀ (S.f ≫ Ext.linearEquiv₀ (R := K) y) = Ext.mk₀ f
      simpa only [← Ext.mk₀_comp_mk₀,
        Ext.mk₀_linearEquiv₀_apply] using hy
  exact (Submodule.quotEquivOfEq _ _ hk).trans (d.quotKerEquivOfSurjective hd)

end
end MaximalSeshadri.ExtCokernel
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def cycles (A B C : Submodule K M) : Submodule K (A × B × C) :=
  LinearMap.ker
    ({ toFun := fun x => (x.1 : M) + (x.2.1 : M) + (x.2.2 : M)
       map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]; abel
       map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd,
        Submodule.coe_smul_of_tower, smul_add, RingHom.id_apply] } :
        (A × B × C) →ₗ[K] M)

def edgeAB (A B C : Submodule K M) : ↥(A ⊓ B) →ₗ[K] cycles A B C where
  toFun x := ⟨(⟨x,x.property.1⟩,⟨-x,B.neg_mem x.property.2⟩,0), by
    change (x : M) + -(x : M) + 0 = 0; simp⟩
  map_add' := by intros; ext <;> simp; all_goals abel
  map_smul' := by intros; ext <;> simp

def edgeAC (A B C : Submodule K M) : ↥(A ⊓ C) →ₗ[K] cycles A B C where
  toFun x := ⟨(⟨x,x.property.1⟩,0,⟨-x,C.neg_mem x.property.2⟩), by
    change (x : M) + 0 + -(x : M) = 0; simp⟩
  map_add' := by intros; ext <;> simp; all_goals abel
  map_smul' := by intros; ext <;> simp

def edgeBC (A B C : Submodule K M) : ↥(B ⊓ C) →ₗ[K] cycles A B C where
  toFun x := ⟨(0,⟨x,x.property.1⟩,⟨-x,C.neg_mem x.property.2⟩), by
    change 0 + (x : M) + -(x : M) = 0; simp⟩
  map_add' := by intros; ext <;> simp; all_goals abel
  map_smul' := by intros; ext <;> simp

def boundaries (A B C : Submodule K M)
    (N₀ : Submodule K ↥(A ⊓ B)) (N₁ : Submodule K ↥(A ⊓ C))
    (N₂ : Submodule K ↥(B ⊓ C)) : Submodule K (cycles A B C) :=
  N₀.map (edgeAB A B C) ⊔ N₁.map (edgeAC A B C) ⊔ N₂.map (edgeBC A B C)

end
end MaximalSeshadri.PlaneCech

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma restrict_unit_app {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) :
    ((Scheme.Modules.restrictAdjunction i).unit.app M).app W =
      M.presheaf.map (homOfLE (i.image_preimage_le W)).op := rfl

lemma restrict_unit_app_iso {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) (hW : W ≤ i.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction i).unit.app M).app W) := by
  rw [restrict_unit_app]
  have he : i ''ᵁ i ⁻¹ᵁ W = W := by
    rw [i.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  have hi : IsIso (homOfLE (i.image_preimage_le W)) :=
    homOfLE_isIso_of_eq _ he
  have : IsIso (homOfLE (i.image_preimage_le W)).op :=
    isIso_op (homOfLE (i.image_preimage_le W))
  exact M.presheaf.map_isIso (homOfLE (i.image_preimage_le W)).op

def rightSquare :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
      (Scheme.Modules.pushforwardComp _ _).symm

def hom (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ⟶
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M)) ≫
  (Scheme.Modules.restrictFunctor U.ι).map
    ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)) ≫
  (Scheme.Modules.restrictAdjunction U.ι).counit.app
    ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))

instance hom_isIso (M : X.Modules) : IsIso (hom f U M) := by
  have ha : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M))) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro W
    change IsIso (((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
      (f ⁻¹ᵁ (U.ι ''ᵁ W)))
    apply restrict_unit_app_iso
    rw [Scheme.Opens.opensRange_ι]
    apply (Opens.map f.base).monotone
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange W
  unfold hom
  infer_instance

def iso (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) := asIso (hom f U M)

end
end MaximalSeshadri.OpenBaseChange

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.LaurentPlane
noncomputable section

abbrev Ring (K : Type*) [CommRing K] := AddMonoidAlgebra K (ℤ × ℤ)

def T {K : Type*} [CommRing K] (z : ℤ × ℤ) : Ring K :=
  AddMonoidAlgebra.single z 1

@[simp] lemma T_zero {K : Type*} [CommRing K] : T (K := K) 0 = 1 := rfl

section Evaluation
variable {K R : Type*} [CommRing K] [CommRing R]

def monomials (u v : Rˣ) : Multiplicative (ℤ × ℤ) →* R where
  toFun z := ↑(u ^ z.toAdd.1 * v ^ z.toAdd.2)
  map_one' := by simp
  map_mul' z w := by
    change ↑(u ^ (z.toAdd.1 + w.toAdd.1) * v ^ (z.toAdd.2 + w.toAdd.2)) =
      (↑(u ^ z.toAdd.1 * v ^ z.toAdd.2) : R) * ↑(u ^ w.toAdd.1 * v ^ w.toAdd.2)
    simp only [zpow_add, Units.val_mul]
    ring

def eval (k : K →+* R) (u v : Rˣ) : Ring K →+* R :=
  AddMonoidAlgebra.liftNCRingHom k (monomials u v) (fun _ _ => .all _ _)

end Evaluation

variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (Ring K) M] [IsScalarTower K (Ring K) M]

end
end MaximalSeshadri.LaurentPlane

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def piece (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {p | (p : R[X]) = monomial n ((p : R[X]).coeff n)}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change (p : R[X]) + q = monomial n (((p : R[X]) + q).coeff n)
    rw [coeff_add, map_add, ← hp, ← hq]
  smul_mem' a p hp := by
    change a • (p : R[X]) = monomial n ((a • (p : R[X])).coeff n)
    rw [coeff_smul, map_smul, ← hp]

lemma mem_piece (n : ℕ) (p : reesAlgebra I) :
    p ∈ piece I n ↔ (p : R[X]) = monomial n ((p : R[X]).coeff n) := Iff.rfl

def component (n : ℕ) (p : reesAlgebra I) : piece I n :=
  ⟨⟨monomial n ((p : R[X]).coeff n), reesAlgebra.monomial_mem.mpr (p.property n)⟩,
    by simp [mem_piece]⟩

@[simp] lemma component_val (n : ℕ) (p : reesAlgebra I) :
    ((component I n p : reesAlgebra I) : R[X]) = monomial n ((p : R[X]).coeff n) := rfl

def components (p : reesAlgebra I) : ⨁ n, piece I n :=
  ⟨fun n => component I n p,
    Trunc.mk ⟨(p : R[X]).support.val, fun n => by
      classical
      by_cases hn : n ∈ (p : R[X]).support
      · exact Or.inl hn
      · right
        apply Subtype.ext
        apply Subtype.ext
        have hc : (p : R[X]).coeff n = 0 := notMem_support_iff.mp hn
        simp [component_val, hc]⟩⟩

@[simp] lemma components_apply (p : reesAlgebra I) (n : ℕ) :
    components I p n = component I n p := rfl

def componentsAdd : reesAlgebra I →+ ⨁ n, piece I n where
  toFun := components I
  map_zero' := by ext n : 1; apply Subtype.ext; apply Subtype.ext; simp [component_val]
  map_add' p q := by
    ext n : 1
    apply Subtype.ext
    apply Subtype.ext
    change monomial n (((p : R[X]) + q).coeff n) =
      monomial n ((p : R[X]).coeff n) + monomial n ((q : R[X]).coeff n)
    rw [coeff_add, map_add]

lemma piece_coeff_ne {n m : ℕ} (hnm : n ≠ m) (p : piece I n) :
    ((p : reesAlgebra I) : R[X]).coeff m = 0 := by
  rw [(mem_piece I n p.val).mp p.property, coeff_monomial, ite_eq_right hnm]

lemma components_of_piece (n : ℕ) (p : piece I n) :
    components I p.val = DirectSum.of (fun n => piece I n) n p := by
  ext m : 1
  by_cases h : n = m
  · subst m
    rw [DirectSum.of_eq_same]
    apply Subtype.ext
    apply Subtype.ext
    exact ((mem_piece I n p.val).mp p.property).symm
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
    apply Subtype.ext
    apply Subtype.ext
    simp [component_val, piece_coeff_ne I h p]

lemma recompose_components (p : reesAlgebra I) :
    DirectSum.coeAddMonoidHom (piece I) (components I p) = p := by
  let f := DirectSum.coeAddMonoidHom (piece I)
  have hc (n : ℕ) :
      ((Polynomial.lcoeff R n).toAddMonoidHom.comp
        ((reesAlgebra I).val.toAddMonoidHom.comp f)) =
      ((Polynomial.lcoeff R n).toAddMonoidHom.comp
        ((reesAlgebra I).val.toAddMonoidHom.comp
          ((piece I n).subtype.toAddMonoidHom.comp (DFinsupp.evalAddMonoidHom n)))) := by
    apply DirectSum.addHom_ext
    intro m a
    dsimp only [f]
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
    change ((a : reesAlgebra I) : R[X]).coeff n =
      (((DirectSum.of (fun i => piece I i) m a) n : reesAlgebra I) : R[X]).coeff n
    by_cases h : m = n
    · subst m
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), piece_coeff_ne I h a]
      rfl
  apply Subtype.ext
  ext n
  have h := DFunLike.congr_fun (hc n) (components I p)
  change ((f (components I p) : reesAlgebra I) : R[X]).coeff n =
    ((component I n p : reesAlgebra I) : R[X]).coeff n at h
  simpa only [component_val, coeff_monomial, ite_true] using h

instance gradedMonoid : SetLike.GradedMonoid (piece I) where
  one_mem := by simp [mem_piece]
  mul_mem {i j} {a b} ha hb := by
    change (a : R[X]) * b = monomial (i+j) (((a : R[X]) * b).coeff (i+j))
    rw [(mem_piece I i a).mp ha, (mem_piece I j b).mp hb,
      monomial_mul_monomial, coeff_monomial, ite_eq_left rfl]

instance grading : GradedAlgebra (piece I) where
  toGradedMonoid := gradedMonoid I
  decompose' := components I
  left_inv := recompose_components I
  right_inv := by
    have h : (componentsAdd I).comp (DirectSum.coeAddMonoidHom (piece I)) = .id _ := by
      apply DirectSum.addHom_ext
      intro n a
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      exact components_of_piece I n a
    exact DFunLike.congr_fun h

def affineBlowup : Scheme.{u} := Proj (piece I)

def zeroEquiv : R ≃+* piece I 0 :=
  RingEquiv.ofBijective (algebraMap R (piece I 0)) (by
    constructor
    · intro a b h
      have hp := congrArg (fun p : piece I 0 => ((p : reesAlgebra I) : R[X])) h
      exact Polynomial.C_injective hp
    · intro p
      refine ⟨((p : reesAlgebra I) : R[X]).coeff 0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (show ((p : reesAlgebra I) : R[X]) =
        C (((p : reesAlgebra I) : R[X]).coeff 0) by
          simpa only [monomial_zero_left] using (mem_piece I 0 p.val).mp p.property).symm)

def zeroIso : CommRingCat.of R ≅ CommRingCat.of (piece I 0) :=
  (zeroEquiv I).toCommRingCatIso

def projection : affineBlowup I ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom

instance : IsScalarTower R (piece I 0) (reesAlgebra I) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := piece I 0) (A := reesAlgebra I)
    (fun _ => rfl)

instance [IsNoetherianRing R] : Algebra.FiniteType (piece I 0) (reesAlgebra I) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R (piece I 0) (reesAlgebra I)

instance projection_proper [IsNoetherianRing R] : IsProper (projection I) := by
  have hP : IsProper (Proj.toSpecZero (piece I)) := inferInstance
  have hS : IsIso (Spec.map (zeroIso I).hom) := inferInstance
  have hQ : IsProper (Spec.map (zeroIso I).hom) := by infer_instance
  exact MorphismProperty.comp_mem (@IsProper) _ _ hP hQ

end

noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def generator (a : I) : reesAlgebra I :=
  ⟨monomial 1 a.val, reesAlgebra.monomial_mem.mpr (by simp [a.property])⟩

@[simp] lemma generator_val (a : I) :
    (generator I a : R[X]) = monomial 1 a.val := rfl

lemma generator_mem (a : I) : generator I a ∈ piece I 1 := by
  simp [mem_piece]

def evaluation : reesAlgebra I →+* R :=
  (Polynomial.evalRingHom 1).comp (reesAlgebra I).val.toRingHom

@[simp] lemma evaluation_generator (a : I) : evaluation I (generator I a) = a.val := by
  simp [evaluation]

abbrev chart (a : I) := HomogeneousLocalization.Away (piece I) (generator I a)

def chartBase (a : I) : R →+* chart I a :=
  (HomogeneousLocalization.fromZeroRingHom (piece I) (Submonoid.powers (generator I a))).comp
    (zeroEquiv I).toRingHom

def ratio (a b : I) : chart I a :=
  HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) 1
    (generator I b) (by simpa using generator_mem I b)

end
end MaximalSeshadri.ReesGrading

end

end OAI
end

section
namespace OAI

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme.{0}}
abbrev complexSectionModule (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    Module ℂ (GlobalSections X M) :=
  Module.compHom _ (baseScalars f)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

end
end MaximalSeshadri.Geometry

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
abbrev JetIndex (r m : ℕ) := Fin r × Fin m × Fin m

noncomputable def finiteJetColumn (r m : ℕ) (points : Fin r → ℂ × ℂ)
    (f : ℂ → ℂ → ℂ) : JetIndex r m → ℂ := fun j =>
  if (j.2.1 : ℕ) + (j.2.2 : ℕ) < m then
    iteratedDeriv j.2.2 (fun z => iteratedDeriv j.2.1 (fun u => f u z)
      (points j.1).1) (points j.1).2 else 0

noncomputable def compressionRowMap (s : ℂ) (B : ℕ) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun P := (1 + Polynomial.C s * Polynomial.X) ^ B * P.comp (1 + Polynomial.C s * Polynomial.X)
  map_add' P Q := by simp [mul_add]
  map_smul' c P := by
    simp only [Polynomial.smul_eq_C_mul, RingHom.id_apply, Polynomial.mul_comp,
      Polynomial.C_comp]
    ring

@[simp] theorem compressionRowMap_pow (s : ℂ) (B j : ℕ) :
    compressionRowMap s B (Polynomial.X ^ j) = (1 + Polynomial.C s * Polynomial.X) ^ (B + j) := by
  simp [compressionRowMap, pow_add]

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation

open scoped BigOperators Pointwise

def rows (s : Finset (ℤ × ℤ)) : Finset ℤ := s.image Prod.snd

def row (s : Finset (ℤ × ℤ)) (y : ℤ) : Finset ℤ :=
  (s.filter (fun p => p.2 = y)).image Prod.fst

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.TildeFlasque
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AffineDenominators AdicInjective InjectiveRange
universe u
variable {R : CommRingCat.{u}} [IsNoetherianRing R]
variable (M : (Spec R).Modules)

theorem top_surjective (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] (U : (Spec R).Opens) :
    Function.Surjective (res U ⊤ le_top (M := M)) := by
  have hU : IsCompact (U : Set (Spec R)) := NoetherianSpace.isCompact _
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact U hU
  let := hι
  let I : Ideal R := Ideal.span (Set.range g)
  let r := res U ⊤ le_top (M := M)
  have hk : r.ker = adicTorsion I Γ(M,⊤) := by
    ext s
    change r s = 0 ↔ s ∈ adicTorsion I Γ(M,⊤)
    rw [mem_adicTorsion]
    exact ⟨kernel_is_torsion g U hg hloc s, torsion_in_kernel g U hg s⟩
  have hi : Module.Injective R (adicTorsion I Γ(M,⊤)) := adicTorsion_injective I Γ(M,⊤)
  let : Module.Injective R r.ker := Module.Baer.injective
    (Module.Baer.of_equiv (LinearEquiv.ofEq _ _ hk.symm) (Module.Baer.of_injective hi))
  apply surjective_of_torsion_cokernel I r
  · exact fun s => cokernel_is_torsion g U hg hU hloc s
  · exact fun s => torsion_free g U hg s

theorem flasque_of_injective_global (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨t,ht⟩ := top_surjective M hloc V.unop s
    refine ⟨res U.unop ⊤ le_top t, ?_⟩
    change res V.unop U.unop (leOfHom i.unop) (res U.unop ⊤ le_top t) = s
    rw [res_comp]
    exact ht

instance tilde_injective_isFlasque (N : ModuleCat.{u} R) [Module.Injective R N] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde N)) := by
  let : Module.Injective R Γ(tilde N,⊤) := Module.Baer.injective
    (Module.Baer.of_equiv (asIso (tilde.toOpen N ⊤)).toLinearEquiv
      (Module.Baer.of_injective inferInstance))
  exact flasque_of_injective_global (tilde N) (isLocalizing_tilde N)

end
end MaximalSeshadri.TildeFlasque

namespace MaximalSeshadri.TildeExact
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {R : CommRingCat.{u}}

instance map_mono {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] : Mono (tilde.map f) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U s t h
  apply Subtype.ext
  funext x
  haveI : (x.1 : PrimeSpectrum R).asIdeal.IsPrime := (x.1 : PrimeSpectrum R).isPrime
  apply LocalizedModule.map_injective (x.1 : PrimeSpectrum R).asIdeal.primeCompl f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)
  exact congrFun (congrArg Subtype.val h) x

instance preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves f _ := map_mono f

instance preservesHomology : (tilde.functor R).PreservesHomology :=
  (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels

instance preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

end
end MaximalSeshadri.TildeExact

namespace MaximalSeshadri.ModuleGrothendieck
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] (R₀ : Cᵒᵖ ⥤ RingCat.{u})

instance presheafAB5 : AB5 (PresheafOfModules.{u} R₀) where
  ofShape J _ _ := HasExactColimitsOfShape.domain_of_functor J
    (PresheafOfModules.toPresheaf R₀)

instance presheafHasSeparator : HasSeparator (PresheafOfModules.{u} R₀) :=
  ⟨⟨∐ (yoneda ⋙ PresheafOfModules.free R₀).obj,
    (PresheafOfModules.freeYoneda.isSeparating R₀).isSeparator_coproduct⟩⟩

instance presheafGrothendieck : IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R₀) where

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]

instance sheafAB5 : AB5 (SheafOfModules.{u} R) where
  ofShape K _ _ :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K

lemma freeSheafSeparating :
    ObjectProperty.IsSeparating (.ofObj (fun U : C =>
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.free R.obj).obj (yoneda.obj U)))) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  intro M N f g h
  apply (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
  apply PresheafOfModules.freeYoneda.isSeparating R.obj
  intro P hP a
  obtain ⟨U⟩ := hP
  obtain ⟨b, rfl⟩ := (adj.homEquiv _ _).surjective a
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_right]
  exact congrArg (adj.homEquiv _ _) (h _ ⟨U⟩ b)

instance sheafHasSeparator : HasSeparator (SheafOfModules.{u} R) :=
  ⟨⟨∐ (fun U : C => (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))),
    (freeSheafSeparating R).isSeparator_coproduct⟩⟩

instance sheafGrothendieck : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) where

theorem enoughInjectives : EnoughInjectives (SheafOfModules.{u} R) := inferInstance

end
end MaximalSeshadri.ModuleGrothendieck

namespace MaximalSeshadri.ModuleFlasque
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

abbrev freeOpen (U : Opens X) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))

abbrev freeOpenMap {U V : Opens X} (i : U ⟶ V) : freeOpen R U ⟶ freeOpen R V :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map i))

lemma freeMap_mono {F G : (Opens X)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [Mono f] :
    Mono ((PresheafOfModules.free R.obj).map f) := by
  apply PresheafOfModules.mono_of_injective
  intro W
  change Function.Injective (Finsupp.mapDomain (f.app W))
  exact Finsupp.mapDomain_injective ((CategoryTheory.mono_iff_injective (f.app W)).mp
    inferInstance)

instance freeOpenMap_mono {U V : Opens X} (i : U ⟶ V) : Mono (freeOpenMap R i) := by
  let := freeMap_mono R (yoneda.map i)
  dsimp [freeOpenMap]
  infer_instance

def freeOpenEquiv (M : SheafOfModules.{u} R) (U : Opens X) :
    (freeOpen R U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    PresheafOfModules.freeYonedaEquiv

lemma freeYoneda_naturality {M : PresheafOfModules.{u} R.obj} {U V : Opens X}
    (i : U ⟶ V) (f : (PresheafOfModules.free R.obj).obj (yoneda.obj V) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.free R.obj).map (yoneda.map i) ≫ f) =
      M.map i.op (PresheafOfModules.freeYonedaEquiv f) := by
  have h := (PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left
    (yoneda.map i) f
  simp only [PresheafOfModules.freeAdjunction_homEquiv] at h
  exact (congrArg yonedaEquiv h).trans
    (yonedaEquiv_naturality (PresheafOfModules.freeHomEquiv f) i).symm

lemma freeOpenEquiv_naturality (M : SheafOfModules.{u} R) {U V : Opens X}
    (i : U ⟶ V) (f : freeOpen R V ⟶ M) :
    freeOpenEquiv R M U (freeOpenMap R i ≫ f) =
      M.val.map i.op (freeOpenEquiv R M V f) := by
  unfold freeOpenEquiv
  dsimp only [Equiv.trans_apply]
  change PresheafOfModules.freeYonedaEquiv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ (_ ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact freeYoneda_naturality R i
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) f)

theorem restriction_surjective (M : SheafOfModules.{u} R) [Injective M]
    {U V : Opens X} (i : U ⟶ V) : Function.Surjective (M.val.map i.op) := by
  intro s
  let f := (freeOpenEquiv R M U).symm s
  obtain ⟨g, hg⟩ := Injective.factors f (freeOpenMap R i)
  refine ⟨freeOpenEquiv R M V g, ?_⟩
  rw [← freeOpenEquiv_naturality, hg]
  exact (freeOpenEquiv R M U).apply_symm_apply s

instance injective_isFlasque (M : SheafOfModules.{u} R) [Injective M] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact restriction_surjective R M i.unop

end
end MaximalSeshadri.ModuleFlasque

namespace MaximalSeshadri.ModuleSheafExact
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]

instance toSheafPreservesColimit {K : Type u} [Category.{u} K]
    (D : K ⥤ SheafOfModules.{u} R) : PreservesColimit D (SheafOfModules.toSheaf R) := by
  let F := PresheafOfModules.sheafification (𝟙 R.obj)
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let H := SheafOfModules.toSheaf R
  let adj : F ⊣ G := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have : PreservesColimitsOfSize.{u,u} (F ⋙ H) :=
    inferInstanceAs (PreservesColimitsOfSize.{u,u}
      (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat))
  have : PreservesColimit (D ⋙ G ⋙ F) H :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves F (colimit.isColimit (D ⋙ G)))
      (isColimitOfPreserves (F ⋙ H) (colimit.isColimit (D ⋙ G)))
  exact preservesColimit_of_iso_diagram H
    ((Functor.isoWhiskerLeft D (asIso adj.counit)) ≪≫ D.rightUnitor)

instance toSheafPreservesColimits :
    PreservesColimitsOfSize.{u,u} (SheafOfModules.toSheaf.{u} R) where
  preservesColimitsOfShape := ⟨fun {_} => inferInstance⟩

theorem shortExact_map {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf R)).ShortExact := hS.map_of_exact _

end
end MaximalSeshadri.ModuleSheafExact

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators NNReal ENNReal

def wordExponent {n : ℕ} (w : Fin n → Bool) : ℕ × ℕ :=
  ((Finset.univ.filter (fun i => w i = false)).card,
    (Finset.univ.filter (fun i => w i = true)).card)

lemma wordExponent_degree {n : ℕ} (w : Fin n → Bool) :
    (wordExponent w).1 + (wordExponent w).2 = n := by
  simpa [wordExponent] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => w i = false))

def coordinateVector : Bool → ℂ × ℂ
  | false => (1, 0)
  | true => (0, 1)

@[simp] lemma norm_coordinateVector (b : Bool) : ‖coordinateVector b‖ = 1 := by
  cases b <;> simp [coordinateVector, Prod.norm_def]

lemma prod_coordinate_word {n : ℕ} (w : Fin n → Bool) (x z : ℂ) :
    (∏ i, if w i = false then x else z) = x ^ (wordExponent w).1 * z ^ (wordExponent w).2 := by
  simp [Finset.prod_ite, wordExponent]

theorem multilinear_coordinate_expansion {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ × ℂ) ℂ) (x z : ℂ) :
    p (fun _ => (x, z)) =
      ∑ w : Fin n → Bool,
        p (fun i => coordinateVector (w i)) *
          x ^ (wordExponent w).1 * z ^ (wordExponent w).2 := by
  have h := p.map_sum (fun (_ : Fin n) (b : Bool) =>
    (if b = false then x else z) • coordinateVector b)
  have he : (fun _ : Fin n => ∑ b : Bool,
      (if b = false then x else z) • coordinateVector b) = fun _ => (x, z) := by
    ext i <;> simp [coordinateVector]
  rw [he] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro w _
  rw [p.map_smul_univ, smul_eq_mul, prod_coordinate_word]
  ring

def ordinaryCoefficient (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (a b : ℕ) : ℂ :=
  ∑ w : Fin (a + b) → Bool, if wordExponent w = (a, b) then
    p (a + b) (fun i => coordinateVector (w i)) else 0

lemma ordinaryCoefficient_norm_le (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (a b : ℕ) :
    ‖ordinaryCoefficient p a b‖ ≤ (2 : ℝ) ^ (a + b) * ‖p (a + b)‖ := by
  calc
    _ ≤ ∑ _w : Fin (a + b) → Bool, ‖p (a + b)‖ := by
      apply norm_sum_le_of_le _
      intro w _
      split_ifs
      · simpa using (p (a + b)).le_opNorm (fun i => coordinateVector (w i))
      · simp
    _ = _ := by simp

lemma ordinaryCoefficient_eq_degree (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    {a b n : ℕ} (h : a + b = n) :
    ordinaryCoefficient p a b = ∑ w : Fin n → Bool, if wordExponent w = (a, b) then
      p n (fun i => coordinateVector (w i)) else 0 := by
  subst n
  rfl

theorem ordinaryCoefficient_homogeneous (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (n : ℕ) (x z : ℂ) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      ordinaryCoefficient p ab.1 ab.2 * x ^ ab.1 * z ^ ab.2) =
        p n (fun _ => (x, z)) := by
  rw [multilinear_coordinate_expansion]
  have he : (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      ordinaryCoefficient p ab.1 ab.2 * x ^ ab.1 * z ^ ab.2) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ w : Fin n → Bool,
        if wordExponent w = ab then
          p n (fun i => coordinateVector (w i)) * x ^ ab.1 * z ^ ab.2 else 0 := by
    apply Finset.sum_congr rfl
    intro ab hab
    rw [ordinaryCoefficient_eq_degree p (Finset.HasAntidiagonal.mem_antidiagonal.mp hab)]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp [Finset.HasAntidiagonal.mem_antidiagonal, wordExponent_degree]

theorem ordinaryCoefficient_geometric_bound (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (ρ C : ℝ) (hρ : 0 < ρ)
    (hp : ∀ n, ‖p n‖ ≤ C / ρ ^ n) (a b : ℕ) :
    ‖ordinaryCoefficient p a b‖ * (ρ / 4) ^ (a + b) ≤ C * (1 / 2 : ℝ) ^ (a + b) := by
  calc
    _ ≤ ((2 : ℝ) ^ (a + b) * (C / ρ ^ (a + b))) * (ρ / 4) ^ (a + b) := by
      gcongr
      exact (ordinaryCoefficient_norm_le p a b).trans (mul_le_mul_of_nonneg_left
        (hp (a + b)) (by positivity))
    _ = _ := by
      rw [div_pow, div_pow]
      field_simp
      ring_nf
      rw [Nat.mul_comm a 2, Nat.mul_comm b 2, pow_mul, pow_mul]
      norm_num

theorem ordinaryCoefficient_absolutely_convergent
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (ρ : ℝ≥0)
    (hρ : 0 < ρ) (hr : (ρ : ℝ≥0∞) < p.radius) :
    Summable (fun ab : ℕ × ℕ => ‖ordinaryCoefficient p ab.1 ab.2‖ *
      ((ρ : ℝ) / 4) ^ (ab.1 + ab.2)) := by
  obtain ⟨C, _, hp⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hρ hr
  have hs : Summable (fun ab : ℕ × ℕ => C * ((1 / 2 : ℝ) ^ (ab.1 + ab.2))) := by
    have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))
    simpa only [pow_add] using (h.mul_of_nonneg h (fun _ => by positivity)
      (fun _ => by positivity)).mul_left C
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun ab => ordinaryCoefficient_geometric_bound p ρ C hρ hp ab.1 ab.2) hs

lemma ordinary_hasSum_by_degree (c : ℕ × ℕ → ℂ) (hc : Summable c) :
    HasSum (fun n : ℕ => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, c ab) (∑' ab, c ab) := by
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hs : HasSum (fun s : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n => c s.2.val)
      (∑' ab, c ab) := e.hasSum_iff.mpr hc.hasSum
  apply hs.sigma
  intro n
  simpa only [Finset.sum_coe_sort] using
    (hasSum_fintype (fun ab : Finset.HasAntidiagonal.antidiagonal n => c ab.val))

lemma ordinary_terms_summable (c : ℕ × ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : Summable (fun ab => ‖c ab‖ * R ^ (ab.1 + ab.2)))
    (x z : ℂ) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    Summable (fun ab => c ab * x ^ ab.1 * z ^ ab.2) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hc
  intro ab
  simp only [norm_mul, norm_pow, pow_add, ← mul_assoc]
  gcongr

theorem hasFPowerSeriesOnBall_ordinary_expansion
    (f : ℂ × ℂ → ℂ) (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (r : ℝ≥0∞) (hf : HasFPowerSeriesOnBall f p 0 r)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hr : (ρ : ℝ≥0∞) < r)
    (x z : ℂ) (hx : ‖x‖ < (ρ : ℝ) / 4) (hz : ‖z‖ < (ρ : ℝ) / 4) :
    f (x,z) = ∑' ab : ℕ × ℕ, ordinaryCoefficient p ab.1 ab.2 * x ^ ab.1 * z ^ ab.2 := by
  have hc := ordinaryCoefficient_absolutely_convergent p ρ hρ (hr.trans_le hf.r_le)
  have hs := ordinary_terms_summable (fun ab => ordinaryCoefficient p ab.1 ab.2)
    ((ρ : ℝ) / 4) (by positivity) hc x z hx.le hz.le
  have hh := ordinary_hasSum_by_degree _ hs
  simp_rw [ordinaryCoefficient_homogeneous] at hh
  have hnorm : ‖(x,z)‖₊ < ρ := by
    change max ‖x‖ ‖z‖ < (ρ : ℝ)
    apply max_lt
    · linarith [show (0 : ℝ) < ρ from hρ]
    · linarith [show (0 : ℝ) < ρ from hρ]
  have hm : (x,z) ∈ Metric.eball (0 : ℂ × ℂ) r := by
    rw [mem_eball_zero_iff]
    exact (ENNReal.coe_lt_coe.mpr hnorm).trans hr
  have hh' := hf.hasSum hm
  simpa only [zero_add] using hh'.unique hh

theorem analyticAt_exists_ordinary_expansion (f : ℂ × ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    ∃ c : ℕ × ℕ → ℂ, ∃ R : ℝ, 0 < R ∧
      Summable (fun ab => ‖c ab‖ * R ^ (ab.1 + ab.2)) ∧
      ∀ x z : ℂ, ‖x‖ < R → ‖z‖ < R →
        f (x,z) = ∑' ab : ℕ × ℕ, c ab * x ^ ab.1 * z ^ ab.2 := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨ρ, hρ, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hρ' : (0 : ℝ≥0) < ρ := by exact_mod_cast hρ
  refine ⟨fun ab => ordinaryCoefficient p ab.1 ab.2, (ρ : ℝ) / 4, by positivity,
    ordinaryCoefficient_absolutely_convergent p ρ hρ' (hr.trans_le hp.r_le), ?_⟩
  intro x z hx hz
  exact hasFPowerSeriesOnBall_ordinary_expansion f p r hp ρ hρ' hr x z hx hz

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter Set

lemma monomialDeriv_at_zero (n a : ℕ) :
    monomialDeriv n a 0 = if n = a then (a.factorial : ℂ) else 0 := by
  by_cases h : n = a
  · subst n
    simp [monomialDeriv, Nat.descFactorial_self]
  · rw [ite_eq_right_iff.mpr (fun he => (h he).elim)]
    by_cases hn : n < a
    · simp [monomialDeriv, Nat.descFactorial_eq_zero_iff_lt.mpr hn]
    · have hd : n - a ≠ 0 := by omega
      simp [monomialDeriv, zero_pow hd]

lemma seriesPartial_at_zero (c : Exponent → ℂ) (a b : ℕ) :
    seriesPartial c a b 0 0 = c (a,b) * (a.factorial : ℂ) * (b.factorial : ℂ) := by
  unfold seriesPartial
  rw [tsum_eq_single (a,b)]
  · simp [monomialDeriv_at_zero]
  · intro p hp
    by_cases h₁ : p.1 = a
    · have h₂ : p.2 ≠ b := by intro h₂; exact hp (Prod.ext h₁ h₂)
      simp [monomialDeriv_at_zero, h₂]
    · simp [monomialDeriv_at_zero, h₁]

theorem mixedDeriv_at_zero (c : Exponent → ℂ) (hc : ConvergentSeries c) (a b : ℕ) :
    iteratedDeriv b (fun z => iteratedDeriv a (fun x => seriesEval c x z) 0) 0 =
      c (a,b) * (a.factorial : ℂ) * (b.factorial : ℂ) := by
  obtain ⟨R, hR, hconv⟩ := hc
  rw [mixedDeriv_seriesEval c (R / 2)
    (derivativeSummable_of_absolute c R (R / 2) hR (by positivity) (by linarith) hconv)
    a b 0 0 (by simpa using (show (0 : ℝ) < R / 2 by positivity))
      (by simpa using (show (0 : ℝ) < R / 2 by positivity))]
  exact seriesPartial_at_zero c a b

lemma mixedDeriv_congr_germ (f g : ℂ × ℂ → ℂ) (h : f =ᶠ[𝓝 0] g) (a b : ℕ) :
    iteratedDeriv b (fun z => iteratedDeriv a (fun x => f (x,z)) 0) 0 =
      iteratedDeriv b (fun z => iteratedDeriv a (fun x => g (x,z)) 0) 0 := by
  obtain ⟨ε, hε, hfg⟩ := Metric.eventually_nhds_iff.mp h
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < ε := by
    change {z : ℂ | ‖z‖ < ε} ∈ 𝓝 (0 : ℂ)
    simpa only [Metric.ball, dist_zero_right] using
      (Metric.ball_mem_nhds (0 : ℂ) hε)
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hn] with z hz
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hn] with x hx
  apply hfg
  simpa [Prod.dist_eq, dist_zero_right, max_lt_iff] using And.intro hx hz

theorem convergent_expansion_unique (c d : Exponent → ℂ)
    (hc : ConvergentSeries c) (hd : ConvergentSeries d)
    (heq : (fun q : ℂ × ℂ => seriesEval c q.1 q.2) =ᶠ[𝓝 0]
      (fun q : ℂ × ℂ => seriesEval d q.1 q.2)) : c = d := by
  ext ab
  have h := mixedDeriv_congr_germ _ _ heq ab.1 ab.2
  rw [mixedDeriv_at_zero c hc, mixedDeriv_at_zero d hd] at h
  exact mul_right_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero ab.1)
    (mul_right_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero ab.2) h)

def analyticFunctionAlgebra : Subalgebra ℂ (ℂ × ℂ → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  mul_mem' := fun hf hg => hf.mul hg
  add_mem' := fun hf hg => hf.add hg
  algebraMap_mem' := fun _ => analyticAt_const

def analyticCoefficients (f : analyticFunctionAlgebra) : Exponent → ℂ :=
  (analyticAt_exists_ordinary_expansion f f.property).choose

lemma analyticCoefficients_spec (f : analyticFunctionAlgebra) :
    ConvergentSeries (analyticCoefficients f) ∧
      (fun q : ℂ × ℂ => f.val q) =ᶠ[𝓝 0]
        (fun q : ℂ × ℂ => seriesEval (analyticCoefficients f) q.1 q.2) := by
  obtain ⟨R, hR, hsum, heq⟩ := (analyticAt_exists_ordinary_expansion f f.property).choose_spec
  refine ⟨⟨R, hR, hsum⟩, ?_⟩
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨R, hR, ?_⟩
  intro q hq
  have hq' : ‖q.1‖ < R ∧ ‖q.2‖ < R := by
    simpa [Prod.dist_eq, dist_zero_right, Prod.norm_def, max_lt_iff] using hq
  exact heq q.1 q.2 hq'.1 hq'.2

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter

local instance : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite

def coeffConvolution (c d : Exponent → ℂ) (e : Exponent) : ℂ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e, c ab.1 * d ab.2

lemma absolute_mono {c : Exponent → ℂ} {R ρ : ℝ}
    (hR : AbsolutelyConvergentAt c R) (hρ : 0 ≤ ρ) (h : ρ ≤ R) :
    AbsolutelyConvergentAt c ρ := by
  exact Summable.of_nonneg_of_le (fun p => by positivity)
    (fun p => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ h _) (norm_nonneg _)) hR

lemma absolute_terms_summable {c : Exponent → ℂ} {R : ℝ}
    (hc : AbsolutelyConvergentAt c R) {x z : ℂ} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    Summable (fun e : Exponent => ‖c e * x ^ e.1 * z ^ e.2‖) := by
  exact (ordinary_terms_summable c R ((norm_nonneg _).trans hx) hc x z hx hz).norm

lemma absolute_convolution {c d : Exponent → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R) :
    AbsolutelyConvergentAt (coeffConvolution c d) R := by
  have hs := hc.mul_of_nonneg hd (fun e => by positivity) (fun e => by positivity)
  have ht := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
    (A := Exponent)).summable_iff.mpr hs
  have hu := ht.sigma
  change Summable (fun e : Exponent => ∑' ab : Finset.HasAntidiagonal.antidiagonal e,
    (‖c ab.val.1‖ * R ^ (ab.val.1.1 + ab.val.1.2)) *
      (‖d ab.val.2‖ * R ^ (ab.val.2.1 + ab.val.2.2))) at hu
  have hu' : Summable (fun e : Exponent => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e,
    (‖c ab.1‖ * R ^ (ab.1.1 + ab.1.2)) *
      (‖d ab.2‖ * R ^ (ab.2.1 + ab.2.2))) := hu.congr (fun e => by
        rw [tsum_fintype]
        exact Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal e)
          (fun ab : Exponent × Exponent => (‖c ab.1‖ * R ^ (ab.1.1 + ab.1.2)) *
            (‖d ab.2‖ * R ^ (ab.2.1 + ab.2.2))))
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_) hu'
  calc
    ‖coeffConvolution c d e‖ * R ^ (e.1 + e.2) ≤
      (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e, ‖c ab.1 * d ab.2‖) *
        R ^ (e.1 + e.2) := by
          exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hR _)
    _ = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e,
      (‖c ab.1‖ * R ^ (ab.1.1 + ab.1.2)) *
        (‖d ab.2‖ * R ^ (ab.2.1 + ab.2.2)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ab hab
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      have he₁ := congrArg Prod.fst he
      have he₂ := congrArg Prod.snd he
      simp only [Prod.fst_add, Prod.snd_add] at he₁ he₂
      rw [← he₁, ← he₂, norm_mul]
      simp only [pow_add]
      ring

lemma seriesEval_convolution {c d : Exponent → ℂ} {R : ℝ}
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R)
    {x z : ℂ} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    seriesEval (coeffConvolution c d) x z = seriesEval c x z * seriesEval d x z := by
  have hf := absolute_terms_summable hc hx hz
  have hg := absolute_terms_summable hd hx hz
  have hs := summable_mul_of_summable_norm hf hg
  let E := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := Exponent)
  have ht := E.summable_iff.mpr hs
  unfold seriesEval
  rw [tsum_mul_tsum_of_summable_norm hf hg, ← E.tsum_eq]
  have hsum := ht.tsum_sigma
  simp only [Function.comp_def] at hsum
  rw [hsum]
  apply tsum_congr
  intro e
  change _ = ∑' ab : Finset.HasAntidiagonal.antidiagonal e,
    (c ab.val.1 * x ^ ab.val.1.1 * z ^ ab.val.1.2) *
      (d ab.val.2 * x ^ ab.val.2.1 * z ^ ab.val.2.2)
  rw [tsum_fintype]
  have heq := Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal e)
    (fun ab : Exponent × Exponent =>
      (c ab.1 * x ^ ab.1.1 * z ^ ab.1.2) * (d ab.2 * x ^ ab.2.1 * z ^ ab.2.2))
  rw [heq]
  simp only [coeffConvolution, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have he₁ := congrArg Prod.fst he
  have he₂ := congrArg Prod.snd he
  simp only [Prod.fst_add, Prod.snd_add] at he₁ he₂
  rw [← he₁, ← he₂]
  simp only [pow_add]
  ring

end
end MaximalSeshadri.AnalyticCoordinates

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri
namespace NodalLocal

open PowerSeries

noncomputable section

variable (K : Type*) [Field K]

def multiples {A : Type*} [CommRing A] [Algebra K A] (f : A) : Submodule K A :=
  LinearMap.range (LinearMap.mulLeft K f)

@[simp] theorem mem_multiples {A : Type*} [CommRing A] [Algebra K A] (f g : A) :
    g ∈ multiples K f ↔ f ∣ g := by
  simp only [multiples, LinearMap.mem_range, LinearMap.mulLeft_apply, dvd_def]
  exact exists_congr (fun _ => eq_comm)

def nodeAlgebra : Subalgebra K (PowerSeries K × PowerSeries K) where
  carrier := {p | constantCoeff p.1 = constantCoeff p.2}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {a b} (ha : constantCoeff a.1 = constantCoeff a.2)
      (hb : constantCoeff b.1 = constantCoeff b.2) := by
    change constantCoeff (a.1 + b.1) = constantCoeff (a.2 + b.2)
    simp only [map_add, ha, hb]
  mul_mem' {a b} (ha : constantCoeff a.1 = constantCoeff a.2)
      (hb : constantCoeff b.1 = constantCoeff b.2) := by
    change constantCoeff (a.1 * b.1) = constantCoeff (a.2 * b.2)
    simp only [map_mul, ha, hb]
  algebraMap_mem' := by intro a; rfl

abbrev Node := nodeAlgebra K

def branchX : Node K →ₐ[K] PowerSeries K where
  toFun := fun f => f.val.1
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl

def branchZ : Node K →ₐ[K] PowerSeries K where
  toFun := fun f => f.val.2
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl

@[ext] theorem node_ext {f g : Node K}
    (hx : branchX K f = branchX K g) (hz : branchZ K f = branchZ K g) : f = g :=
  Subtype.ext (Prod.ext hx hz)

def includeX : PowerSeries K →ₗ[K] Node K where
  toFun := fun f => ⟨(X * f, 0), by change constantCoeff (X * f) = constantCoeff 0; simp⟩
  map_add' := by intro f g; apply Subtype.ext; ext <;> simp [mul_add]
  map_smul' := by intro a f; apply Subtype.ext; ext <;> simp

@[simp] theorem branchX_includeX (f : PowerSeries K) :
    branchX K (includeX K f) = X * f := rfl
@[simp] theorem branchZ_includeX (f : PowerSeries K) :
    branchZ K (includeX K f) = 0 := rfl

def liftZ : PowerSeries K →ₗ[K] Node K where
  toFun := fun f => ⟨(C (constantCoeff f), f), by
    change constantCoeff (C (constantCoeff f)) = constantCoeff f
    simp⟩
  map_add' := by intro f g; apply Subtype.ext; ext <;> simp
  map_smul' := by
    intro a f
    apply Subtype.ext
    change (C (constantCoeff (a • f)), a • f) = (a • C (constantCoeff f), a • f)
    congr 1
    simp only [Algebra.smul_def, map_mul, PowerSeries.algebraMap_apply,
      constantCoeff_C]

@[simp] theorem branchX_liftZ (f : PowerSeries K) :
    branchX K (liftZ K f) = C (constantCoeff f) := rfl
@[simp] theorem branchZ_liftZ (f : PowerSeries K) :
    branchZ K (liftZ K f) = f := rfl

lemma includeX_mul (f : Node K) (g : PowerSeries K) :
    includeX K (branchX K f * g) = f * includeX K g := by
  apply node_ext <;> simp [mul_left_comm]

def coefficientJet (n : ℕ) : PowerSeries K →ₗ[K] (Fin n → K) :=
  LinearMap.pi (fun i => coeff i.val)

@[simp] lemma coefficientJet_apply (n : ℕ) (f : PowerSeries K) (i : Fin n) :
    coefficientJet K n f i = coeff i.val f := rfl

def quotientZ (f : Node K) :
    (Node K ⧸ multiples K f) →ₗ[K]
      (PowerSeries K ⧸ multiples K (branchZ K f)) :=
  (multiples K f).liftQ
    ((multiples K (branchZ K f)).mkQ.comp (branchZ K).toLinearMap) (by
      rintro y ⟨a, rfl⟩
      change (Submodule.Quotient.mk (branchZ K (f * a)) :
        PowerSeries K ⧸ multiples K (branchZ K f)) = 0
      simp only [map_mul, Submodule.Quotient.mk_eq_zero, mem_multiples]
      exact dvd_mul_right _ _)

@[simp] lemma quotientZ_mk (f g : Node K) :
    quotientZ K f (Submodule.Quotient.mk g) = Submodule.Quotient.mk (branchZ K g) := rfl

def quotientX (f : Node K) :
    (PowerSeries K ⧸ multiples K (branchX K f)) →ₗ[K]
      (Node K ⧸ multiples K f) :=
  (multiples K (branchX K f)).liftQ
    ((multiples K f).mkQ.comp (includeX K)) (by
      rintro y ⟨a, rfl⟩
      change (Submodule.Quotient.mk (includeX K (branchX K f * a)) :
        Node K ⧸ multiples K f) = 0
      rw [includeX_mul, Submodule.Quotient.mk_eq_zero, mem_multiples]
      exact dvd_mul_right _ _)

@[simp] lemma quotientX_mk (f : Node K) (g : PowerSeries K) :
    quotientX K f (Submodule.Quotient.mk g) = Submodule.Quotient.mk (includeX K g) := rfl

abbrev Bivariate := PowerSeries (PowerSeries K)

def constAlg : PowerSeries K →ₐ[K] K where
  toRingHom := constantCoeff
  commutes' := by intro a; simp

def restrictX : Bivariate K →ₐ[K] PowerSeries K where
  toRingHom := constantCoeff
  commutes' := by intro a; simp [PowerSeries.algebraMap_apply]

def restrictZ : Bivariate K →ₐ[K] PowerSeries K :=
  PowerSeries.mapAlgHom (constAlg K)

@[simp] lemma restrictX_apply (f : Bivariate K) : restrictX K f = constantCoeff f := rfl
@[simp] lemma restrictZ_apply (f : Bivariate K) :
    restrictZ K f = PowerSeries.map constantCoeff f := rfl

lemma restrict_constants (f : Bivariate K) :
    constantCoeff (restrictX K f) = constantCoeff (restrictZ K f) := by
  simp only [restrictX_apply, restrictZ_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_map]

def toNode : Bivariate K →ₐ[K] Node K where
  toFun f := ⟨(restrictX K f, restrictZ K f), restrict_constants K f⟩
  map_zero' := by
    apply Subtype.ext
    exact Prod.ext (map_zero (restrictX K)) (map_zero (restrictZ K))
  map_one' := by
    apply Subtype.ext
    exact Prod.ext (map_one (restrictX K)) (map_one (restrictZ K))
  map_add' := by intro f g; apply node_ext <;> simp
  map_mul' := by intro f g; apply node_ext <;> simp
  commutes' := by
    intro a
    apply Subtype.ext
    exact Prod.ext ((restrictX K).commutes a) ((restrictZ K).commutes a)

@[simp] lemma branchX_toNode (f : Bivariate K) :
    branchX K (toNode K f) = restrictX K f := rfl
@[simp] lemma branchZ_toNode (f : Bivariate K) :
    branchZ K (toNode K f) = restrictZ K f := rfl

def nodeEquation : Bivariate K := C (X : PowerSeries K) * X

@[simp] lemma toNode_nodeEquation : toNode K (nodeEquation K) = 0 := by
  apply node_ext <;> simp [nodeEquation]

def intersectionIdeal (f : Bivariate K) : Ideal (Bivariate K) :=
  Ideal.span {f, nodeEquation K}

end

end NodalLocal
end MaximalSeshadri

namespace MaximalSeshadri.LocalComparison
noncomputable section
open IsLocalRing
open MaximalSeshadri.NodalLocal
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  [IsLocalRing A] [IsNoetherianRing A]

end
end MaximalSeshadri.LocalComparison
end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

def globalPowerFrame {M : X.Modules} (e : M ≅ structureSheaf X) (n : ℕ) :
    modulePow X M n ≅ structureSheaf X :=
  (modulePowFunctor n).mapIso e ≪≫ unitPowerIso n

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

def localPowerFrame (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) :
    (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme :=
  modulePowRestrict U M n ≪≫ globalPowerFrame e n

end
end MaximalSeshadri.Geometry

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y Z : Scheme.{0}}

def pullbackUnitIso (f : Y ⟶ X) : (Scheme.Modules.pullback f).obj (O X) ≅ O Y := by
  letI : (Opens.map f.base).Final := opensMap_final f
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := Opens.map f.base) f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := Opens.map f.base) f.toRingCatSheafHom
  let a : (SheafOfModules.pullback f.toRingCatSheafHom).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf :=
    asIso (C := SheafOfModules Y.ringCatSheaf)
      (SheafOfModules.pullbackObjUnitToUnit (F := Opens.map f.base) f.toRingCatSheafHom)
  exact { hom := a.hom, inv := a.inv, hom_inv_id := a.hom_inv_id, inv_hom_id := a.inv_hom_id }

def pullbackSection (f : Y ⟶ X) {M : X.Modules} (s : O X ⟶ M) :
    O Y ⟶ (Scheme.Modules.pullback f).obj M :=
  (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def leftSquare :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm (rightSquare f U)

end
end MaximalSeshadri.OpenBaseChange

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K : Type*} [Field K]

def coneA : Set (ℤ × ℤ) := {z | 0 ≤ z.2}
def coneB : Set (ℤ × ℤ) := {z | 0 ≤ z.1}
def coneC (d : ℤ) : Set (ℤ × ℤ) := {z | z.1 + z.2 ≤ d}

end
end MaximalSeshadri.PlaneCech

end

end OAI
end


