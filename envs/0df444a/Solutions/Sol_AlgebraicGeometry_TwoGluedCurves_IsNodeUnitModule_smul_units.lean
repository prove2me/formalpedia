-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.smul_units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/d1895fef-a12d-58fd-bb38-44c4081f45aa

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves

open Opposite

noncomputable section

namespace TwoGluedCurvesScaleAux

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
  {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
  {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)}

local notation "XT" => pullback x h
local notation "C₁T" => pullback c₁ h
local notation "C₂T" => pullback c₂ h
set_option quotPrecheck false in
local notation "i₁T" => curveChange i₁.1 i₁.2 h
set_option quotPrecheck false in
local notation "i₂T" => curveChange i₂.1 i₂.2 h
local notation "σ¹" => nodeSectionFst p₁ h
local notation "σ²" => nodeSectionSnd p₂ h
local notation "nl" => nodeLocus x i₁ i₂ p₁ p₂ h
set_option quotPrecheck false in

local notation "P²" => (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
  (SheafOfModules.unit (pullback c₂ h).ringCatSheaf)

def fn₂ (W : (XT).Opens) (g : Γ(P², W)) : Γ(C₂T, (i₂T) ⁻¹ᵁ W) := g

def ofFn₂ (W : (XT).Opens) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) : Γ(P², W) := g

@[scoped simp] lemma fn₂_ofFn₂ (W : (XT).Opens) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) : fn₂ W (ofFn₂ W g) = g := rfl

lemma fn₂_injective (W : (XT).Opens) : Function.Injective (fn₂ (i₂ := i₂) W) := fun _ _ e => e

lemma fn₂_add (W : (XT).Opens) (g g' : Γ(P², W)) : fn₂ W (g + g') = fn₂ W g + fn₂ W g' := rfl

lemma fn₂_smul (W : (XT).Opens) (r : Γ(XT, W)) (g : Γ(P², W)) :
    fn₂ W (r • g) = (i₂T).app W r * fn₂ W g := rfl

lemma fn₂_map {W W' : (XT).Opens} (i : W' ⟶ W) (g : Γ(P², W)) :
    fn₂ W' ((P²).presheaf.map i.op g) =
      (C₂T).presheaf.map ((TopologicalSpace.Opens.map (i₂T).base).map i).op (fn₂ W g) := rfl

def sndFun (d : Γ(T, ⊤)) (W : (XT).Opens) : Γ(C₂T, (i₂T) ⁻¹ᵁ W) :=
  (pullback.snd c₂ h).appLE ⊤ ((i₂T) ⁻¹ᵁ W) le_top d

lemma sndFun_mul (d d' : Γ(T, ⊤)) (W : (XT).Opens) :
    sndFun (i₂ := i₂) (d * d') W = sndFun d W * sndFun d' W := map_mul _ _ _

lemma sndFun_one (W : (XT).Opens) : sndFun (i₂ := i₂) (1 : Γ(T, ⊤)) W = 1 := map_one _

lemma sndFun_map (d : Γ(T, ⊤)) {W W' : (XT).Opens} (i : W' ⟶ W) :
    (C₂T).presheaf.map ((TopologicalSpace.Opens.map (i₂T).base).map i).op (sndFun d W) = sndFun d W' := by
  unfold sndFun
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

lemma isUnit_sndFun (v : Γ(T, ⊤)ˣ) (W : (XT).Opens) : IsUnit (sndFun (i₂ := i₂) (v : Γ(T, ⊤)) W) :=
  (Units.isUnit v).map _

lemma nodeSectionSnd_snd (j : ι) : σ² j ≫ pullback.snd c₂ h = 𝟙 T := by
  simp only [nodeSectionSnd, rigSection, pullback.lift_snd]

lemma appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (e : f = g) (U : Z.Opens) (V : Y.Opens)
    (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V h₁ = g.appLE U V h₂ := by
  subst e; rfl

lemma appLE_sndFun (j : ι) (W : (XT).Opens) (d : Γ(T, ⊤)) :
    (σ² j).appLE ((i₂T) ⁻¹ᵁ W) (nl j W) inf_le_right (sndFun d W) =
      T.presheaf.map (homOfLE (le_top : nl j W ≤ ⊤)).op d := by
  unfold sndFun
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [appLE_congr_hom (nodeSectionSnd_snd j) ⊤ (nl j W) _ le_top]
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  rfl

def mulSnd (d : Γ(T, ⊤)) (W : (XT).Opens) (g : Γ(P², W)) : Γ(P², W) := ofFn₂ W (sndFun d W * fn₂ W g)

lemma fn₂_mulSnd (d : Γ(T, ⊤)) (W : (XT).Opens) (g : Γ(P², W)) :
    fn₂ W (mulSnd d W g) = sndFun d W * fn₂ W g := rfl

lemma mulSnd_add (d : Γ(T, ⊤)) (W : (XT).Opens) (g g' : Γ(P², W)) :
    mulSnd d W (g + g') = mulSnd d W g + mulSnd d W g' := by
  apply fn₂_injective W
  rw [fn₂_mulSnd, fn₂_add, fn₂_add, fn₂_mulSnd, fn₂_mulSnd, mul_add]

lemma mulSnd_smul (d : Γ(T, ⊤)) (W : (XT).Opens) (r : Γ(XT, W)) (g : Γ(P², W)) :
    mulSnd d W (r • g) = r • mulSnd d W g := by
  apply fn₂_injective W
  rw [fn₂_mulSnd, fn₂_smul, fn₂_smul, fn₂_mulSnd, mul_left_comm]

lemma mulSnd_map (d : Γ(T, ⊤)) {W W' : (XT).Opens} (i : W' ⟶ W) (g : Γ(P², W)) :
    mulSnd d W' ((P²).presheaf.map i.op g) = (P²).presheaf.map i.op (mulSnd d W g) := by
  apply fn₂_injective W'
  rw [fn₂_mulSnd, fn₂_map, fn₂_map, fn₂_mulSnd, map_mul, sndFun_map]

def mulSndPresheafHom (d : Γ(T, ⊤)) : (P²).presheaf ⟶ (P²).presheaf where
  app W := AddCommGrpCat.ofHom (AddMonoidHom.mk' (mulSnd d W.unop) (mulSnd_add d W.unop))
  naturality W W' i := by
    ext g
    obtain ⟨i, rfl⟩ : ∃ i' : W'.unop ⟶ W.unop, i = i'.op := ⟨i.unop, rfl⟩
    exact mulSnd_map d i g

def mulSndHom (d : Γ(T, ⊤)) : P² ⟶ P² :=
  ⟨PresheafOfModules.homMk (mulSndPresheafHom d) (fun W r g => mulSnd_smul d W.unop r g)⟩

@[scoped simp] lemma mulSndHom_app (d : Γ(T, ⊤)) (W : (XT).Opens) (g : Γ(P², W)) :
    (mulSndHom d).app W g = mulSnd d W g := rfl

lemma fn₂_comp_mulSndHom_app {M : (XT).Modules} (j₂ : M ⟶ P²) (d : Γ(T, ⊤)) (W : (XT).Opens)
    (m : Γ(M, W)) :
    fn₂ W ((j₂ ≫ mulSndHom d).app W m) = sndFun d W * fn₂ W (j₂.app W m) := by
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, mulSndHom_app, fn₂_mulSnd]

lemma nodeCondition_smul_iff (u : ι → Γ(T, ⊤)ˣ) (c : Γ(T, ⊤)ˣ) (W : (XT).Opens) (j : ι)
    (f : Γ(C₁T, (i₁T) ⁻¹ᵁ W)) (g : Γ(C₂T, (i₂T) ⁻¹ᵁ W)) :
    NodeCondition x i₁ i₂ p₁ p₂ h (fun j => c * u j) W j f g ↔
      NodeCondition x i₁ i₂ p₁ p₂ h u W j f (sndFun (c : Γ(T, ⊤)) W * g) := by
  unfold NodeCondition
  simp only [Units.val_mul, map_mul, appLE_sndFun]
  constructor <;> intro e <;> rw [e] <;> ring

end TwoGluedCurvesScaleAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units.TwoGluedCurvesScaleAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units.TwoGluedCurvesScaleAux"

open TwoGluedCurvesScaleAux in
theorem solution
    {κ : Type u} [Field κ]
    {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
    {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} {M : (pullback x h).Modules}
    (hM : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M) (c : Γ(T, ⊤)ˣ) :
    IsNodeUnitModule x i₁ i₂ p₁ p₂ h (fun j => c * u j) M := by
  obtain ⟨j₁, j₂, hj⟩ := hM
  refine ⟨j₁, j₂ ≫ mulSndHom ((c⁻¹ : Γ(T, ⊤)ˣ) : Γ(T, ⊤)), fun W => ⟨?_, ?_⟩⟩
  ·
    intro m m' e
    have e₁ := congrArg Prod.fst e
    have e₂ := congrArg (fun q => fn₂ W q.2) e
    dsimp only at e₁ e₂
    rw [fn₂_comp_mulSndHom_app, fn₂_comp_mulSndHom_app] at e₂
    exact (hj W).1 (Prod.ext e₁ ((isUnit_sndFun c⁻¹ W).mul_right_injective e₂))
  ·
    ext fg
    constructor
    · rintro ⟨m, rfl⟩
      have hm : (j₁.app W m, j₂.app W m) ∈
          Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) := ⟨m, rfl⟩
      rw [(hj W).2, Set.mem_setOf_eq] at hm
      rw [Set.mem_setOf_eq]
      intro j
      rw [nodeCondition_smul_iff]
      change NodeCondition x i₁ i₂ p₁ p₂ h u W j (j₁.app W m)
        (sndFun (c : Γ(T, ⊤)) W * fn₂ W ((j₂ ≫ mulSndHom ((c⁻¹ : Γ(T, ⊤)ˣ) : Γ(T, ⊤))).app W m))
      rw [fn₂_comp_mulSndHom_app, ← mul_assoc, ← sndFun_mul, Units.mul_inv, sndFun_one, one_mul]
      exact hm j
    · intro hfg
      rw [Set.mem_setOf_eq] at hfg
      have hfg' : (fg.1, ofFn₂ W (sndFun (c : Γ(T, ⊤)) W * fn₂ W fg.2)) ∈
          Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) := by
        rw [(hj W).2, Set.mem_setOf_eq]
        intro j
        exact (nodeCondition_smul_iff u c W j _ _).mp (hfg j)
      obtain ⟨m, hm⟩ := hfg'
      have e₁ : j₁.app W m = fg.1 := congrArg Prod.fst hm
      refine ⟨m, Prod.ext e₁ ?_⟩
      apply fn₂_injective W
      change fn₂ W ((j₂ ≫ mulSndHom ((c⁻¹ : Γ(T, ⊤)ˣ) : Γ(T, ⊤))).app W m) = fn₂ W fg.2
      have e₂ : fn₂ W (j₂.app W m) = sndFun (c : Γ(T, ⊤)) W * fn₂ W fg.2 :=
        congrArg (fun q => fn₂ W q.2) hm
      rw [fn₂_comp_mulSndHom_app, e₂, ← mul_assoc, ← sndFun_mul, Units.inv_mul, sndFun_one, one_mul]

end S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units (solution)
