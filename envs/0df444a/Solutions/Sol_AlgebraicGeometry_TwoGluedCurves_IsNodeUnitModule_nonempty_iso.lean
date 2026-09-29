-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.nonempty_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/eb34035f-9fa6-5f9d-b4ee-13a6dad28015

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves

open Opposite

noncomputable section

namespace TwoGluedCurvesUniqAux

variable {Y : Scheme.{u}} {P₁ P₂ : Y.Modules}

section Pair

variable {M : Y.Modules} (j₁ : M ⟶ P₁) (j₂ : M ⟶ P₂)

def pair (W : Y.Opens) (m : Γ(M, W)) : Γ(P₁, W) × Γ(P₂, W) := (j₁.app W m, j₂.app W m)

lemma pair_add (W : Y.Opens) (m m' : Γ(M, W)) :
    pair j₁ j₂ W (m + m') = pair j₁ j₂ W m + pair j₁ j₂ W m' := by
  simp only [pair, map_add, Prod.mk_add_mk]

lemma pair_smul (W : Y.Opens) (r : Γ(Y, W)) (m : Γ(M, W)) :
    pair j₁ j₂ W (r • m) = r • pair j₁ j₂ W m := by
  simp only [pair, Scheme.Modules.Hom.app_smul, Prod.smul_mk]

lemma app_map {N N' : Y.Modules} (φ : N ⟶ N') {W W' : Y.Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h n

lemma pair_map {W W' : Y.Opens} (i : W' ⟶ W) (m : Γ(M, W)) :
    pair j₁ j₂ W' (M.presheaf.map i.op m) =
      (P₁.presheaf.map i.op (pair j₁ j₂ W m).1, P₂.presheaf.map i.op (pair j₁ j₂ W m).2) := by
  simp only [pair, app_map]

end Pair

section Lift

variable {M M' : Y.Modules} (j₁ : M ⟶ P₁) (j₂ : M ⟶ P₂) (j₁' : M' ⟶ P₁) (j₂' : M' ⟶ P₂)
  (hinj' : ∀ W : Y.Opens, Function.Injective (pair j₁' j₂' W))
  (hle : ∀ W : Y.Opens, Set.range (pair j₁ j₂ W) ⊆ Set.range (pair j₁' j₂' W))

include hle in
lemma exists_pair_eq (W : Y.Opens) (m : Γ(M, W)) : ∃ m' : Γ(M', W), pair j₁' j₂' W m' = pair j₁ j₂ W m :=
  hle W ⟨m, rfl⟩

def lift (W : Y.Opens) (m : Γ(M, W)) : Γ(M', W) := (exists_pair_eq j₁ j₂ j₁' j₂' hle W m).choose

lemma pair_lift (W : Y.Opens) (m : Γ(M, W)) :
    pair j₁' j₂' W (lift j₁ j₂ j₁' j₂' hle W m) = pair j₁ j₂ W m :=
  (exists_pair_eq j₁ j₂ j₁' j₂' hle W m).choose_spec

include hinj' in
lemma lift_add (W : Y.Opens) (m n : Γ(M, W)) :
    lift j₁ j₂ j₁' j₂' hle W (m + n) = lift j₁ j₂ j₁' j₂' hle W m + lift j₁ j₂ j₁' j₂' hle W n := by
  apply hinj' W
  rw [pair_add, pair_lift, pair_lift, pair_lift, pair_add]

include hinj' in
lemma lift_smul (W : Y.Opens) (r : Γ(Y, W)) (m : Γ(M, W)) :
    lift j₁ j₂ j₁' j₂' hle W (r • m) = r • lift j₁ j₂ j₁' j₂' hle W m := by
  apply hinj' W
  rw [pair_smul, pair_lift, pair_lift, pair_smul]

include hinj' in
lemma lift_map {W W' : Y.Opens} (i : W' ⟶ W) (m : Γ(M, W)) :
    lift j₁ j₂ j₁' j₂' hle W' (M.presheaf.map i.op m) =
      M'.presheaf.map i.op (lift j₁ j₂ j₁' j₂' hle W m) := by
  apply hinj' W'
  rw [pair_lift, pair_map, pair_map, pair_lift]

def liftPresheafHom : M.presheaf ⟶ M'.presheaf where
  app W := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (lift j₁ j₂ j₁' j₂' hle W.unop) (lift_add j₁ j₂ j₁' j₂' hinj' hle W.unop))
  naturality W W' i := by
    ext m
    obtain ⟨i, rfl⟩ : ∃ i' : W'.unop ⟶ W.unop, i = i'.op := ⟨i.unop, rfl⟩
    exact lift_map j₁ j₂ j₁' j₂' hinj' hle i m

def liftHom : M ⟶ M' :=
  ⟨PresheafOfModules.homMk (liftPresheafHom j₁ j₂ j₁' j₂' hinj' hle)
    (fun W r m => lift_smul j₁ j₂ j₁' j₂' hinj' hle W.unop r m)⟩

@[scoped simp] lemma liftHom_app (W : Y.Opens) (m : Γ(M, W)) :
    (liftHom j₁ j₂ j₁' j₂' hinj' hle).app W m = lift j₁ j₂ j₁' j₂' hle W m := rfl

end Lift

theorem nonempty_iso_of_range_pair_eq {M M' : Y.Modules} (j₁ : M ⟶ P₁) (j₂ : M ⟶ P₂)
    (j₁' : M' ⟶ P₁) (j₂' : M' ⟶ P₂)
    (hinj : ∀ W : Y.Opens, Function.Injective (pair j₁ j₂ W))
    (hinj' : ∀ W : Y.Opens, Function.Injective (pair j₁' j₂' W))
    (hrange : ∀ W : Y.Opens, Set.range (pair j₁ j₂ W) = Set.range (pair j₁' j₂' W)) :
    Nonempty (M ≅ M') := by
  have hle : ∀ W : Y.Opens, Set.range (pair j₁ j₂ W) ⊆ Set.range (pair j₁' j₂' W) :=
    fun W => (hrange W).le
  have hge : ∀ W : Y.Opens, Set.range (pair j₁' j₂' W) ⊆ Set.range (pair j₁ j₂ W) :=
    fun W => (hrange W).ge
  refine ⟨⟨liftHom j₁ j₂ j₁' j₂' hinj' hle, liftHom j₁' j₂' j₁ j₂ hinj hge, ?_, ?_⟩⟩
  · apply Scheme.Modules.hom_ext
    intro W
    ext m
    change lift j₁' j₂' j₁ j₂ hge W (lift j₁ j₂ j₁' j₂' hle W m) = m
    apply hinj W
    rw [pair_lift, pair_lift]
  · apply Scheme.Modules.hom_ext
    intro W
    ext m
    change lift j₁ j₂ j₁' j₂' hle W (lift j₁' j₂' j₁ j₂ hge W m) = m
    apply hinj' W
    rw [pair_lift, pair_lift]

end TwoGluedCurvesUniqAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso.TwoGluedCurvesUniqAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso.TwoGluedCurvesUniqAux"

open TwoGluedCurvesUniqAux in
theorem solution
    {κ : Type u} [Field κ]
    {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    {i₁ : SchemeHomOver c₁ x} {i₂ : SchemeHomOver c₂ x}
    {ι : Type v} {p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁} {p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂}
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} {M M' : (pullback x h).Modules}
    (hM : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M) (hM' : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M') :
    Nonempty (M ≅ M') := by
  obtain ⟨j₁, j₂, hj⟩ := hM
  obtain ⟨j₁', j₂', hj'⟩ := hM'
  refine nonempty_iso_of_range_pair_eq j₁ j₂ j₁' j₂' (fun W => (hj W).1) (fun W => (hj' W).1) ?_
  intro W
  change Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) =
    Set.range (fun m : Γ(M', W) => (j₁'.app W m, j₂'.app W m))
  rw [(hj W).2, (hj' W).2]

end S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso (solution)
