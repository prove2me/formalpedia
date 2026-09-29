-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullback_locally_mem_span_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8a9c1e7f-a614-5f17-b68d-e60b3b026f91

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.Hom.zero_app ringCatSheaf Modules.pullback Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules.pullbackPushforwardAdjunction Modules Opens Modules.map_smul PresheafOfModules"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.zero_app pushforward pullback presheaf Hom.comp_app Hom mapPresheaf_app Hom.app isSheaf pullbackPushforwardAdjunction map_smul"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PullbackGen

variable {X Y : Scheme.{u}} (ψ : X ⟶ Y) (E : Y.Modules)

noncomputable abbrev F : X.Modules := (Modules.pullback ψ).obj E

noncomputable abbrev res (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) : Γ(M, W) → Γ(M, W') :=
  fun y => M.presheaf.map (homOfLE h).op y

omit E in
lemma res_res (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (y : Γ(M, W₁)) :
    res M h₃₂ (res M h₂₁ y) = res M (h₃₂.trans h₂₁) y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]
  rfl

omit E in
lemma res_eq_map (M : X.Modules) {W' W : X.Opens} (f : W' ⟶ W) (y : Γ(M, W)) :
    M.presheaf.map f.op y = res M f.le y := by
  rw [Subsingleton.elim f (homOfLE f.le)]

omit E in
lemma res_smul (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (y : Γ(M, W)) :
    res M h (r • y) = X.presheaf.map (homOfLE h).op r • res M h y :=
  Modules.map_smul M (homOfLE h) r y

omit E in
lemma res_add (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (y z : Γ(M, W)) :
    res M h (y + z) = res M h y + res M h z := map_add _ y z

omit E in
lemma res_zero (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) : res M h (0 : Γ(M, W)) = 0 := map_zero _

noncomputable def eta (U : Y.Opens) (e : Γ(E, U)) : Γ(F ψ E, ψ ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction ψ).unit.app E).app U e

lemma res_eta {U U' : Y.Opens} (h : U' ≤ U) (e : Γ(E, U)) :
    res (F ψ E) (ψ.preimage_mono h) (eta ψ E U e) = eta ψ E U' (E.presheaf.map (homOfLE h).op e) := by
  have hnat := ((pullbackPushforwardAdjunction ψ).unit.app E).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hnat e
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx

  exact ((res_eq_map (F ψ E) ((Opens.map ψ.base).map (homOfLE h)) _).symm).trans hx.symm

noncomputable def span₁ (U : Y.Opens) (W : X.Opens) (j : W ≤ ψ ⁻¹ᵁ U) : Submodule Γ(X, W) Γ(F ψ E, W) :=
  Submodule.span Γ(X, W) (Set.range fun e : Γ(E, U) => res (F ψ E) j (eta ψ E U e))

noncomputable def spanAll (W : X.Opens) : Submodule Γ(X, W) Γ(F ψ E, W) :=
  Submodule.span Γ(X, W)
    {y | ∃ (U : Y.Opens) (j : W ≤ ψ ⁻¹ᵁ U) (e : Γ(E, U)), y = res (F ψ E) j (eta ψ E U e)}

lemma eta_res_mem_spanAll {U : Y.Opens} {W : X.Opens} (j : W ≤ ψ ⁻¹ᵁ U) (e : Γ(E, U)) :
    res (F ψ E) j (eta ψ E U e) ∈ spanAll ψ E W :=
  Submodule.subset_span ⟨U, j, e, rfl⟩

lemma res_mem_spanAll {W' W : X.Opens} (h : W' ≤ W) {y : Γ(F ψ E, W)} (hy : y ∈ spanAll ψ E W) :
    res (F ψ E) h y ∈ spanAll ψ E W' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨U, j, e, rfl⟩ := hz
    rw [res_res]
    exact eta_res_mem_spanAll ψ E (h.trans j) e
  | zero => rw [res_zero]; exact zero_mem _
  | add z₁ z₂ _ _ h₁ h₂ => rw [res_add]; exact add_mem h₁ h₂
  | smul r z _ hz => rw [res_smul]; exact Submodule.smul_mem _ _ hz

lemma res_mem_span₁ {U U₁ : Y.Opens} {W W₁ : X.Opens} (hU : U ≤ U₁) (hW : W ≤ W₁) (j₁ : W₁ ≤ ψ ⁻¹ᵁ U₁)
    (j : W ≤ ψ ⁻¹ᵁ U) {y : Γ(F ψ E, W₁)} (hy : y ∈ span₁ ψ E U₁ W₁ j₁) :
    res (F ψ E) hW y ∈ span₁ ψ E U W j := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, rfl⟩ := hz
    rw [res_res]
    have : res (F ψ E) (hW.trans j₁) (eta ψ E U₁ e) =
        res (F ψ E) j (eta ψ E U (E.presheaf.map (homOfLE hU).op e)) := by
      rw [← res_eta, res_res]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [res_zero]; exact zero_mem _
  | add z₁ z₂ _ _ h₁ h₂ => rw [res_add]; exact add_mem h₁ h₂
  | smul r z _ hz => rw [res_smul]; exact Submodule.smul_mem _ _ hz

noncomputable def locSpan (W : X.Opens) : Submodule Γ(X, W) Γ(F ψ E, W) where
  carrier := {y | ∀ x ∈ W, ∃ (W' : X.Opens) (i : W' ≤ W), x ∈ W' ∧ res (F ψ E) i y ∈ spanAll ψ E W'}
  zero_mem' := fun x hx => ⟨W, le_rfl, hx, by rw [res_zero]; exact zero_mem _⟩
  add_mem' := by
    intro y z hy hz x hx
    obtain ⟨W₁, i₁, hx₁, h₁⟩ := hy x hx
    obtain ⟨W₂, i₂, hx₂, h₂⟩ := hz x hx
    refine ⟨W₁ ⊓ W₂, inf_le_left.trans i₁, ⟨hx₁, hx₂⟩, ?_⟩
    rw [res_add]
    refine add_mem ?_ ?_
    · rw [← res_res (F ψ E) i₁ inf_le_left]; exact res_mem_spanAll ψ E _ h₁
    · rw [← res_res (F ψ E) i₂ inf_le_right]; exact res_mem_spanAll ψ E _ h₂
  smul_mem' := by
    intro r y hy x hx
    obtain ⟨W₁, i₁, hx₁, h₁⟩ := hy x hx
    refine ⟨W₁, i₁, hx₁, ?_⟩
    rw [res_smul]
    exact Submodule.smul_mem _ _ h₁

lemma res_mem_locSpan {W' W : X.Opens} (h : W' ≤ W) {y : Γ(F ψ E, W)} (hy : y ∈ locSpan ψ E W) :
    res (F ψ E) h y ∈ locSpan ψ E W' := by
  intro x hx
  obtain ⟨W₁, i₁, hx₁, h₁⟩ := hy x (h hx)
  refine ⟨W₁ ⊓ W', inf_le_right, ⟨hx₁, hx⟩, ?_⟩
  rw [res_res, ← res_res (F ψ E) i₁ inf_le_left]
  exact res_mem_spanAll ψ E _ h₁

lemma eta_mem_locSpan (U : Y.Opens) (e : Γ(E, U)) : eta ψ E U e ∈ locSpan ψ E (ψ ⁻¹ᵁ U) := by
  intro x hx
  refine ⟨ψ ⁻¹ᵁ U, le_rfl, hx, ?_⟩
  exact eta_res_mem_spanAll ψ E le_rfl e

end PullbackGen

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.Hom.zero_app ringCatSheaf Modules.pullback Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules.pullbackPushforwardAdjunction Modules Opens Modules.map_smul PresheafOfModules"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.zero_app pushforward pullback presheaf Hom.comp_app Hom mapPresheaf_app Hom.app isSheaf pullbackPushforwardAdjunction map_smul"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PullbackGen

variable {X Y : Scheme.{u}} (ψ : X ⟶ Y) (E : Y.Modules)

omit E in
lemma map_eq_res (M : X.Modules) {W W' : (X.Opens)ᵒᵖ} (f : W ⟶ W') (y : Γ(M, W.unop)) :
    M.presheaf.map f y = res M f.unop.le y :=
  res_eq_map M f.unop y

noncomputable def locSpanAb : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (locSpan ψ E W.unop)
  map {W W'} f := AddCommGrpCat.ofHom (X := locSpan ψ E W.unop) (Y := locSpan ψ E W'.unop)
    { toFun := fun y => ⟨(F ψ E).presheaf.map f y.1, by
        rw [map_eq_res]; exact res_mem_locSpan ψ E f.unop.le y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun y z => Subtype.ext (map_add _ _ _) }
  map_id W := by
    ext y
    change (F ψ E).presheaf.map (𝟙 W) y.1 = y.1
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext y
    change (F ψ E).presheaf.map (f ≫ g) y.1 = (F ψ E).presheaf.map g ((F ψ E).presheaf.map f y.1)
    rw [CategoryTheory.Functor.map_comp]
    rfl

@[scoped simp] lemma locSpanAb_map_apply_val {W W' : (X.Opens)ᵒᵖ} (f : W ⟶ W') (y : locSpan ψ E W.unop) :
    ((locSpanAb ψ E).map f y).1 = (F ψ E).presheaf.map f y.1 := rfl

noncomputable scoped instance instModuleLocSpanAb (W : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj W) ((locSpanAb ψ E).obj W) :=
  inferInstanceAs (Module Γ(X, W.unop) (locSpan ψ E W.unop))

lemma isSheaf_locSpanAb : TopCat.Presheaf.IsSheaf (locSpanAb ψ E) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X.carrier := ⟨(F ψ E).presheaf, (F ψ E).isSheaf⟩
  let tf : ∀ i, Γ(F ψ E, U i) := fun i => (sf i).1
  have htf : TopCat.Presheaf.IsCompatible Fsh.1 U tf := fun i j => congrArg Subtype.val (hsf i j)
  obtain ⟨t, ht, huniq⟩ := Fsh.existsUnique_gluing U tf htf
  have hmem : t ∈ locSpan ψ E (iSup U) := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨W', i', hx', h'⟩ := (sf i).2 x hi
    refine ⟨W', i'.trans (le_iSup U i), hx', ?_⟩
    rw [← res_res (F ψ E) (le_iSup U i) i']
    have hti : res (F ψ E) (le_iSup U i) t = tf i := by
      rw [← ht i]; exact (res_eq_map (F ψ E) _ t).symm
    rw [hti]
    exact h'
  refine ⟨⟨t, hmem⟩, fun i => Subtype.ext (ht i), fun s hs => Subtype.ext (huniq s.1 fun i => ?_)⟩
  exact congrArg Subtype.val (hs i)

noncomputable def G : X.Modules where
  val := @PresheafOfModules.ofPresheaf _ _ X.ringCatSheaf.obj (locSpanAb ψ E) (instModuleLocSpanAb ψ E)
    (fun W W' f r m => Subtype.ext (Modules.map_smul (F ψ E) f.unop r m.1))
  isSheaf := isSheaf_locSpanAb ψ E

noncomputable def incl : G ψ E ⟶ F ψ E :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (X := locSpan ψ E W.unop) (Y := Γ(F ψ E, W.unop))
        (locSpan ψ E W.unop).subtype.toAddMonoidHom
      naturality := fun W W' f => rfl }
    (fun W r m => rfl)⟩

@[scoped simp] lemma incl_app_apply (W : X.Opens) (y : locSpan ψ E W) :
    (incl ψ E).app W (show Γ(G ψ E, W) from y) = y.1 := rfl

scoped instance : Mono (incl ψ E) := ⟨fun a b h => by
  refine Modules.hom_ext _ _ fun W => ?_
  ext z
  apply Subtype.ext
  have := congrArg (fun φ => (Modules.Hom.app φ W) z) h
  simp only [Modules.Hom.comp_app] at this
  exact this⟩

scoped instance : Epi (incl ψ E) := by
  refine Preadditive.epi_of_cancel_zero _ fun {R} g hg => ?_
  apply ((pullbackPushforwardAdjunction ψ).homEquiv E R).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_zero]
  refine Eq.trans ?_ (Limits.comp_zero).symm
  refine Modules.hom_ext _ _ fun U => ?_
  rw [Modules.Hom.comp_app, Modules.Hom.zero_app]
  change Hom.app ((pullbackPushforwardAdjunction ψ).unit.app E) U ≫ g.app (ψ ⁻¹ᵁ U) = 0
  ext e
  change g.app (ψ ⁻¹ᵁ U) (eta ψ E U e) = (0 : Γ(E, U) ⟶ Γ(R, ψ ⁻¹ᵁ U)) e
  have h2 := congrArg (fun φ => (Modules.Hom.app φ (ψ ⁻¹ᵁ U)) (show Γ(G ψ E, ψ ⁻¹ᵁ U) from
    (⟨eta ψ E U e, eta_mem_locSpan ψ E U e⟩ : locSpan ψ E (ψ ⁻¹ᵁ U)))) hg
  simp only [Modules.Hom.comp_app, Modules.Hom.zero_app] at h2
  have h3 : g.app (ψ ⁻¹ᵁ U) (eta ψ E U e) = 0 := by
    refine Eq.trans ?_ (h2.trans ?_)
    · rfl
    · rfl
  rw [h3]
  rfl

scoped instance : IsIso (incl ψ E) := isIso_of_mono_of_epi _

lemma mem_locSpan (W : X.Opens) (y : Γ(F ψ E, W)) : y ∈ locSpan ψ E W := by
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso ((incl ψ E).app W)).2 y
  rw [← hz]
  exact (show locSpan ψ E W from z).2

theorem main {W : X.Opens} (y : Γ(F ψ E, W)) {x : X} (hx : x ∈ W) {U₀ : Y.Opens} (hU₀ : ψ.base x ∈ U₀) :
    ∃ (U : Y.Opens) (W' : X.Opens) (i : W' ≤ W) (j : W' ≤ ψ ⁻¹ᵁ U), U ≤ U₀ ∧ x ∈ W' ∧
      res (F ψ E) i y ∈ span₁ ψ E U W' j := by
  obtain ⟨W₁, i₁, hx₁, h₁⟩ := mem_locSpan ψ E W y x hx
  suffices H : ∀ z ∈ spanAll ψ E W₁, ∃ (U : Y.Opens) (W' : X.Opens) (i : W' ≤ W₁) (j : W' ≤ ψ ⁻¹ᵁ U),
      U ≤ U₀ ∧ x ∈ W' ∧ res (F ψ E) i z ∈ span₁ ψ E U W' j by
    obtain ⟨U, W', i, j, hU, hxW', hmem⟩ := H _ h₁
    exact ⟨U, W', i.trans i₁, j, hU, hxW', by rwa [res_res] at hmem⟩
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨U, j, e, rfl⟩ := hz
    refine ⟨U ⊓ U₀, W₁ ⊓ ψ ⁻¹ᵁ (U ⊓ U₀), inf_le_left, inf_le_right, inf_le_right,
      ⟨hx₁, ⟨j hx₁, hU₀⟩⟩, ?_⟩
    exact res_mem_span₁ ψ E inf_le_left inf_le_left j inf_le_right (Submodule.subset_span ⟨e, rfl⟩)
  | zero =>
    exact ⟨U₀, W₁ ⊓ ψ ⁻¹ᵁ U₀, inf_le_left, inf_le_right, le_rfl, ⟨hx₁, hU₀⟩,
      by rw [res_zero]; exact zero_mem _⟩
  | add z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨U₁, W₁', i₁', j₁', hU₁, hx₁', hm₁⟩ := h₁
    obtain ⟨U₂, W₂', i₂', j₂', hU₂, hx₂', hm₂⟩ := h₂
    have j' : W₁' ⊓ W₂' ≤ ψ ⁻¹ᵁ (U₁ ⊓ U₂) := fun p hp => ⟨j₁' hp.1, j₂' hp.2⟩
    refine ⟨U₁ ⊓ U₂, W₁' ⊓ W₂', inf_le_left.trans i₁', j', inf_le_left.trans hU₁, ⟨hx₁', hx₂'⟩, ?_⟩
    rw [res_add]
    refine add_mem ?_ ?_
    · rw [← res_res (F ψ E) i₁' inf_le_left]
      exact res_mem_span₁ ψ E inf_le_left inf_le_left j₁' j' hm₁
    · rw [← res_res (F ψ E) i₂' inf_le_right]
      exact res_mem_span₁ ψ E inf_le_right inf_le_right j₂' j' hm₂
  | smul r z _ hz =>
    obtain ⟨U, W', i, j, hU, hxW', hm⟩ := hz
    exact ⟨U, W', i, j, hU, hxW', by rw [res_smul]; exact Submodule.smul_mem _ _ hm⟩

end PullbackGen
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry.Scheme.Modules.PullbackGen"

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry.Scheme.Modules.PullbackGen P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry.Scheme.Modules.PullbackGen P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry.Scheme.Modules.PullbackGen P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.AlgebraicGeometry"

theorem solution
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) (E : Y.Modules) {W : X.Opens}
    (y : Γ((Scheme.Modules.pullback ψ).obj E, W)) {x : X} (hx : x ∈ W)
    {U₀ : Y.Opens} (hU₀ : ψ.base x ∈ U₀) :
    ∃ (U : Y.Opens) (W' : X.Opens) (i : W' ≤ W) (j : W' ≤ ψ ⁻¹ᵁ U), U ≤ U₀ ∧ x ∈ W' ∧
      ((Scheme.Modules.pullback ψ).obj E).presheaf.map (homOfLE i).op y ∈
        Submodule.span Γ(X, W') (Set.range fun e : Γ(E, U) =>
          ((Scheme.Modules.pullback ψ).obj E).presheaf.map (homOfLE j).op
            ((((Scheme.Modules.pullbackPushforwardAdjunction ψ).unit.app E).app U e :
              Γ((Scheme.Modules.pullback ψ).obj E, ψ ⁻¹ᵁ U)))) :=
  AlgebraicGeometry.Scheme.Modules.PullbackGen.main ψ E y hx hU₀

end S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit (solution)
