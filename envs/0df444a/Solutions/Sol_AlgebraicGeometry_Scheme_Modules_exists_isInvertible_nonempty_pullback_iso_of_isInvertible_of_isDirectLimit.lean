-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/817db2c5-40a3-5947-b8f0-5fa3b1dfb0f1

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_UnitCocycle_exists_comap_eq_of_isDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit.AlgebraicGeometry TopologicalSpace Opposite"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.pullback Scheme.Hom QuasiCompact Spec Spec.map Scheme Scheme.Hom.preimage_top Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules QuasiSeparated Scheme.Hom.preimage_iSup Scheme.Hom.comp_preimage Scheme.Modules.map_smul Scheme.Modules.pullbackComp Scheme.Modules.UnitCocycle Scheme.Modules.IsInvertible Scheme.Modules.exists_pullback_glueOfCocycle_iso Scheme.Modules.exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq Scheme.Modules.isInvertible_glueOfCocycle Scheme.Modules.UnitCocycle.exists_comap_eq_of_isDirectLimit Scheme.Modules.IsInvertible.exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit"
namespace LimitPic
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules"

theorem coeff_unique {X : Scheme.{u}} {M : X.Modules} {U W : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s W)
    (hWU : W ≤ U) {g g' : Γ(X, W)}
    (h : g • M.presheaf.map (homOfLE hWU).op s = g' • M.presheaf.map (homOfLE hWU).op s) : g = g' :=
  (hs hWU le_rfl).1 h

theorem nonempty_pullback_glueOfCocycle_iso {X X' : Scheme.{u}} (π : X' ⟶ X) {ι : Type u} [LinearOrder ι]
    {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : UnitCocycle U)
    (𝓛 : X'.Modules) (s : ∀ i, Γ(𝓛, π ⁻¹ᵁ U i)) (hs : ∀ i, IsFrameOn (s i) (π ⁻¹ᵁ U i))
    (htrans : ∀ i j, i < j →
      (c.comap π).u i j • 𝓛.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U i)).op (s i) =
        𝓛.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U j)).op (s j)) :
    Nonempty ((Scheme.Modules.pullback π).obj (glueOfCocycle c) ≅ 𝓛) := by
  obtain ⟨φ, -⟩ := AlgebraicGeometry.Scheme.Modules.exists_pullback_glueOfCocycle_iso π hU c
  have hT : ⨆ i, π ⁻¹ᵁ U i = ⊤ := π.iSup_preimage_eq_top hU
  let c' := c.comap π
  obtain ⟨e, -⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
    (fun i => π ⁻¹ᵁ U i) hT (L := glueOfCocycle c') (L' := 𝓛) (fun i => glueFrame c' i) s
    (fun i => isFrameOn_glueFrame c' i) hs (by
      intro i j hij g hg
      have hu : (c'.u i j) • (glueOfCocycle c').presheaf.map (homOfLE inf_le_left).op (glueFrame c' i) =
          (glueOfCocycle c').presheaf.map (homOfLE inf_le_right).op (glueFrame c' j) :=
        (map_glueFrame_eq_smul c' i j).symm
      have hg' : g = c'.u i j :=
        coeff_unique ((isFrameOn_glueFrame c' i).mono inf_le_left) inf_le_left (hg.trans hu.symm)
      rw [hg']
      exact htrans i j hij)
  exact ⟨φ ≪≫ e⟩

theorem nonempty_pullback_glueOfCocycle_iso' {X X' : Scheme.{u}} (π : X' ⟶ X) {ι : Type u} [LinearOrder ι]
    {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : UnitCocycle U)
    (V : ι → X'.Opens) (hV : ∀ i, π ⁻¹ᵁ U i = V i)
    (𝓛 : X'.Modules) (s : ∀ i, Γ(𝓛, V i)) (hs : ∀ i, IsFrameOn (s i) (V i))
    (htrans : ∀ i j, i < j →
      X'.presheaf.map (eqToHom (show V i ⊓ V j = π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j by rw [hV i, hV j])).op
          ((c.comap π).u i j) •
        𝓛.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (s i) =
        𝓛.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (s j)) :
    Nonempty ((Scheme.Modules.pullback π).obj (glueOfCocycle c) ≅ 𝓛) := by
  obtain rfl : V = fun i => π ⁻¹ᵁ U i := funext fun i => (hV i).symm
  refine nonempty_pullback_glueOfCocycle_iso π hU c 𝓛 s hs (fun i j hij => ?_)
  have h := htrans i j hij
  rw [eqToHom_refl, op_id, X'.presheaf.map_id] at h
  exact h

section FramesCocycle

variable {X : Scheme.{u}} {ι : Type u} (V : ι → X.Opens) (𝓛 : X.Modules)
  (s : ∀ i, Γ(𝓛, V i))

noncomputable abbrev rL {A B : X.Opens} (h : B ≤ A) : Γ(𝓛, A) → Γ(𝓛, B) :=
  fun x => 𝓛.presheaf.map (homOfLE h).op x

theorem rL_rL {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (x : Γ(𝓛, A)) :
    rL 𝓛 hCB (rL 𝓛 hBA x) = rL 𝓛 (hCB.trans hBA) x := by
  change (𝓛.presheaf.map (homOfLE hBA).op ≫ 𝓛.presheaf.map (homOfLE hCB).op) x = _
  rw [← Functor.map_comp]; rfl

theorem rL_smul {A B : X.Opens} (h : B ≤ A) (g : Γ(X, A)) (x : Γ(𝓛, A)) :
    rL 𝓛 h (g • x) = GlueOfCocycle.rO h g • rL 𝓛 h x :=
  Scheme.Modules.map_smul 𝓛 (homOfLE h) g x

noncomputable def tr (hs : ∀ i, IsFrameOn (s i) (V i)) (i j : ι) : Γ(X, V i ⊓ V j) :=
  ((hs i).existsUnique (inf_le_left : V i ⊓ V j ≤ V i) inf_le_left (rL 𝓛 inf_le_right (s j))).choose

theorem tr_spec (hs : ∀ i, IsFrameOn (s i) (V i)) (i j : ι) : tr V 𝓛 s hs i j • rL 𝓛 (inf_le_left : V i ⊓ V j ≤ V i) (s i) = rL 𝓛 inf_le_right (s j) :=
  ((hs i).existsUnique (inf_le_left : V i ⊓ V j ≤ V i) inf_le_left (rL 𝓛 inf_le_right (s j))).choose_spec.1

theorem coeff_eq (hs : ∀ i, IsFrameOn (s i) (V i)) (i : ι) {W : X.Opens} (hW : W ≤ V i) {g g' : Γ(X, W)}
    (h : g • rL 𝓛 hW (s i) = g' • rL 𝓛 hW (s i)) : g = g' :=
  coeff_unique ((hs i).mono hW) hW h

theorem tr_spec_le (hs : ∀ i, IsFrameOn (s i) (V i)) (i j : ι) {W : X.Opens} (hW : W ≤ V i ⊓ V j) :
    GlueOfCocycle.rO hW (tr V 𝓛 s hs i j) • rL 𝓛 (hW.trans inf_le_left) (s i) = rL 𝓛 (hW.trans inf_le_right) (s j) := by
  have h := congrArg (rL 𝓛 hW) (tr_spec V 𝓛 s hs i j)
  rw [rL_smul, rL_rL, rL_rL] at h
  exact h

theorem tr_refl (hs : ∀ i, IsFrameOn (s i) (V i)) (i : ι) : tr V 𝓛 s hs i i = 1 := by
  apply coeff_eq V 𝓛 s hs i (inf_le_left : V i ⊓ V i ≤ V i)
  rw [one_smul, tr_spec]

theorem tr_cocycle (hs : ∀ i, IsFrameOn (s i) (V i)) (i j k : ι) :
    GlueOfCocycle.rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) : V i ⊓ V j ⊓ V k ≤ V i ⊓ V j)
        (tr V 𝓛 s hs i j) *
      GlueOfCocycle.rO (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V i ⊓ V j ⊓ V k ≤ V j ⊓ V k)
        (tr V 𝓛 s hs j k) =
    GlueOfCocycle.rO (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V i ⊓ V j ⊓ V k ≤ V i ⊓ V k)
        (tr V 𝓛 s hs i k) := by

  have hWi : V i ⊓ V j ⊓ V k ≤ V i := inf_le_left.trans inf_le_left
  apply coeff_eq V 𝓛 s hs i hWi
  have h1 := tr_spec_le V 𝓛 s hs i j (W := V i ⊓ V j ⊓ V k)
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
  have h2 := tr_spec_le V 𝓛 s hs j k (W := V i ⊓ V j ⊓ V k) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h3 := tr_spec_le V 𝓛 s hs i k (W := V i ⊓ V j ⊓ V k) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  rw [mul_comm, ← smul_smul]
  erw [h1, h2]
  exact h3.symm

theorem exists_unitCocycle_of_frames' (hs : ∀ i, IsFrameOn (s i) (V i)) :
    ∃ g : UnitCocycle V, ∀ i j,
      g.u i j • 𝓛.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (s i) =
        𝓛.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (s j) :=
  ⟨{ u := tr V 𝓛 s hs, refl := tr_refl V 𝓛 s hs, cocycle := tr_cocycle V 𝓛 s hs }, tr_spec V 𝓛 s hs⟩

end FramesCocycle

theorem isFrameOn_cast {X : Scheme.{u}} {𝓛 : X.Modules} {V V' : X.Opens} (e : V' = V) (s : Γ(𝓛, V))
    (hs : IsFrameOn s V) : IsFrameOn (𝓛.presheaf.map (eqToHom e).op s) V' := by
  subst e
  rw [eqToHom_refl, op_id, 𝓛.presheaf.map_id]
  exact hs

end AlgebraicGeometry.LimitPic

end

open AlgebraicGeometry.LimitPic _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (𝓛 : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (j : ι) (hij : i ≤ j) (𝓛j : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))).Modules),
      Scheme.Modules.IsInvertible 𝓛j ∧
      ∀ cX : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶
          Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))),
        cX ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i))) →
        cX ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) =
          Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        Nonempty ((Scheme.Modules.pullback cX).obj 𝓛j ≅ 𝓛) := by
  classical

  have hcompat : ∀ (a b : ι) (h : a ≤ b), (g b).comp (φ a b h) = g a := fun a b h =>
    RingHom.ext fun x => hR.compatibility a b h x
  have hφφ : ∀ (a b c : ι) (hab : a ≤ b) (hbc : b ≤ c), (φ b c hbc).comp (φ a b hab) = φ a c (hab.trans hbc) :=
    fun a b c hab hbc => RingHom.ext fun x => DirectedSystem.map_map' (f := φ) hab hbc x
  have hSpec : ∀ (a b : ι) (h : a ≤ b),
      Spec.map (CommRingCat.ofHom (g b)) ≫ Spec.map (CommRingCat.ofHom (φ a b h)) = Spec.map (CommRingCat.ofHom (g a)) :=
    fun a b h => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcompat]
  have hSpecφ : ∀ (a b c : ι) (hab : a ≤ b) (hbc : b ≤ c),
      Spec.map (CommRingCat.ofHom (φ b c hbc)) ≫ Spec.map (CommRingCat.ofHom (φ a b hab)) =
        Spec.map (CommRingCat.ofHom (φ a c (hab.trans hbc))) :=
    fun a b c hab hbc => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφφ]

  obtain ⟨j₀, hij₀, n, W, hW, HW⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isAffineOpen_isFrameOn_preimage_of_isDirectLimit
      φ g hR i fX 𝓛 h𝓛

  let XR := Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))
  let prR := Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))
  let sndR := Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (g i)))
  let X₀ := Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j₀ hij₀)))
  let pr₀ := Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₀ hij₀)))
  let f₀ : X₀ ⟶ Spec (CommRingCat.of (G j₀)) := Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j₀ hij₀)))

  let c₀ : XR ⟶ X₀ := Limits.pullback.lift prR (sndR ≫ Spec.map (CommRingCat.ofHom (g j₀)))
    (by rw [Category.assoc, hSpec, Limits.pullback.condition])
  have hc₀₁ : c₀ ≫ pr₀ = prR := Limits.pullback.lift_fst _ _ _
  have hc₀₂ : c₀ ≫ f₀ = sndR ≫ Spec.map (CommRingCat.ofHom (g j₀)) := Limits.pullback.lift_snd _ _ _
  obtain ⟨hcov₀, s, hs⟩ := HW c₀ hc₀₁ hc₀₂

  haveI : QuasiCompact f₀ := inferInstance
  haveI : QuasiSeparated f₀ := inferInstance
  let X'R := Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (g j₀)))
  let pr'R := Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (g j₀)))
  let snd'R := Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (g j₀)))
  let eh : X'R ⟶ XR := Limits.pullback.lift (pr'R ≫ pr₀) snd'R (by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, Limits.pullback.condition, Category.assoc, hSpec])
  let ei : XR ⟶ X'R := Limits.pullback.lift c₀ sndR hc₀₂
  have eh₁ : eh ≫ prR = pr'R ≫ pr₀ := Limits.pullback.lift_fst _ _ _
  have eh₂ : eh ≫ sndR = snd'R := Limits.pullback.lift_snd _ _ _
  have ei₁ : ei ≫ pr'R = c₀ := Limits.pullback.lift_fst _ _ _
  have ei₂ : ei ≫ snd'R = sndR := Limits.pullback.lift_snd _ _ _
  have heh_c₀ : eh ≫ c₀ = pr'R := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hc₀₁, eh₁]
    · rw [Category.assoc, hc₀₂, ← Category.assoc, eh₂, Limits.pullback.condition]
  let e : X'R ≅ XR :=
    { hom := eh, inv := ei
      hom_inv_id := by
        apply Limits.pullback.hom_ext
        · rw [Category.assoc, ei₁, heh_c₀, Category.id_comp]
        · rw [Category.assoc, ei₂, eh₂, Category.id_comp]
      inv_hom_id := by
        apply Limits.pullback.hom_ext
        · rw [Category.assoc, eh₁, ← Category.assoc, ei₁, hc₀₁, Category.id_comp]
        · rw [Category.assoc, eh₂, ei₂, Category.id_comp] }

  let 𝓛' : X'R.Modules := (Scheme.Modules.pullback e.hom).obj 𝓛
  have h𝓛' : IsInvertible 𝓛' := h𝓛.pullback e.hom
  have hO : ∀ k, pr'R ⁻¹ᵁ W k = e.hom ⁻¹ᵁ (c₀ ⁻¹ᵁ W k) := fun k => by
    rw [← Scheme.Hom.comp_preimage]; exact congrArg (· ⁻¹ᵁ W k) heh_c₀.symm
  let s' : ∀ k, Γ(𝓛', pr'R ⁻¹ᵁ W k) := fun k =>
    𝓛'.presheaf.map (eqToHom (hO k)).op (pullbackLocalSection e.hom (s k))
  have hs' : ∀ k, IsFrameOn (s' k) (pr'R ⁻¹ᵁ W k) := fun k =>
    isFrameOn_cast (hO k) _ ((hs k).pullbackLocalSection e.hom)

  obtain ⟨gc, hgc⟩ := exists_unitCocycle_of_frames' (fun k => pr'R ⁻¹ᵁ W k) 𝓛' s' hs'
  have hW' : ∀ k, IsCompact ((W k : X₀.Opens) : Set X₀) := fun k => (hW k).isCompact
  have hcov' : (⨆ k, pr'R ⁻¹ᵁ W k) = ⊤ := by
    rw [show (fun k => pr'R ⁻¹ᵁ W k) = fun k => e.hom ⁻¹ᵁ (c₀ ⁻¹ᵁ W k) from funext hO,
      ← Scheme.Hom.preimage_iSup, hcov₀, Scheme.Hom.preimage_top]
  obtain ⟨j, hj₀j, c, hcovj, Hc⟩ :=
    AlgebraicGeometry.Scheme.Modules.UnitCocycle.exists_comap_eq_of_isDirectLimit φ g hR j₀ f₀ W hW' hcov' gc

  let X'j := Limits.pullback f₀ (Spec.map (CommRingCat.ofHom (φ j₀ j hj₀j)))
  let pr'j := Limits.pullback.fst f₀ (Spec.map (CommRingCat.ofHom (φ j₀ j hj₀j)))
  let snd'j := Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom (φ j₀ j hj₀j)))
  let cX' : X'R ⟶ X'j := Limits.pullback.lift pr'R (snd'R ≫ Spec.map (CommRingCat.ofHom (g j)))
    (by rw [Category.assoc, hSpec, Limits.pullback.condition])
  have hcX'₁ : cX' ≫ pr'j = pr'R := Limits.pullback.lift_fst _ _ _
  have hcX'₂ : cX' ≫ snd'j = snd'R ≫ Spec.map (CommRingCat.ofHom (g j)) := Limits.pullback.lift_snd _ _ _
  have hV : ∀ k, cX' ⁻¹ᵁ (pr'j ⁻¹ᵁ W k) = pr'R ⁻¹ᵁ W k := fun k => by
    rw [← Scheme.Hom.comp_preimage]; exact congrArg (· ⁻¹ᵁ W k) hcX'₁
  let 𝓛'j : X'j.Modules := glueOfCocycle c
  have h𝓛'j : IsInvertible 𝓛'j := AlgebraicGeometry.Scheme.Modules.isInvertible_glueOfCocycle hcovj c
  obtain ⟨iso₁⟩ : Nonempty ((Scheme.Modules.pullback cX').obj 𝓛'j ≅ 𝓛') := by
    refine nonempty_pullback_glueOfCocycle_iso' cX' hcovj c (fun k => pr'R ⁻¹ᵁ W k) hV 𝓛' s' hs' ?_
    intro a b hab
    rw [← hgc a b]
    congr 1
    exact Hc cX' hcX'₁ hcX'₂ a b _

  let Xj := Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j (hij₀.trans hj₀j))))
  let prj := Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j (hij₀.trans hj₀j))))
  let sndj := Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j (hij₀.trans hj₀j))))

  let d : Xj ⟶ X₀ := Limits.pullback.lift prj (sndj ≫ Spec.map (CommRingCat.ofHom (φ j₀ j hj₀j)))
    (by rw [Category.assoc, hSpecφ, Limits.pullback.condition])
  have hd₁ : d ≫ pr₀ = prj := Limits.pullback.lift_fst _ _ _
  have hd₂ : d ≫ f₀ = sndj ≫ Spec.map (CommRingCat.ofHom (φ j₀ j hj₀j)) := Limits.pullback.lift_snd _ _ _
  let ejh : X'j ⟶ Xj := Limits.pullback.lift (pr'j ≫ pr₀) snd'j (by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, Limits.pullback.condition, Category.assoc, hSpecφ])
  let eji : Xj ⟶ X'j := Limits.pullback.lift d sndj hd₂
  have ejh₁ : ejh ≫ prj = pr'j ≫ pr₀ := Limits.pullback.lift_fst _ _ _
  have ejh₂ : ejh ≫ sndj = snd'j := Limits.pullback.lift_snd _ _ _
  have eji₁ : eji ≫ pr'j = d := Limits.pullback.lift_fst _ _ _
  have eji₂ : eji ≫ snd'j = sndj := Limits.pullback.lift_snd _ _ _
  have hejh_d : ejh ≫ d = pr'j := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hd₁, ejh₁]
    · rw [Category.assoc, hd₂, ← Category.assoc, ejh₂, Limits.pullback.condition]
  let ej : X'j ≅ Xj :=
    { hom := ejh, inv := eji
      hom_inv_id := by
        apply Limits.pullback.hom_ext
        · rw [Category.assoc, eji₁, hejh_d, Category.id_comp]
        · rw [Category.assoc, eji₂, ejh₂, Category.id_comp]
      inv_hom_id := by
        apply Limits.pullback.hom_ext
        · rw [Category.assoc, ejh₁, ← Category.assoc, eji₁, hd₁, Category.id_comp]
        · rw [Category.assoc, ejh₂, eji₂, Category.id_comp] }
  let 𝓛j : Xj.Modules := (Scheme.Modules.pullback ej.inv).obj 𝓛'j
  refine ⟨j, hij₀.trans hj₀j, 𝓛j, h𝓛'j.pullback ej.inv, fun cX h1 h2 => ?_⟩

  haveI : Mono ej.hom := (Iso.isIso_hom ej).mono_of_iso
  have hkey : cX ≫ ej.inv = e.inv ≫ cX' := by
    rw [← cancel_mono ej.hom, Category.assoc, ej.inv_hom_id, Category.comp_id, Category.assoc]
    apply Limits.pullback.hom_ext
    · rw [h1, Category.assoc, Category.assoc, ejh₁, ← Category.assoc cX', hcX'₁]
      change prR = e.inv ≫ pr'R ≫ pr₀
      rw [← eh₁, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    · rw [h2, Category.assoc, Category.assoc, ejh₂, hcX'₂]
      change sndR ≫ _ = e.inv ≫ snd'R ≫ _
      rw [← eh₂, ← Category.assoc, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  refine ⟨(Scheme.Modules.pullbackComp cX ej.inv).app 𝓛'j ≪≫ (Scheme.Modules.pullbackCongr hkey).app 𝓛'j ≪≫
    ((Scheme.Modules.pullbackComp e.inv cX').app 𝓛'j).symm ≪≫ (Scheme.Modules.pullback e.inv).mapIso iso₁ ≪≫
    (Scheme.Modules.pullbackComp e.inv e.hom).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr e.inv_hom_id).app 𝓛 ≪≫
    (Scheme.Modules.pullbackId XR).app 𝓛⟩

end S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit (solution)
