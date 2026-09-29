-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_normModule_frameKit_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/23b6d71e-675e-55e6-8203-d5cb2023c8e9

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isFrameOn_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_Algebra_norm_eq_norm_fst_mul_norm_snd_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS"
p2m_attr_erase "instance" "PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace"
p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry.Scheme.Modules"

set_option backward.isDefEq.respectTransparency false

namespace N2Assembly

variable {X Y : Scheme.{u}}

namespace Frame

variable {Z : Scheme.{u}} {M : Z.Modules} {U : Z.Opens}

theorem map_map {V₁ V₂ V₃ : Z.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem exists_isUnit_smul_eq {s s' : Γ(M, U)} {V : Z.Opens}
    (hs : IsFrameOn s V) (hs' : IsFrameOn s' V) {W : Z.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    ∃ u : Γ(Z, W), IsUnit u ∧
      u • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU).op s' := by
  obtain ⟨u, hu⟩ := (hs hWU hWV).2 (M.presheaf.map (homOfLE hWU).op s')
  obtain ⟨w, hw⟩ := (hs' hWU hWV).2 (M.presheaf.map (homOfLE hWU).op s)
  refine ⟨u, ?_, hu⟩
  have h1 : (w * u) • M.presheaf.map (homOfLE hWU).op s =
      (1 : Γ(Z, W)) • M.presheaf.map (homOfLE hWU).op s := by
    rw [mul_smul, one_smul]
    simp only at hu hw
    rw [hu, hw]
  have hwu : w * u = 1 := (hs hWU hWV).1 h1
  exact ⟨⟨u, w, (mul_comm u w).trans hwu, hwu⟩, rfl⟩

set_option maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem exists_isUnit_smul_eq' {s s' : Γ(M, U)} (hs : IsFrameOn s U) (hs' : IsFrameOn s' U) :
    ∃ u : Γ(Z, U), IsUnit u ∧ u • s = s' := by
  obtain ⟨u, hu, h⟩ := exists_isUnit_smul_eq hs hs' (le_refl U) (le_refl U)
  refine ⟨u, hu, ?_⟩
  have e : ∀ t : Γ(M, U), M.presheaf.map (homOfLE (le_refl U)).op t = t := fun t => by
    rw [Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id, M.presheaf.map_id]; rfl
  rwa [e, e] at h

end Frame

section P1
variable {P Q : Y.Modules} {V : Y.Opens}

theorem exists_unique_ihomSection (p : Γ(P, V)) (hp : IsFrameOn p V) (q : Γ(Q, V)) :
    ∃! θ : Γ((ihom P).obj Q, V), ihomEval P Q V p θ = q :=
  Scheme.Modules.IsFrameOn.existsUnique_ihomEval_eq hp q

theorem ihomSection_eq_of_ihomEval_eq (p : Γ(P, V)) (hp : IsFrameOn p V)
    {θ θ' : Γ((ihom P).obj Q, V)} (h : ihomEval P Q V p θ = ihomEval P Q V p θ') : θ = θ' :=
  (Scheme.Modules.IsFrameOn.existsUnique_ihomEval_eq hp (ihomEval P Q V p θ')).unique h rfl

end P1

section P4
variable {P Q : Y.Modules}

theorem isIso_of_frames (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → Y.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, IsFrameOn (q i) (𝒱 i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ :=
  Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top μ 𝒱 hcov p q hp hq hμ

end P4

structure NormFrameKit (π : X ⟶ Y) (d : ℕ) where
  good : Y.Opens → Prop
  good_of_le : ∀ ⦃W W' : Y.Opens⦄, good W → W' ≤ W → good W'
  exists_good : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ good W
  Nm : ∀ ⦃W : Y.Opens⦄, good W → (Γ(X, π ⁻¹ᵁ W) →* Γ(Y, W))
  nf : ∀ (M : X.Modules) ⦃W : Y.Opens⦄, good W → Γ(M, π ⁻¹ᵁ W) → Γ(normModule π d M, W)
  isFrameOn_nf : ∀ (M : X.Modules) ⦃W : Y.Opens⦄ (hW : good W) (s : Γ(M, π ⁻¹ᵁ W)),
    IsFrameOn s (π ⁻¹ᵁ W) → IsFrameOn (nf M hW s) W
  map_nf : ∀ (M : X.Modules) ⦃W W' : Y.Opens⦄ (hW : good W) (hW'W : W' ≤ W) (s : Γ(M, π ⁻¹ᵁ W)),
    (normModule π d M).presheaf.map (homOfLE hW'W).op (nf M hW s) =
      nf M (good_of_le hW hW'W) (M.presheaf.map (homOfLE (π.preimage_mono hW'W)).op s)
  nf_smul : ∀ (M : X.Modules) ⦃W : Y.Opens⦄ (hW : good W) (v : Γ(X, π ⁻¹ᵁ W)) (s : Γ(M, π ⁻¹ᵁ W)),
    IsUnit v → IsFrameOn s (π ⁻¹ᵁ W) → nf M hW (v • s) = Nm hW v • nf M hW s

theorem exists_isFrameOn_preimage (π : X ⟶ Y) [IsFinite π] {L : X.Modules} (hL : IsInvertible L) (y : Y) :
    ∃ (W : Y.Opens) (s : Γ(L, π ⁻¹ᵁ W)), y ∈ W ∧ IsFrameOn s (π ⁻¹ᵁ W) := by
  obtain ⟨W, hy, ⟨e⟩⟩ := hL.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π y
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit (π ⁻¹ᵁ W) e
  exact ⟨W, s, hy, hs⟩

end N2Assembly

namespace N2Adapter

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}} {P : X.Modules} {U V : X.Opens}

theorem dual_unique {p : Γ(P, V)} (hp : IsFrameOn p V) {q q' : Γ(dual P, V)}
    (hq : ihomEval P (𝟙_ X.Modules) V p q = unitSection V)
    (hq' : ihomEval P (𝟙_ X.Modules) V p q' = unitSection V) : q = q' :=
  N2Assembly.ihomSection_eq_of_ihomEval_eq (Q := 𝟙_ X.Modules) p hp (hq.trans hq'.symm)

theorem smul_dual_eq {p : Γ(P, V)} (hp : IsFrameOn p V) (c : Γ(X, V)) {q q' : Γ(dual P, V)}
    (hq : ihomEval P (𝟙_ X.Modules) V p q = unitSection V)
    (hq' : ihomEval P (𝟙_ X.Modules) V (c • p) q' = unitSection V) : c • q' = q := by
  apply dual_unique hp _ hq
  rw [ihomEval_smul_right, ← ihomEval_smul_left, hq']

theorem ihomEval_map_dual {p : Γ(P, V)} {q : Γ(dual P, V)}
    (hq : ihomEval P (𝟙_ X.Modules) V p q = unitSection V) {W : X.Opens} (h : W ≤ V) :
    ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE h).op p)
      ((dual P).presheaf.map (homOfLE h).op q) = unitSection W := by
  have := map_ihomEval (M := P) (N := 𝟙_ X.Modules) (homOfLE h) p q
  rw [hq, map_unitSection] at this
  exact this.symm

theorem map_dual_eq {p : Γ(P, V)} (hp : IsFrameOn p V) {q : Γ(dual P, V)}
    (hq : ihomEval P (𝟙_ X.Modules) V p q = unitSection V) {W : X.Opens} (h : W ≤ V)
    {qW : Γ(dual P, W)}
    (hqW : ihomEval P (𝟙_ X.Modules) W (P.presheaf.map (homOfLE h).op p) qW = unitSection W) :
    (dual P).presheaf.map (homOfLE h).op q = qW :=
  dual_unique ((hp.map (homOfLE h)).mono h) (ihomEval_map_dual hq h) hqW

end N2Adapter

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Modules.pushforward Scheme.Modules.pullback IsFinite IsIntegral Scheme Flat IsClosedImmersion Scheme.Modules LocallyOfFinitePresentation Scheme.Modules.normModule Scheme.Modules.presheafExteriorPower Scheme.Modules.det Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.IsFrameOn Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit Scheme.Modules.IsFrameOn.existsUnique_ihomEval_eq Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pushforward Modules.pullback Γ empty Modules Opens grothendieckTopology Modules.map_smul restrict PresheafOfModules Modules.normModule Modules.presheafExteriorPower Modules.det Modules.IsInvertible Modules.pullbackUnitIso Modules.IsFrameOn Modules.exists_isFrameOn_of_pullback_iso_unit Modules.IsFrameOn.existsUnique_ihomEval_eq Modules.isIso_of_isFrameOn_of_iSup_eq_top Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback presheaf isSheaf restrict map_smul normModule presheafExteriorPower exteriorPower det dual IsInvertible pullbackUnitIso tensorSections tensorSections_smul_left tensorSections_smul_right map_homOfLE_tensorSections unitSection map_unitSection IsFrameOn ihomEval map_ihomEval ihomEval_smul_left ihomEval_smul_right IsLocallyFreeOfRank pullbackLocalSection pullbackLocalSection_smul map_homOfLE_pullbackLocalSection IsFrameOn.tensorSections exists_isFrameOn_of_pullback_iso_unit IsFrameOn.existsUnique_ihomEval_eq isIso_of_isFrameOn_of_iSup_eq_top isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver isFrameOn_sheafificationAdjunction_unit_iotaMulti IsFrameOn.exists_isFrameOn_dual IsFrameOn.exists_isFrameOn_normModule sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul"
namespace Ws31H1
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry Opposite TopologicalSpace"

section ModuleLevel

open Set Set.powersetCard

@[reducible] noncomputable def uniquePowersetCardFin (n : ℕ) : Unique (Set.powersetCard (Fin n) n) where
  default := Set.powersetCard.ofCard (n := n) (s := (Finset.univ : Finset (Fin n))) (by simp)
  uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by
    rw [Fintype.card_fin]; exact Set.powersetCard.card_eq s))

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {n : ℕ}

lemma exists_basis_exteriorPower_top (b : Module.Basis (Fin n) A M) :
    ∃ B : Module.Basis (Set.powersetCard (Fin n) n) A (⋀[A]^n M), ∀ s, B s = exteriorPower.ιMulti A n b := by
  letI := uniquePowersetCardFin n
  let φ : Fin n ↪o Fin n := ofFinEmbEquiv.symm (default : Set.powersetCard (Fin n) n)
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective φ (Finite.injective_iff_bijective.1 φ.injective)
  refine ⟨(b.reindex σ).exteriorPower n, fun s => ?_⟩
  rw [Subsingleton.elim s default, exteriorPower.basis_apply]
  change exteriorPower.ιMulti A n ((b.reindex σ) ∘ σ) = _
  congr 1
  funext i
  simp

lemma exists_eq_smul_ιMulti (b : Module.Basis (Fin n) A M) (x : ⋀[A]^n M) :
    ∃ r : A, x = r • exteriorPower.ιMulti A n b := by
  letI := uniquePowersetCardFin n
  obtain ⟨B, hB⟩ := exists_basis_exteriorPower_top b
  refine ⟨B.repr x default, ?_⟩
  conv_lhs => rw [← B.sum_repr x]
  rw [Fintype.sum_unique, hB]

lemma smul_ιMulti_injective (b : Module.Basis (Fin n) A M) :
    Function.Injective fun r : A => r • exteriorPower.ιMulti A n b := by
  letI := uniquePowersetCardFin n
  obtain ⟨B, hB⟩ := exists_basis_exteriorPower_top b
  intro r r' h
  have h' := congrArg (fun y => B.repr y default) h
  simp only [← hB default] at h'
  simpa [Module.Basis.repr_self] using h'

end ModuleLevel

variable {X : Scheme.{u}} (n : ℕ)

noncomputable abbrev pre (M : X.Modules) : X.PresheafOfModules :=
  (presheafExteriorPower X n).obj M.val

noncomputable def toSh (M : X.Modules) (W : X.Opens) :
    (⋀[Γ(X, W)]^n Γ(M, W)) → Γ(det n M, W) :=
  fun w => ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n M)).app
    (op W) (show (pre n M).obj (op W) from w)

lemma toSh_add (M : X.Modules) (W : X.Opens) (w w' : ⋀[Γ(X, W)]^n Γ(M, W)) :
    toSh n M W (w + w') = toSh n M W w + toSh n M W w' :=
  map_add (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n M)).app
    (op W)).hom _ _

lemma toSh_zero (M : X.Modules) (W : X.Opens) : toSh n M W 0 = 0 :=
  map_zero (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n M)).app
    (op W)).hom

lemma toSh_smul (M : X.Modules) (W : X.Opens) (r : Γ(X, W)) (w : ⋀[Γ(X, W)]^n Γ(M, W)) :
    toSh n M W (r • w) = r • toSh n M W w :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre n M)).app
    (op W)).hom.map_smul r _

private noncomputable abbrev _root_.AlgebraicGeometry.Scheme.Modules.Ws31H1.res (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (s : Γ(M, W)) : Γ(M, W') :=
  M.presheaf.map (homOfLE h).op s

p2m_export "AlgebraicGeometry.Scheme.Modules.Ws31H1" "res"
lemma res_res (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (s : Γ(M, W₁)) : res M h₃₂ (res M h₂₁ s) = res M (h₃₂.trans h₂₁) s := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma res_smul (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (s : Γ(M, W)) :
    res M h (r • s) = X.presheaf.map (homOfLE h).op r • res M h s :=
  Modules.map_smul M (homOfLE h) r s

noncomputable abbrev preMap (M : X.Modules) {W W' : X.Opens} (j : W' ⟶ W)
    (w : ⋀[Γ(X, W)]^n Γ(M, W)) : ⋀[Γ(X, W')]^n Γ(M, W') :=
  show ⋀[Γ(X, W')]^n Γ(M, W') from (pre n M).map j.op (show (pre n M).obj (op W) from w)

lemma preMap_ιMulti (M : X.Modules) {W W' : X.Opens} (j : W' ⟶ W) (m : Fin n → Γ(M, W)) :
    preMap n M j (exteriorPower.ιMulti _ n m) =
      exteriorPower.ιMulti _ n (fun k => (M.presheaf.map j.op : Γ(M, W) ⟶ _) (m k)) :=
  PresheafOfModules.exteriorPower_map_ιMulti n M.val j.op m

lemma preMap_smul (M : X.Modules) {W W' : X.Opens} (j : W' ⟶ W)
    (r : Γ(X, W)) (w : ⋀[Γ(X, W)]^n Γ(M, W)) :
    preMap n M j (r • w) = X.presheaf.map j.op r • preMap n M j w :=
  (pre n M).map_smul j.op r (show (pre n M).obj (op W) from w)

lemma preMap_zero (M : X.Modules) {W W' : X.Opens} (j : W' ⟶ W) :
    preMap n M j (0 : ⋀[Γ(X, W)]^n Γ(M, W)) = 0 :=
  map_zero ((pre n M).map j.op).hom

lemma res_toSh (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W) (w : ⋀[Γ(X, W)]^n Γ(M, W)) :
    res (det n M) h (toSh n M W w) = toSh n M W' (preMap n M (homOfLE h) w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (pre n M))).naturality (homOfLE h).op
  have hx := congrArg (fun φ => φ.hom (show (pre n M).obj (op W) from w)) hnat
  exact hx.symm

lemma toSh_locally_injective (M : X.Modules) {W : X.Opens} (w w' : ⋀[Γ(X, W)]^n Γ(M, W))
    (h : toSh n M W w = toSh n M W w') (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ preMap n M (homOfLE i) w = preMap n M (homOfLE i) w' := by
  have hli : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n M).presheaf) := inferInstance
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n M).presheaf) (X := op W)
    (show (pre n M).presheaf.obj (op W) from w) (show (pre n M).presheaf.obj (op W) from w') h
  obtain ⟨V, f, hf, hxV⟩ := hmem x hx
  refine ⟨V, f.le, hxV, ?_⟩
  rw [show homOfLE f.le = f from Subsingleton.elim _ _]
  exact hf

lemma toSh_locally_surjective (M : X.Modules) {W : X.Opens} (c : Γ(det n M, W)) (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ ∃ w : ⋀[Γ(X, V)]^n Γ(M, V), toSh n M V w = res (det n M) i c := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n M).presheaf) :=
    (inferInstance : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre n M).presheaf))
  obtain ⟨V, i, ⟨w, hw⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hls W c x hx
  exact ⟨V, i, hxV, show ⋀[Γ(X, V)]^n Γ(M, V) from w, hw⟩

section Wedge

variable {n} {M : X.Modules} {U : X.Opens} (e : Fin n → Γ(M, U))

noncomputable abbrev eRes {W : X.Opens} (hW : W ≤ U) : Fin n → Γ(M, W) := fun i => res M hW (e i)

noncomputable def wedge {W : X.Opens} (hW : W ≤ U) : Γ(det n M, W) :=
  toSh n M W (exteriorPower.ιMulti _ n (eRes e hW))

lemma res_toSh_ιMulti {W : X.Opens} (hW : W ≤ U) :
    res (det n M) hW (toSh n M U (exteriorPower.ιMulti _ n e)) = wedge e hW := by
  rw [wedge, res_toSh, preMap_ιMulti]

lemma res_wedge {W W' : X.Opens} (hW : W ≤ U) (h : W' ≤ W) :
    res (det n M) h (wedge e hW) = wedge e (h.trans hW) := by
  rw [wedge, wedge, res_toSh, preMap_ιMulti]
  congr 2
  funext i
  exact res_res M hW h (e i)

variable (he : ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
  ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i))

include he in

lemma exists_basis_eq {W : X.Opens} (hW : W ≤ U) :
    ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), (b : Fin n → Γ(M, W)) = eRes e hW := by
  obtain ⟨b, hb⟩ := he W hW
  exact ⟨b, funext hb⟩

include he in

lemma smul_wedge_injective {W : X.Opens} (hW : W ≤ U) :
    Function.Injective fun g : Γ(X, W) => g • wedge e hW := by
  intro g g' hgg'
  rw [← sub_eq_zero]
  have h0 : (g - g') • wedge e hW = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr hgg'
  have h1 : toSh n M W ((g - g') • exteriorPower.ιMulti _ n (eRes e hW)) = toSh n M W 0 := by
    rw [toSh_smul, toSh_zero]; exact h0
  have key : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ X.presheaf.map (homOfLE i).op (g - g') = 0 := by
    intro x hx
    obtain ⟨V, i, hxV, hV⟩ := toSh_locally_injective n M _ _ h1 x hx
    refine ⟨V, i, hxV, ?_⟩
    rw [preMap_zero, preMap_smul, preMap_ιMulti] at hV
    obtain ⟨b, hb⟩ := exists_basis_eq e he (i.trans hW)
    have hfam : (fun k => (M.presheaf.map (homOfLE i).op : Γ(M, W) ⟶ _) (eRes e hW k)) = (b : Fin n → Γ(M, V)) := by
      rw [hb]; funext k; exact res_res M hW i (e k)
    rw [hfam] at hV
    exact smul_ιMulti_injective b (hV.trans (zero_smul _ _).symm)
  choose V hV using key
  refine X.sheaf.eq_of_locally_eq' (fun p : {x // x ∈ W} => V p.1 p.2) W
    (fun p => homOfLE (hV p.1 p.2).1) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, (hV x hx).2.1⟩) (g - g') 0
    (fun p => ?_)
  rw [map_zero]
  exact (hV p.1 p.2).2.2

include he in

lemma smul_wedge_surjective {W : X.Opens} (hW : W ≤ U) :
    Function.Surjective fun g : Γ(X, W) => g • wedge e hW := by
  intro c
  have key : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ ∃ r : Γ(X, V),
      res (det n M) i c = r • wedge e (i.trans hW) := by
    intro x hx
    obtain ⟨V, i, hxV, w, hw⟩ := toSh_locally_surjective n M c x hx
    obtain ⟨b, hb⟩ := exists_basis_eq e he (i.trans hW)
    obtain ⟨r, hr⟩ := exists_eq_smul_ιMulti b w
    refine ⟨V, i, hxV, r, ?_⟩
    rw [← hw, hr, toSh_smul, hb]
    rfl
  choose V i hxV r hr using key
  let ι := {x // x ∈ W}
  let Vf : ι → X.Opens := fun p => V p.1 p.2
  have hcover : W ≤ iSup Vf := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩

  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 Vf (fun p => r p.1 p.2) := by
    intro p q
    rw [Subsingleton.elim (Opens.infLELeft (Vf p) (Vf q)) (homOfLE inf_le_left),
      Subsingleton.elim (Opens.infLERight (Vf p) (Vf q)) (homOfLE inf_le_right)]
    have hpq_p : Vf p ⊓ Vf q ≤ Vf p := inf_le_left
    have hpq_q : Vf p ⊓ Vf q ≤ Vf q := inf_le_right
    have hp : (X.presheaf.map (homOfLE hpq_p).op (r p.1 p.2) : Γ(X, Vf p ⊓ Vf q)) •
        wedge e (hpq_p.trans ((i p.1 p.2).trans hW)) = res (det n M) (hpq_p.trans (i p.1 p.2)) c := by
      rw [← res_wedge e ((i p.1 p.2).trans hW) hpq_p, ← res_smul, ← hr p.1 p.2, res_res]
    have hq : (X.presheaf.map (homOfLE hpq_q).op (r q.1 q.2) : Γ(X, Vf p ⊓ Vf q)) •
        wedge e (hpq_q.trans ((i q.1 q.2).trans hW)) = res (det n M) (hpq_q.trans (i q.1 q.2)) c := by
      rw [← res_wedge e ((i q.1 q.2).trans hW) hpq_q, ← res_smul, ← hr q.1 q.2, res_res]
    apply smul_wedge_injective e he (hpq_p.trans ((i p.1 p.2).trans hW))
    exact hp.trans hq.symm
  obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' Vf W (fun p => homOfLE (i p.1 p.2)) hcover
    (fun p => r p.1 p.2) hcompat
  refine ⟨show Γ(X, W) from g, ?_⟩

  let D : TopCat.Sheaf Ab X.toTopCat := ⟨(det n M).presheaf, (det n M).isSheaf⟩
  refine D.eq_of_locally_eq' Vf W (fun p => homOfLE (i p.1 p.2)) hcover _ c (fun p => ?_)
  change res (det n M) (i p.1 p.2) ((show Γ(X, W) from g) • wedge e hW) = res (det n M) (i p.1 p.2) c
  rw [res_smul, res_wedge, hr p.1 p.2]
  congr 1
  exact hg p

include he in

theorem isFrameOn_toSh_ιMulti :
    IsFrameOn (M := det n M) (toSh n M U (exteriorPower.ιMulti _ n e)) U := by
  intro W hWU _
  have hres : (det n M).presheaf.map (homOfLE hWU).op (toSh n M U (exteriorPower.ιMulti _ n e)) =
      wedge e hWU := res_toSh_ιMulti e hWU
  simp only [hres]
  exact ⟨smul_wedge_injective e he hWU, smul_wedge_surjective e he hWU⟩

end Wedge

end AlgebraicGeometry.Scheme.Modules.Ws31H1

namespace N2Adapter

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry.Scheme.Modules.Ws31H1"

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ)

noncomputable abbrev OX : Y.Modules := (pushforward π).obj (𝟙_ X.Modules)

def BasisClause (W : Y.Opens) (e : Fin d → Γ(OX π, W)) : Prop :=
  ∀ (W' : Y.Opens) (h : W' ≤ W), ∃ b : Module.Basis (Fin d) Γ(Y, W') Γ(OX π, W'),
    ∀ i, b i = (OX π).presheaf.map (homOfLE h).op (e i)

def good (W : Y.Opens) : Prop := ∃ e : Fin d → Γ(OX π, W), BasisClause π d W e

theorem basisClause_res {W W' : Y.Opens} {e : Fin d → Γ(OX π, W)} (he : BasisClause π d W e) (h : W' ≤ W) :
    BasisClause π d W' (fun i => (OX π).presheaf.map (homOfLE h).op (e i)) := by
  intro W'' h''
  obtain ⟨b, hb⟩ := he W'' (h''.trans h)
  refine ⟨b, fun i => ?_⟩
  rw [hb i]
  exact (res_res (OX π) h h'' (e i)).symm

theorem good_of_le {W W' : Y.Opens} (hW : good π d W) (h : W' ≤ W) : good π d W' := by
  obtain ⟨e, he⟩ := hW
  exact ⟨_, basisClause_res π d he h⟩

theorem exists_good [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] (hd : ∀ y : Y, π.finrank y = d) (y : Y) :
    ∃ W : Y.Opens, y ∈ W ∧ good π d W := by
  have hN : ∀ t : Y, ∃ W : Y.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj (𝟙_ X.Modules) ≅ 𝟙_ (↑(π ⁻¹ᵁ W) : Scheme.{u}).Modules) :=
    fun t => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩
  have hE : IsLocallyFreeOfRank d (OX π) :=
    isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd _ hN
  obtain ⟨W, hy, e, he⟩ := hE.exists_basis y
  exact ⟨W, hy, e, he⟩

theorem res_toSh_ιMulti' (M : Y.Modules) {W W' : Y.Opens} (h : W' ≤ W) (m : Fin d → Γ(M, W)) :
    res (det d M) h (toSh d M W (exteriorPower.ιMulti _ d m)) =
      toSh d M W' (exteriorPower.ιMulti _ d (fun k => res M h (m k))) := by
  rw [res_toSh, preMap_ιMulti]

end N2Adapter

theorem N2Adapter.toSh_iotaMulti_smul_eq_det_toMatrix_smul
    {X Y : Scheme.{u}} (π : X ⟶ Y) {L : X.Modules} {V : Y.Opens} {d : ℕ}
    (e e' : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (b : Module.Basis (Fin d) Γ(Y, V) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (hb : ∀ i, b i = e i) (s : Γ(L, π ⁻¹ᵁ V)) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val).obj (op V) from
        exteriorPower.ιMulti Γ(Y, V) d
          (fun j => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e' j) • s))) :
      Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj L), V)) =
    (b.toMatrix e').det •
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val).obj (op V) from
        exteriorPower.ιMulti Γ(Y, V) d
          (fun i => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i) • s))) :
      Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj L), V)) := by

  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V) →ₗ[Γ(Y, V)]
      Γ((Scheme.Modules.pushforward π).obj L, V),
      ∀ x, Φ x = (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from x) • s) :=
    ⟨{ toFun := fun x =>
         (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from x) • s),
       map_add' := fun x y => add_smul (show Γ(X, π ⁻¹ᵁ V) from x) (show Γ(X, π ⁻¹ᵁ V) from y) s,
       map_smul' := fun r x => by
         change ((π.app V).hom r * (show Γ(X, π ⁻¹ᵁ V) from x)) • s =
           (π.app V).hom r • ((show Γ(X, π ⁻¹ᵁ V) from x) • s)
         exact mul_smul _ _ _ }, fun x => rfl⟩
  refine AlgebraicGeometry.Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
    _ _ (b.toMatrix e') (fun j => ?_)

  have hA : ∑ i, (b.toMatrix e') i j •
      (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i) • s) =
      Φ (∑ i, (b.repr (e' j)) i • b i) := by
    rw [_root_.map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.map_smul, hb i, hΦ, Module.Basis.toMatrix_apply]
  rw [hA, b.sum_repr (e' j), hΦ]

theorem N2Adapter.toSh_iotaMulti_eq_det_toMatrix_smul
    {X Y : Scheme.{u}} (π : X ⟶ Y) {V : Y.Opens} {d : ℕ}
    (e e' : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (b : Module.Basis (Fin d) Γ(Y, V) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (hb : ∀ i, b i = e i) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).val).obj (op V)
        from exteriorPower.ιMulti Γ(Y, V) d e') :
      Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)), V)) =
    (b.toMatrix e').det •
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)).val).obj (op V)
        from exteriorPower.ιMulti Γ(Y, V) d e) :
      Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)), V)) := by
  refine AlgebraicGeometry.Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
    _ _ (b.toMatrix e') (fun j => ?_)
  calc e' j = ∑ i, (b.repr (e' j)) i • b i := (b.sum_repr (e' j)).symm
    _ = ∑ i, (b.toMatrix e') i j • e i :=
        Finset.sum_congr rfl (fun i _ => by rw [Module.Basis.toMatrix_apply, hb i])

namespace N2Adapter

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry.Scheme.Modules.Ws31H1"

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ)

theorem res_self (M : Y.Modules) {W : Y.Opens} (x : Γ(M, W)) : res M (le_refl W) x = x := by
  change M.presheaf.map (homOfLE (le_refl W)).op x = x
  rw [Subsingleton.elim (homOfLE (le_refl W)) (𝟙 W), op_id, M.presheaf.map_id]; rfl

noncomputable def Lu (W : Y.Opens) (u : Γ(X, π ⁻¹ᵁ W)) : Γ(OX π, W) →ₗ[Γ(Y, W)] Γ(OX π, W) where
  toFun x := (show Γ(OX π, W) from u * (show Γ(X, π ⁻¹ᵁ W) from x))
  map_add' x y := mul_add u _ _
  map_smul' r x := by
    change u * (_ * _) = _ * (u * _)
    exact mul_left_comm _ _ _

theorem Lu_apply (W : Y.Opens) (u : Γ(X, π ⁻¹ᵁ W)) (x : Γ(OX π, W)) :
    (show Γ(X, π ⁻¹ᵁ W) from Lu π W u x) = u * (show Γ(X, π ⁻¹ᵁ W) from x) := rfl

theorem Lu_one (W : Y.Opens) : Lu π W 1 = LinearMap.id := by
  ext x; change (1 : Γ(X, π ⁻¹ᵁ W)) * _ = _; rw [one_mul]; rfl

theorem Lu_mul (W : Y.Opens) (u v : Γ(X, π ⁻¹ᵁ W)) : Lu π W (u * v) = Lu π W u ∘ₗ Lu π W v := by
  ext x; change (u * v) * _ = u * (v * _); rw [mul_assoc]

noncomputable def Nm (W : Y.Opens) : Γ(X, π ⁻¹ᵁ W) →* Γ(Y, W) where
  toFun u := LinearMap.det (Lu π W u)
  map_one' := by rw [Lu_one, LinearMap.det_id]
  map_mul' u v := by rw [Lu_mul, LinearMap.det_comp]

variable {π d}

noncomputable def eOf {W : Y.Opens} (hW : good π d W) : Fin d → Γ(OX π, W) := hW.choose
theorem eOf_spec {W : Y.Opens} (hW : good π d W) : BasisClause π d W (eOf hW) := hW.choose_spec

noncomputable def pO {W : Y.Opens} (hW : good π d W) : Γ(det d (OX π), W) :=
  toSh d (OX π) W (exteriorPower.ιMulti _ d (eOf hW))

theorem isFrameOn_pO {W : Y.Opens} (hW : good π d W) : IsFrameOn (pO hW) W :=
  isFrameOn_sheafificationAdjunction_unit_iotaMulti (eOf hW) (eOf_spec hW)

noncomputable def qO {W : Y.Opens} (hW : good π d W) : Γ(dual (det d (OX π)), W) :=
  (IsFrameOn.exists_isFrameOn_dual (isFrameOn_pO hW) (le_refl W)).choose

theorem isFrameOn_qO {W : Y.Opens} (hW : good π d W) : IsFrameOn (qO hW) W :=
  (IsFrameOn.exists_isFrameOn_dual (isFrameOn_pO hW) (le_refl W)).choose_spec.1

theorem qO_pair {W : Y.Opens} (hW : good π d W) :
    ihomEval (det d (OX π)) (𝟙_ Y.Modules) W (pO hW) (qO hW) = unitSection W := by
  have := (IsFrameOn.exists_isFrameOn_dual (isFrameOn_pO hW) (le_refl W)).choose_spec.2
  convert this using 3
  all_goals first | rfl | exact (res_self _ _).symm

noncomputable abbrev fam (M : X.Modules) {W : Y.Opens} (hW : good π d W) (s : Γ(M, π ⁻¹ᵁ W)) :
    Fin d → Γ((pushforward π).obj M, W) :=
  fun i => (show Γ((pushforward π).obj M, W) from (show Γ(X, π ⁻¹ᵁ W) from eOf hW i) • s)

noncomputable def δ (M : X.Modules) {W : Y.Opens} (hW : good π d W) (s : Γ(M, π ⁻¹ᵁ W)) :
    Γ(normModule π d M, W) :=
  (show Γ(det d ((pushforward π).obj M) ⊗ dual (det d (OX π)), W) from
    tensorSections (toSh d ((pushforward π).obj M) W (exteriorPower.ιMulti _ d (fam M hW s))) (qO hW))

set_option maxHeartbeats 1600000 in
theorem isFrameOn_δ (M : X.Modules) {W : Y.Opens} (hW : good π d W) {s : Γ(M, π ⁻¹ᵁ W)}
    (hs : IsFrameOn s (π ⁻¹ᵁ W)) : IsFrameOn (δ M hW s) W := by
  obtain ⟨q', -, hq'pair, hδ'⟩ := IsFrameOn.exists_isFrameOn_normModule π d (eOf hW) (eOf_spec hW) hs
  have hq : q' = qO hW := dual_unique (isFrameOn_pO hW) hq'pair (qO_pair hW)
  subst hq
  exact hδ'

theorem A5core {L : X.Modules} {V : Y.Opens}
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (b : Module.Basis (Fin d) Γ(Y, V) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (hb : ∀ i, b i = e i)
    (s : Γ(L, π ⁻¹ᵁ V)) (u : Γ(X, π ⁻¹ᵁ V))
    (Lu' : Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V) →ₗ[Γ(Y, V)]
      Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V))
    (hLu : ∀ x : Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V),
      (show Γ(X, π ⁻¹ᵁ V) from Lu' x) = u * (show Γ(X, π ⁻¹ᵁ V) from x)) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val).obj (op V) from
        exteriorPower.ιMulti Γ(Y, V) d
          (fun i => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i) • (u • s)))) :
      Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj L), V)) =
    LinearMap.det Lu' •
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val)).app (op V)
      (show ((Scheme.Modules.presheafExteriorPower Y d).obj ((Scheme.Modules.pushforward π).obj L).val).obj (op V) from
        exteriorPower.ιMulti Γ(Y, V) d
          (fun i => (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i) • s))) :
      Γ(Scheme.Modules.det d ((Scheme.Modules.pushforward π).obj L), V)) := by

  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Γ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules), V) →ₗ[Γ(Y, V)]
      Γ((Scheme.Modules.pushforward π).obj L, V),
      ∀ x, Φ x = (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from x) • s) :=
    ⟨{ toFun := fun x =>
         (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from x) • s),
       map_add' := fun x y => add_smul (show Γ(X, π ⁻¹ᵁ V) from x) (show Γ(X, π ⁻¹ᵁ V) from y) s,
       map_smul' := fun r x => by
         change ((π.app V).hom r * (show Γ(X, π ⁻¹ᵁ V) from x)) • s =
           (π.app V).hom r • ((show Γ(X, π ⁻¹ᵁ V) from x) • s)
         exact mul_smul _ _ _ }, fun x => rfl⟩
  rw [← LinearMap.det_toMatrix b Lu']
  refine AlgebraicGeometry.Scheme.Modules.sheafificationAdjunction_unit_iotaMulti_eq_det_smul_of_eq_sum_smul
    _ _ (LinearMap.toMatrix b b Lu') (fun j => ?_)

  have hA : ∑ i, (LinearMap.toMatrix b b Lu') i j •
      (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e i) • s) =
      Φ (∑ i, (LinearMap.toMatrix b b Lu') i j • b i) := by
    rw [_root_.map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.map_smul, hb i, hΦ]
  have hB : ∑ i, (LinearMap.toMatrix b b Lu') i j • b i = Lu' (b j) := by
    simp_rw [LinearMap.toMatrix_apply]
    exact b.sum_repr (Lu' (b j))
  have hC : Φ (Lu' (b j)) =
      (show Γ((Scheme.Modules.pushforward π).obj L, V) from (show Γ(X, π ⁻¹ᵁ V) from e j) • (u • s)) := by
    rw [hΦ]
    change (show Γ(X, π ⁻¹ᵁ V) from Lu' (b j)) • s = (show Γ(X, π ⁻¹ᵁ V) from e j) • (u • s)
    calc (show Γ(X, π ⁻¹ᵁ V) from Lu' (b j)) • s
        = (u * (show Γ(X, π ⁻¹ᵁ V) from b j)) • s := congrArg (· • s) (hLu (b j))
      _ = (u * (show Γ(X, π ⁻¹ᵁ V) from e j)) • s := by rw [hb j]
      _ = (show Γ(X, π ⁻¹ᵁ V) from e j) • (u • s) := by rw [mul_comm, mul_smul]
  exact (hA.trans ((congrArg Φ hB).trans hC)).symm

set_option maxHeartbeats 1600000 in
theorem δ_smul (M : X.Modules) {W : Y.Opens} (hW : good π d W) (v : Γ(X, π ⁻¹ᵁ W)) (s : Γ(M, π ⁻¹ᵁ W)) :
    δ M hW (v • s) = Nm π W v • δ M hW s := by
  obtain ⟨b, hb⟩ := eOf_spec hW W (le_refl W)
  have hb' : ∀ i, b i = eOf hW i := fun i => (hb i).trans (res_self _ _)
  have key := A5core (L := M) (eOf hW) b hb' s v (Lu π W v) (fun x => rfl)
  change tensorSections (toSh d ((pushforward π).obj M) W (exteriorPower.ιMulti _ d (fam M hW (v • s)))) (qO hW) =
    Nm π W v • tensorSections (toSh d ((pushforward π).obj M) W (exteriorPower.ιMulti _ d (fam M hW s))) (qO hW)
  rw [← tensorSections_smul_left]
  congr 1

set_option maxHeartbeats 1600000 in

theorem map_δ (M : X.Modules) {W W' : Y.Opens} (hW : good π d W) (h : W' ≤ W) (s : Γ(M, π ⁻¹ᵁ W)) :
    (normModule π d M).presheaf.map (homOfLE h).op (δ M hW s) =
      δ M (good_of_le π d hW h) (M.presheaf.map (homOfLE (π.preimage_mono h)).op s) := by

  set hW' := good_of_le π d hW h
  set e := eOf hW
  set e' := eOf hW'
  set eW' : Fin d → Γ(OX π, W') := fun i => res (OX π) h (e i)
  set s' : Γ(M, π ⁻¹ᵁ W') := M.presheaf.map (homOfLE (π.preimage_mono h)).op s

  obtain ⟨b, hb⟩ := eOf_spec hW W' h

  have hnum : res (det d ((pushforward π).obj M)) h
      (toSh d ((pushforward π).obj M) W (exteriorPower.ιMulti _ d (fam M hW s))) =
      toSh d ((pushforward π).obj M) W' (exteriorPower.ιMulti _ d
        (fun i => (show Γ((pushforward π).obj M, W') from (show Γ(X, π ⁻¹ᵁ W') from eW' i) • s'))) := by
    rw [res_toSh_ιMulti']
    refine congrArg _ (congrArg _ (funext fun i => ?_))

    change M.presheaf.map (homOfLE (π.preimage_mono h)).op ((show Γ(X, π ⁻¹ᵁ W) from e i) • s) =
      X.presheaf.map (homOfLE (π.preimage_mono h)).op (show Γ(X, π ⁻¹ᵁ W) from e i) • s'
    exact M.map_smul (homOfLE (π.preimage_mono h)) _ _

  have hpO : res (det d (OX π)) h (pO hW) = toSh d (OX π) W' (exteriorPower.ιMulti _ d eW') :=
    res_toSh_ιMulti' d (OX π) h e
  have hq1 : ihomEval (det d (OX π)) (𝟙_ Y.Modules) W' (toSh d (OX π) W' (exteriorPower.ιMulti _ d eW'))
      (res (dual (det d (OX π))) h (qO hW)) = unitSection W' := by
    rw [← hpO]; exact ihomEval_map_dual (qO_pair hW) h

  have hb' : ∀ i, b i = eW' i := hb
  have hden : toSh d (OX π) W' (exteriorPower.ιMulti _ d e') =
      (b.toMatrix e').det • toSh d (OX π) W' (exteriorPower.ιMulti _ d eW') :=
    toSh_iotaMulti_eq_det_toMatrix_smul π eW' e' b hb'
  have hnum' : toSh d ((pushforward π).obj M) W' (exteriorPower.ιMulti _ d (fam M hW' s')) =
      (b.toMatrix e').det • toSh d ((pushforward π).obj M) W' (exteriorPower.ιMulti _ d
        (fun i => (show Γ((pushforward π).obj M, W') from (show Γ(X, π ⁻¹ᵁ W') from eW' i) • s'))) :=
    toSh_iotaMulti_smul_eq_det_toMatrix_smul π eW' e' b hb' s'

  have hq2 : (b.toMatrix e').det • qO hW' = res (dual (det d (OX π))) h (qO hW) := by
    apply smul_dual_eq (isFrameOn_sheafificationAdjunction_unit_iotaMulti eW' (basisClause_res π d (eOf_spec hW) h)) _ hq1
    convert qO_pair hW' using 3
    exact hden.symm

  change res (det d ((pushforward π).obj M) ⊗ dual (det d (OX π))) h
      (tensorSections (toSh d ((pushforward π).obj M) W (exteriorPower.ιMulti _ d (fam M hW s))) (qO hW)) =
    tensorSections (toSh d ((pushforward π).obj M) W' (exteriorPower.ιMulti _ d (fam M hW' s'))) (qO hW')
  rw [show res (det d ((pushforward π).obj M) ⊗ dual (det d (OX π))) h
      (tensorSections (toSh d ((pushforward π).obj M) W (exteriorPower.ιMulti _ d (fam M hW s))) (qO hW)) =
      tensorSections (res _ h (toSh d ((pushforward π).obj M) W (exteriorPower.ιMulti _ d (fam M hW s))))
        (res _ h (qO hW)) from map_homOfLE_tensorSections h _ _,
    hnum, ← hq2, tensorSections_smul_right, ← tensorSections_smul_left, ← hnum']

theorem nonempty_normFrameKit' [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hd : ∀ y : Y, π.finrank y = d) : Nonempty (N2Assembly.NormFrameKit π d) :=
  ⟨{ good := good π d
     good_of_le := fun _ _ hW h => good_of_le π d hW h
     exists_good := exists_good π d hd
     Nm := fun W _ => Nm π W
     nf := fun M W hW s => δ M hW s
     isFrameOn_nf := fun M W hW s hs => isFrameOn_δ M hW hs
     map_nf := fun M W W' hW h s => map_δ M hW h s
     nf_smul := fun M W hW v s _ _ => δ_smul M hW v s }⟩

end N2Adapter

namespace NormKit

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.N2Adapter"

variable {X Z Z₀ Z₁ : Scheme.{u}} (π : Z ⟶ X) (ι₀ : Z₀ ⟶ Z) (ι₁ : Z₁ ⟶ Z) (d d₀ d₁ : ℕ) (L : Z.Modules)

noncomputable abbrev res₀ {W : X.Opens} (s : Γ(L, π ⁻¹ᵁ W)) :
    Γ((Scheme.Modules.pullback ι₀).obj L, (ι₀ ≫ π) ⁻¹ᵁ W) :=
  (show Γ((Scheme.Modules.pullback ι₀).obj L, (ι₀ ≫ π) ⁻¹ᵁ W) from pullbackLocalSection ι₀ s)

noncomputable abbrev res₁ {W : X.Opens} (s : Γ(L, π ⁻¹ᵁ W)) :
    Γ((Scheme.Modules.pullback ι₁).obj L, (ι₁ ≫ π) ⁻¹ᵁ W) :=
  (show Γ((Scheme.Modules.pullback ι₁).obj L, (ι₁ ≫ π) ⁻¹ᵁ W) from pullbackLocalSection ι₁ s)

noncomputable def qSec {W : X.Opens} (hW₀ : good (ι₀ ≫ π) d₀ W) (hW₁ : good (ι₁ ≫ π) d₁ W) (s : Γ(L, π ⁻¹ᵁ W)) :
    Γ(normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
      normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L), W) :=
  tensorSections (δ ((Scheme.Modules.pullback ι₀).obj L) hW₀ (res₀ π ι₀ L s))
    (δ ((Scheme.Modules.pullback ι₁).obj L) hW₁ (res₁ π ι₁ L s))

def S (W : X.Opens) : Set (Γ(normModule π d L, W) ×
    Γ(normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
      normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L), W)) :=
  {pq | ∃ (hW : good π d W) (hW₀ : good (ι₀ ≫ π) d₀ W) (hW₁ : good (ι₁ ≫ π) d₁ W) (s : Γ(L, π ⁻¹ᵁ W)),
    IsFrameOn s (π ⁻¹ᵁ W) ∧ pq = (δ L hW s, qSec π ι₀ ι₁ d₀ d₁ L hW₀ hW₁ s)}

variable {π ι₀ ι₁ d d₀ d₁ L}

theorem frame (W : X.Opens) (pq : Γ(normModule π d L, W) × Γ(normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
      normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L), W)) (h : pq ∈ S π ι₀ ι₁ d d₀ d₁ L W) :
    IsFrameOn pq.1 W ∧ IsFrameOn pq.2 W := by
  obtain ⟨hW, hW₀, hW₁, s, hs, rfl⟩ := h
  exact ⟨isFrameOn_δ L hW hs,
    IsFrameOn.tensorSections (isFrameOn_δ _ hW₀ (hs.pullbackLocalSection ι₀))
      (isFrameOn_δ _ hW₁ (hs.pullbackLocalSection ι₁))⟩

theorem cov [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    [IsFinite (ι₀ ≫ π)] [Flat (ι₀ ≫ π)] [LocallyOfFinitePresentation (ι₀ ≫ π)]
    [IsFinite (ι₁ ≫ π)] [Flat (ι₁ ≫ π)] [LocallyOfFinitePresentation (ι₁ ≫ π)]
    (hd : ∀ x : X, π.finrank x = d) (hd₀ : ∀ x : X, (ι₀ ≫ π).finrank x = d₀)
    (hd₁ : ∀ x : X, (ι₁ ≫ π).finrank x = d₁) (hL : Scheme.Modules.IsInvertible L) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ (S π ι₀ ι₁ d d₀ d₁ L W).Nonempty := by
  obtain ⟨W₁, hx₁, hW₁⟩ := exists_good π d hd x
  obtain ⟨W₂, hx₂, hW₂⟩ := exists_good (ι₀ ≫ π) d₀ hd₀ x
  obtain ⟨W₃, hx₃, hW₃⟩ := exists_good (ι₁ ≫ π) d₁ hd₁ x
  obtain ⟨W₄, s, hx₄, hs⟩ := N2Assembly.exists_isFrameOn_preimage π hL x
  let W : X.Opens := W₁ ⊓ W₂ ⊓ W₃ ⊓ W₄
  have h₁ : W ≤ W₁ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have h₂ : W ≤ W₂ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have h₃ : W ≤ W₃ := inf_le_left.trans inf_le_right
  have h₄ : W ≤ W₄ := inf_le_right
  refine ⟨W, ⟨⟨⟨hx₁, hx₂⟩, hx₃⟩, hx₄⟩, ⟨_, good_of_le π d hW₁ h₁, good_of_le _ d₀ hW₂ h₂, good_of_le _ d₁ hW₃ h₃,
    L.presheaf.map (homOfLE (π.preimage_mono h₄)).op s, ?_, rfl⟩⟩
  exact (hs.map (homOfLE (π.preimage_mono h₄))).mono (π.preimage_mono h₄)

theorem res (W W' : X.Opens) (h : W' ≤ W)
    (pq : Γ(normModule π d L, W) × Γ(normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
      normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L), W)) (hpq : pq ∈ S π ι₀ ι₁ d d₀ d₁ L W) :
    ((normModule π d L).presheaf.map (homOfLE h).op pq.1,
      (normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
        normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L)).presheaf.map (homOfLE h).op pq.2) ∈
      S π ι₀ ι₁ d d₀ d₁ L W' := by
  obtain ⟨hW, hW₀, hW₁, s, hs, rfl⟩ := hpq
  refine ⟨good_of_le π d hW h, good_of_le _ d₀ hW₀ h, good_of_le _ d₁ hW₁ h,
    L.presheaf.map (homOfLE (π.preimage_mono h)).op s,
    (hs.map (homOfLE (π.preimage_mono h))).mono (π.preimage_mono h), ?_⟩
  refine Prod.ext (map_δ L hW h s) ?_
  change (normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
        normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L)).presheaf.map (homOfLE h).op
      (tensorSections _ _) = tensorSections _ _
  rw [map_homOfLE_tensorSections, map_δ _ hW₀ h, map_δ _ hW₁ h]
  congr 2
  · exact map_homOfLE_pullbackLocalSection ι₀ (π.preimage_mono h) s
  · exact map_homOfLE_pullbackLocalSection ι₁ (π.preimage_mono h) s

theorem cocycle [IsIntegral X] (hsum : d = d₀ + d₁)
    (hcov : ∀ (U : Z.Opens) (s : Γ(Z, U)), (ι₀.app U).hom s = 0 → (ι₁.app U).hom s = 0 → s = 0)
    {W : X.Opens} [Nonempty W] (hW : good π d W) (hW₀ : good (ι₀ ≫ π) d₀ W) (hW₁ : good (ι₁ ≫ π) d₁ W)
    (v : Γ(Z, π ⁻¹ᵁ W)) :
    Nm π W v = Nm (ι₀ ≫ π) W ((ι₀.app (π ⁻¹ᵁ W)).hom v) * Nm (ι₁ ≫ π) W ((ι₁.app (π ⁻¹ᵁ W)).hom v) := by
  classical

  letI alg : Algebra Γ(X, W) Γ(Z, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
  letI alg₀ : Algebra Γ(X, W) Γ(Z₀, (ι₀ ≫ π) ⁻¹ᵁ W) := ((ι₀ ≫ π).app W).hom.toAlgebra
  letI alg₁ : Algebra Γ(X, W) Γ(Z₁, (ι₁ ≫ π) ⁻¹ᵁ W) := ((ι₁ ≫ π).app W).hom.toAlgebra

  obtain ⟨b, -⟩ := eOf_spec hW W le_rfl
  obtain ⟨b₀, -⟩ := eOf_spec hW₀ W le_rfl
  obtain ⟨b₁, -⟩ := eOf_spec hW₁ W le_rfl
  let bY : Module.Basis (Fin d) Γ(X, W) Γ(Z, π ⁻¹ᵁ W) := b
  let bY₀ : Module.Basis (Fin d₀) Γ(X, W) Γ(Z₀, (ι₀ ≫ π) ⁻¹ᵁ W) := b₀
  let bY₁ : Module.Basis (Fin d₁) Γ(X, W) Γ(Z₁, (ι₁ ≫ π) ⁻¹ᵁ W) := b₁
  haveI : Module.Free Γ(X, W) Γ(Z, π ⁻¹ᵁ W) := Module.Free.of_basis bY
  haveI : Module.Finite Γ(X, W) Γ(Z, π ⁻¹ᵁ W) := Module.Finite.of_basis bY
  haveI : Module.Free Γ(X, W) Γ(Z₀, (ι₀ ≫ π) ⁻¹ᵁ W) := Module.Free.of_basis bY₀
  haveI : Module.Finite Γ(X, W) Γ(Z₀, (ι₀ ≫ π) ⁻¹ᵁ W) := Module.Finite.of_basis bY₀
  haveI : Module.Free Γ(X, W) Γ(Z₁, (ι₁ ≫ π) ⁻¹ᵁ W) := Module.Free.of_basis bY₁
  haveI : Module.Finite Γ(X, W) Γ(Z₁, (ι₁ ≫ π) ⁻¹ᵁ W) := Module.Finite.of_basis bY₁

  have brP : Nm π W v = Algebra.norm Γ(X, W) v := by
    rw [Algebra.norm_eq_matrix_det bY]
    change LinearMap.det (Lu π W v) = _
    rw [← LinearMap.det_toMatrix b]
    congr 1
  have br₀ : Nm (ι₀ ≫ π) W ((ι₀.app (π ⁻¹ᵁ W)).hom v) =
      Algebra.norm Γ(X, W) (show Γ(Z₀, (ι₀ ≫ π) ⁻¹ᵁ W) from (ι₀.app (π ⁻¹ᵁ W)).hom v) := by
    rw [Algebra.norm_eq_matrix_det bY₀]
    change LinearMap.det (Lu (ι₀ ≫ π) W _) = _
    rw [← LinearMap.det_toMatrix b₀]
    congr 1
  have br₁ : Nm (ι₁ ≫ π) W ((ι₁.app (π ⁻¹ᵁ W)).hom v) =
      Algebra.norm Γ(X, W) (show Γ(Z₁, (ι₁ ≫ π) ⁻¹ᵁ W) from (ι₁.app (π ⁻¹ᵁ W)).hom v) := by
    rw [Algebra.norm_eq_matrix_det bY₁]
    change LinearMap.det (Lu (ι₁ ≫ π) W _) = _
    rw [← LinearMap.det_toMatrix b₁]
    congr 1

  let φ : Γ(Z, π ⁻¹ᵁ W) →ₐ[Γ(X, W)] Γ(Z₀, (ι₀ ≫ π) ⁻¹ᵁ W) × Γ(Z₁, (ι₁ ≫ π) ⁻¹ᵁ W) :=
    { toRingHom := RingHom.prod
        (show Γ(Z, π ⁻¹ᵁ W) →+* Γ(Z₀, (ι₀ ≫ π) ⁻¹ᵁ W) from (ι₀.app (π ⁻¹ᵁ W)).hom)
        (show Γ(Z, π ⁻¹ᵁ W) →+* Γ(Z₁, (ι₁ ≫ π) ⁻¹ᵁ W) from (ι₁.app (π ⁻¹ᵁ W)).hom)
      commutes' := fun r => rfl }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    exact hcov (π ⁻¹ᵁ W) b (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have hrank : Module.finrank Γ(X, W) Γ(Z, π ⁻¹ᵁ W) =
      Module.finrank Γ(X, W) Γ(Z₀, (ι₀ ≫ π) ⁻¹ᵁ W) + Module.finrank Γ(X, W) Γ(Z₁, (ι₁ ≫ π) ⁻¹ᵁ W) := by
    rw [Module.finrank_eq_card_basis bY, Module.finrank_eq_card_basis bY₀, Module.finrank_eq_card_basis bY₁]
    simpa only [Fintype.card_fin] using hsum
  haveI : IsDomain Γ(X, W) := inferInstance
  have key := Algebra.norm_eq_norm_fst_mul_norm_snd_of_injective φ hφ hrank v
  rw [brP, br₀, br₁]
  exact key

private theorem _root_.NormKit.unit [IsIntegral X] (hsum : d = d₀ + d₁)
    (hcov : ∀ (U : Z.Opens) (s : Γ(Z, U)), (ι₀.app U).hom s = 0 → (ι₁.app U).hom s = 0 → s = 0)
    (W : X.Opens)
    (pq pq' : Γ(normModule π d L, W) × Γ(normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
      normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L), W))
    (hpq : pq ∈ S π ι₀ ι₁ d d₀ d₁ L W) (hpq' : pq' ∈ S π ι₀ ι₁ d d₀ d₁ L W) :
    ∃ u : Γ(X, W), pq'.1 = u • pq.1 ∧ pq'.2 = u • pq.2 := by
  obtain ⟨hW, hW₀, hW₁, s, hs, rfl⟩ := hpq
  obtain ⟨hW', hW₀', hW₁', s', hs', rfl⟩ := hpq'
  obtain ⟨v, -, hvs⟩ := N2Assembly.Frame.exists_isUnit_smul_eq' hs hs'
  subst hvs

  have hP : δ L hW' (v • s) = Nm π W v • δ L hW s := δ_smul L hW v s

  have hQ : qSec π ι₀ ι₁ d₀ d₁ L hW₀' hW₁' (v • s) =
      (Nm (ι₀ ≫ π) W ((ι₀.app (π ⁻¹ᵁ W)).hom v) * Nm (ι₁ ≫ π) W ((ι₁.app (π ⁻¹ᵁ W)).hom v)) •
        qSec π ι₀ ι₁ d₀ d₁ L hW₀ hW₁ s := by
    have h₀ : res₀ π ι₀ L (v • s) = (show Γ(Z₀, (ι₀ ≫ π) ⁻¹ᵁ W) from (ι₀.app (π ⁻¹ᵁ W)).hom v) • res₀ π ι₀ L s :=
      pullbackLocalSection_smul ι₀ v s
    have h₁ : res₁ π ι₁ L (v • s) = (show Γ(Z₁, (ι₁ ≫ π) ⁻¹ᵁ W) from (ι₁.app (π ⁻¹ᵁ W)).hom v) • res₁ π ι₁ L s :=
      pullbackLocalSection_smul ι₁ v s
    unfold qSec
    rw [h₀, h₁, δ_smul, δ_smul, tensorSections_smul_left, tensorSections_smul_right, smul_smul, mul_comm]
  by_cases hne : Nonempty W
  · refine ⟨Nm π W v, hP, ?_⟩
    rw [hQ, ← cocycle hsum hcov hW hW₀ hW₁ v]
  ·
    have hWb : W = ⊥ := by
      rw [← TopologicalSpace.Opens.coe_eq_empty]
      exact Set.isEmpty_coe_sort.mp (not_nonempty_iff.mp hne)
    subst hWb
    haveI : Subsingleton Γ(X, (⊥ : X.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty X.sheaf)
    refine ⟨Nm π ⊥ v, hP, ?_⟩
    rw [hQ, Subsingleton.elim (_ * _) (Nm π ⊥ v)]

p2m_export "NormKit" "unit"
end NormKit

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.AlgebraicGeometry in
theorem solution
    {X Z Z₀ Z₁ : Scheme.{u}} [IsIntegral X] (π : Z ⟶ X) (ι₀ : Z₀ ⟶ Z) (ι₁ : Z₁ ⟶ Z)
    [IsClosedImmersion ι₀] [IsClosedImmersion ι₁]
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    [IsFinite (ι₀ ≫ π)] [Flat (ι₀ ≫ π)] [LocallyOfFinitePresentation (ι₀ ≫ π)]
    [IsFinite (ι₁ ≫ π)] [Flat (ι₁ ≫ π)] [LocallyOfFinitePresentation (ι₁ ≫ π)]
    (d d₀ d₁ : ℕ) (hd : ∀ x : X, π.finrank x = d) (hd₀ : ∀ x : X, (ι₀ ≫ π).finrank x = d₀)
    (hd₁ : ∀ x : X, (ι₁ ≫ π).finrank x = d₁) (hsum : d = d₀ + d₁)
    (hcov : ∀ (U : Z.Opens) (s : Γ(Z, U)), (ι₀.app U).hom s = 0 → (ι₁.app U).hom s = 0 → s = 0)
    {L : Z.Modules} (hL : Scheme.Modules.IsInvertible L) :
    letI P : X.Modules := Scheme.Modules.normModule π d L
    letI Q : X.Modules := Scheme.Modules.normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
        Scheme.Modules.normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L)
    ∃ S : ∀ W : X.Opens, Set (Γ(P, W) × Γ(Q, W)),
      (∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
        Scheme.Modules.IsFrameOn pq.1 W ∧ Scheme.Modules.IsFrameOn pq.2 W) ∧
      (∀ x : X, ∃ W : X.Opens, x ∈ W ∧ (S W).Nonempty) ∧
      (∀ (W W' : X.Opens) (h : W' ≤ W) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
        (P.presheaf.map (homOfLE h).op pq.1, Q.presheaf.map (homOfLE h).op pq.2) ∈ S W') ∧
      (∀ (W : X.Opens) (pq pq' : Γ(P, W) × Γ(Q, W)), pq ∈ S W → pq' ∈ S W →
        ∃ u : Γ(X, W), pq'.1 = u • pq.1 ∧ pq'.2 = u • pq.2) := by
  refine ⟨NormKit.S π ι₀ ι₁ d d₀ d₁ L, NormKit.frame, NormKit.cov hd hd₀ hd₁ hL, NormKit.res, NormKit.unit hsum hcov⟩

end S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion (solution)
