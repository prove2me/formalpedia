-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2f760527-b05e-52b7-8162-884bb9a93d27

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_existsUnique_isBaseScalar_of_isInvertible_of_bijective
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_one_of_isBaseScalar
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_trans
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_comp_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_pullback_mapIso_one
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_symm_of_mul_eq_one
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_translate_comp_schemeNsmul_of_mem_torsionSubset
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_translate_mul
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback

import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_map_pullback_of_comm_sq
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard AlgebraicGeometry.DescentCharacter"

namespace PhiCore

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R))

theorem isBaseScalar_id (M : X.Modules) : IsBaseScalar p (𝟙 M) (1 : R) := by
  intro U s
  rw [Scheme.Modules.Hom.id_app, baseSection_one, one_smul]
  rfl

theorem isBaseScalar_comp {M : X.Modules} {σ τ : M ⟶ M} {c c' : R}
    (hσ : IsBaseScalar p σ c) (hτ : IsBaseScalar p τ c') : IsBaseScalar p (σ ≫ τ) (c * c') := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app]
  show τ.app U (σ.app U s) = _
  rw [hσ U s, Scheme.Modules.Hom.app_smul, hτ U, smul_smul, baseSection_mul, mul_comm]

variable (hH0 : Function.Bijective fun c : R => p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))

include hH0

noncomputable def scalarOf {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (σ : M ⟶ M) : R :=
  (existsUnique_isBaseScalar_of_isInvertible_of_bijective p hH0 hM σ).choose

theorem isBaseScalar_scalarOf {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (σ : M ⟶ M) :
    IsBaseScalar p σ (scalarOf p hH0 hM σ) :=
  (existsUnique_isBaseScalar_of_isInvertible_of_bijective p hH0 hM σ).choose_spec.1

theorem scalarOf_unique {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) {σ : M ⟶ M} {c : R}
    (hc : IsBaseScalar p σ c) : c = scalarOf p hH0 hM σ :=
  (existsUnique_isBaseScalar_of_isInvertible_of_bijective p hH0 hM σ).unique hc (isBaseScalar_scalarOf p hH0 hM σ)

theorem eq_of_isBaseScalar {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) {σ : M ⟶ M} {c c' : R}
    (hc : IsBaseScalar p σ c) (hc' : IsBaseScalar p σ c') : c = c' :=
  (scalarOf_unique p hH0 hM hc).trans (scalarOf_unique p hH0 hM hc').symm

theorem isUnit_of_isBaseScalar_iso {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (γ : M ≅ M) {c : R}
    (hc : IsBaseScalar p γ.hom c) : IsUnit c := by
  have h1 : IsBaseScalar p (γ.hom ≫ γ.inv) (c * scalarOf p hH0 hM γ.inv) :=
    isBaseScalar_comp p hc (isBaseScalar_scalarOf p hH0 hM γ.inv)
  rw [Iso.hom_inv_id] at h1
  have h2 := eq_of_isBaseScalar p hH0 hM h1 (isBaseScalar_id p M)
  exact IsUnit.of_mul_eq_one _ h2

variable {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)

noncomputable def valueOf (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) : R :=
  scalarOf p hH0 (hM.pullback q) (discrepancy h β).hom

theorem hasValue_valueOf (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    HasValue p h β (valueOf p hH0 h hM β) :=
  isBaseScalar_scalarOf p hH0 _ _

theorem valueOf_unique {β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M} {c : R}
    (hc : HasValue p h β c) : c = valueOf p hH0 h hM β :=
  scalarOf_unique p hH0 _ hc

theorem isUnit_valueOf (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    IsUnit (valueOf p hH0 h hM β) :=
  isUnit_of_isBaseScalar_iso p hH0 (hM.pullback q) (discrepancy h β) (hasValue_valueOf p hH0 h hM β)

omit hH0 in
theorem hasValue_of_eq' {T₁ T₂ : X ⟶ X} (e : T₁ = T₂) {q' : X ⟶ Y} (h₁ : T₁ ≫ q' = q') (h₂ : T₂ ≫ q' = q')
    {N' M' : Y.Modules} (β : (Scheme.Modules.pullback q').obj N' ≅ (Scheme.Modules.pullback q').obj M') (c : R)
    (hβ : HasValue p h₁ β c) : HasValue p h₂ β c := by
  subst e; exact hβ

theorem valueOf_eq_valueOf (hT : T ≫ p = p) (hN : Scheme.Modules.IsInvertible N)
    (β β' : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    valueOf p hH0 h hM β = valueOf p hH0 h hM β' := by

  obtain ⟨γ, hγdef⟩ : ∃ γ : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj N,
      γ = β' ≪≫ β.symm := ⟨_, rfl⟩
  have hsc : IsBaseScalar p γ.hom (scalarOf p hH0 (hN.pullback q) γ.hom) :=
    isBaseScalar_scalarOf p hH0 (hN.pullback q) γ.hom
  have hγ : HasValue p h γ 1 := hasValue_one_of_isBaseScalar p h hT γ _ hsc
  have hβ' : γ ≪≫ β = β' := by
    rw [hγdef, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  have h2 : HasValue p h (γ ≪≫ β) (1 * valueOf p hH0 h hM β) :=
    hasValue_trans p h γ β 1 _ hγ (hasValue_valueOf p hH0 h hM β)
  rw [one_mul, hβ'] at h2
  exact valueOf_unique p hH0 h hM h2

end PhiCore

namespace PhiSetup

p2m_open "P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial.PhiCore GoodReductionJacobian.RelativeGroupLaw"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f)

theorem hH0_of (hA : AbelianSchemePropertyBundle S f) {T : Type} [CommRing T]
    (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) :
    Function.Bijective fun c : T => (pullback.snd f σ).appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv c) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective σ
  letI : Algebra S T := φ.hom.toAlgebra
  have h := hA.bijective_algebraMap_sections_pullback T
  have e : Scheme.TwoAffineOpenCover.specMap S T = Spec.map φ := rfl
  have key : ∀ c : T, (pullback.snd f (Spec.map φ)).appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of T)).inv c) =
      (pullback.snd f (Spec.map φ)).appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv c) := by
    intro c
    simp [Scheme.Hom.appLE]
  have hfun : (fun c : T => (pullback.snd f (Spec.map φ)).appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv c)) =
      fun c => (Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤).algebraMap c := by
    funext c
    rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, ← key]
    rfl
  rw [hfun]
  exact h

variable {R : Type} [CommRing R] {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}

noncomputable def xpt {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver σ f) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) (baseChangeStr σ f) :=
  baseChangePointOfBase σ (t' := 𝟙 (Spec (CommRingCat.of T))) ⟨x.1, by rw [Category.id_comp]; exact x.2⟩

theorem xpt_fst {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver σ f) :
    (xpt σ x).1 ≫ pullback.fst f σ = x.1 := pullback.lift_fst _ _ _

noncomputable def Tx {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver σ f) :
    pullback f σ ⟶ pullback f σ :=
  (L.baseChange σ).translate (xpt σ x)

theorem Tx_over {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver σ f) :
    Tx L σ x ≫ pullback.snd f σ = pullback.snd f σ :=
  (L.baseChange σ).translate_over _

theorem nsmul_val_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (e : t₁ = t₂) (n : ℕ)
    (y₁ : SchemeHomOver t₁ f) (y₂ : SchemeHomOver t₂ f) (hy : y₁.1 = y₂.1) :
    (L.nsmul t₁ n y₁).1 = (L.nsmul t₂ n y₂).1 := by
  subst e; rw [Subtype.ext hy]

theorem mul_val_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (e : t₁ = t₂)
    (y₁ z₁ : SchemeHomOver t₁ f) (y₂ z₂ : SchemeHomOver t₂ f) (hy : y₁.1 = y₂.1) (hz : z₁.1 = z₂.1) :
    (L.mul t₁ y₁ z₁).1 = (L.mul t₂ y₂ z₂).1 := by
  subst e; rw [Subtype.ext hy, Subtype.ext hz]

theorem one_val_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (e : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst e; rfl

theorem baseChange_nsmul {T' : Type} [CommRing T'] (σ : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S))
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of T')) (n : ℕ) (y : SchemeHomOver t' (baseChangeStr σ f)) :
    (L.baseChange σ).nsmul t' n y = baseChangePointOfBase σ (L.nsmul (t' ≫ σ) n (baseChangePointToBase σ y)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, nsmul_succ, ih, baseChange_mul, baseChangePointToBase_ofBase]

theorem xpt_mem_torsionSubset {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    (x : SchemeHomOver σ f) (hx : L.IsTorsionPoint σ n x) :
    xpt σ x ∈ (L.baseChange σ).torsionSubset (𝟙 (Spec (CommRingCat.of T))) n := by
  rw [mem_torsionSubset, isTorsionPoint_def, xpt, baseChange_nsmul, baseChange_one, baseChangePointToBase_ofBase]

  congr 1

theorem Tx_q (hc : L.IsCommutative) {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver σ f) (hx : L.IsTorsionPoint σ 2 x) :
    Tx L σ x ≫ (L.baseChange σ).schemeNsmul 2 = (L.baseChange σ).schemeNsmul 2 :=
  translate_comp_schemeNsmul_of_mem_torsionSubset _ (hc.baseChange σ) 2 _ (xpt_mem_torsionSubset L σ 2 x hx)

theorem Tx_mul {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S))
    (x y : SchemeHomOver σ f) : Tx L σ (L.mul σ x y) = Tx L σ x ≫ Tx L σ y := by
  unfold Tx
  rw [← translate_mul]
  congr 1
  rw [baseChange_mul]
  unfold xpt
  rw [baseChangePointToBase_ofBase, baseChangePointToBase_ofBase]

  congr 1

theorem baseChangeSnd_fst {T T' : Type} [CommRing T] [CommRing T']
    {s : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)} {s' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver s' s) : baseChangeSnd f ψ ≫ pullback.fst f s = pullback.fst f s' := by
  unfold baseChangeSnd; rw [pullback.lift_fst, Category.comp_id]

theorem baseChangeSnd_snd {T T' : Type} [CommRing T] [CommRing T']
    {s : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)} {s' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver s' s) : baseChangeSnd f ψ ≫ pullback.snd f s = pullback.snd f s' ≫ ψ.1 := by
  unfold baseChangeSnd; rw [pullback.lift_snd]

theorem schemeNsmul_comp_baseChangeSnd {T T' : Type} [CommRing T] [CommRing T']
    {s : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)} {s' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver s' s) (n : ℕ) :
    (L.baseChange s').schemeNsmul n ≫ baseChangeSnd f ψ = baseChangeSnd f ψ ≫ (L.baseChange s).schemeNsmul n := by
  have w := (isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange s L n).1.w
  have w' := (isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange s' L n).1.w
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeSnd_fst, Category.assoc, ← w, ← Category.assoc, baseChangeSnd_fst, w']
  · rw [Category.assoc, baseChangeSnd_snd, Category.assoc, (L.baseChange s).schemeNsmul_over, ← Category.assoc,
      (L.baseChange s').schemeNsmul_over, baseChangeSnd_snd]

noncomputable def fstPt {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) :
    SchemeHomOver (pullback.fst f σ ≫ f) f := ⟨pullback.fst f σ, rfl⟩

noncomputable def sndPt {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver σ f) :
    SchemeHomOver (pullback.fst f σ ≫ f) f :=
  ⟨pullback.snd f σ ≫ x.1, by rw [Category.assoc, x.2, pullback.condition]⟩

theorem mul_coe_congr {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ Q₁ : SchemeHomOver t₁ f} {P₂ Q₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht; rw [Subtype.ext hP, Subtype.ext hQ]

theorem Tx_fst {T : Type} [CommRing T] (σ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver σ f) :
    Tx L σ x ≫ pullback.fst f σ = (L.mul (pullback.fst f σ ≫ f) (fstPt σ) (sndPt σ x)).1 := by
  unfold Tx RelativeGroupLaw.translate
  rw [baseChange_mul, baseChangePointOfBase_coe, pullback.lift_fst]
  apply mul_coe_congr L
  · exact pullback.condition.symm
  · rw [baseChangePointToBase_coe]; exact Category.id_comp _
  · rw [baseChangePointToBase_coe, Category.assoc, xpt_fst]; rfl

theorem Tx_comp_baseChangeSnd {T T' : Type} [CommRing T] [CommRing T']
    {s : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)} {s' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver s' s) (x : SchemeHomOver s f) (x' : SchemeHomOver s' f) (hxx : x'.1 = ψ.1 ≫ x.1) :
    Tx L s' x' ≫ baseChangeSnd f ψ = baseChangeSnd f ψ ≫ Tx L s x := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeSnd_fst, Tx_fst, Category.assoc, Tx_fst]
    have hn := congrArg Subtype.val
      (L.mul_natural (pullback.fst f s ≫ f) (baseChangeSnd f ψ ≫ pullback.fst f s ≫ f) (baseChangeSnd f ψ) rfl
        (fstPt s) (sndPt s x))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at hn
    rw [hn]
    apply mul_coe_congr L
    · rw [← Category.assoc, baseChangeSnd_fst]
    · show pullback.fst f s' = baseChangeSnd f ψ ≫ pullback.fst f s
      rw [baseChangeSnd_fst]
    · show pullback.snd f s' ≫ x'.1 = baseChangeSnd f ψ ≫ (pullback.snd f s ≫ x.1)
      rw [← Category.assoc, baseChangeSnd_snd, Category.assoc, hxx]
  · rw [Category.assoc, baseChangeSnd_snd, ← Category.assoc, Tx_over, Category.assoc, Tx_over, baseChangeSnd_snd]

end PhiSetup

namespace PhiMain

p2m_open "P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial.PhiCore P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial.PhiSetup GoodReductionJacobian.RelativeGroupLaw"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem isInvertible_tensorUnit (X : Scheme.{0}) : Scheme.Modules.IsInvertible (𝟙_ X.Modules) := by
  rw [Scheme.Modules.tensorUnit_eq]; exact Scheme.Modules.isInvertible_unit X

section Test

variable (L : RelativeGroupLaw S f) {R : Type} [CommRing R] {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}

abbrev KER2 (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) : Prop :=
  Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _)

theorem ker2_pullbackAlong {R' : Type} [CommRing R'] {ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)}
    (ψ : SchemeHomOver ι' ι) (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (h : KER2 L ι N) : KER2 L ι' (N.pullbackAlong ψ) := by
  obtain ⟨e⟩ := h
  exact ⟨(Scheme.Modules.pullbackComp ((L.baseChange ι').schemeNsmul 2) (baseChangeSnd f ψ)).app N.L ≪≫
    (Scheme.Modules.pullbackCongr (schemeNsmul_comp_baseChangeSnd L ψ 2)).app N.L ≪≫
    ((Scheme.Modules.pullbackComp (baseChangeSnd f ψ) ((L.baseChange ι).schemeNsmul 2)).app N.L).symm ≪≫
    (Scheme.Modules.pullback (baseChangeSnd f ψ)).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (baseChangeSnd f ψ)⟩

variable (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
  (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))

include L hc hA N T κ

omit hc hA in
theorem nonempty_beta (h : KER2 L ι N) :
    Nonempty ((Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
      (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _)) := by
  obtain ⟨e⟩ := ker2_pullbackAlong L (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι) N h
  exact ⟨e ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm⟩

omit hc hA in

noncomputable def beta0 (h : KER2 L ι N) :
    (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
      (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _) :=
  Classical.choice (nonempty_beta L N T κ h)

noncomputable def rawVal (h : KER2 L ι N) (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) : T :=
  valueOf (pullback.snd f (κ ≫ ι)) (hH0_of hA (κ ≫ ι)) (Tx_q L hc (κ ≫ ι) x hx) (isInvertible_tensorUnit _)
    (beta0 L N T κ h)

theorem hasValue_rawVal (h : KER2 L ι N) (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
    (β : (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
      (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _)) :
    HasValue (pullback.snd f (κ ≫ ι)) (Tx_q L hc (κ ≫ ι) x hx) β (rawVal L hc hA N T κ h x hx) := by
  unfold rawVal
  rw [valueOf_eq_valueOf (pullback.snd f (κ ≫ ι)) (hH0_of hA (κ ≫ ι)) (Tx_q L hc (κ ≫ ι) x hx)
    (isInvertible_tensorUnit _) (Tx_over L (κ ≫ ι) x) (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).isInvertible (beta0 L N T κ h) β]
  exact hasValue_valueOf _ _ _ _ β

theorem rawVal_unique (h : KER2 L ι N) (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
    (β : (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
      (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _)) (c : T)
    (hcv : HasValue (pullback.snd f (κ ≫ ι)) (Tx_q L hc (κ ≫ ι) x hx) β c) : c = rawVal L hc hA N T κ h x hx := by
  rw [valueOf_unique (pullback.snd f (κ ≫ ι)) (hH0_of hA (κ ≫ ι)) (Tx_q L hc (κ ≫ ι) x hx) (isInvertible_tensorUnit _) hcv]
  unfold rawVal
  exact valueOf_eq_valueOf _ _ _ _ (Tx_over L (κ ≫ ι) x) (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).isInvertible β _

theorem isUnit_rawVal (h : KER2 L ι N) (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) :
    IsUnit (rawVal L hc hA N T κ h x hx) :=
  isUnit_valueOf _ _ _ _ _

noncomputable def unitVal (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) : Tˣ := by
  classical
  exact if h : KER2 L ι N then (isUnit_rawVal L hc hA N T κ h x hx).unit else 1

theorem unitVal_of_ker2 (h : KER2 L ι N) (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) :
    ((unitVal L hc hA N T κ x hx : Tˣ) : T) = rawVal L hc hA N T κ h x hx := by
  unfold unitVal; rw [dif_pos h]; rfl

theorem unitVal_of_not_ker2 (h : ¬ KER2 L ι N) (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) :
    unitVal L hc hA N T κ x hx = 1 := by
  unfold unitVal; rw [dif_neg h]

theorem rawVal_mul (h : KER2 L ι N) (x y : SchemeHomOver (κ ≫ ι) f)
    (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) (hy : L.IsTorsionPoint (κ ≫ ι) 2 y)
    (hxy : L.IsTorsionPoint (κ ≫ ι) 2 (L.mul (κ ≫ ι) x y)) :
    rawVal L hc hA N T κ h (L.mul (κ ≫ ι) x y) hxy = rawVal L hc hA N T κ h x hx * rawVal L hc hA N T κ h y hy := by
  have h12 : (Tx L (κ ≫ ι) x ≫ Tx L (κ ≫ ι) y) ≫ (L.baseChange (κ ≫ ι)).schemeNsmul 2 =
      (L.baseChange (κ ≫ ι)).schemeNsmul 2 := by
    rw [Category.assoc, Tx_q L hc _ y hy, Tx_q L hc _ x hx]
  have hprod := hasValue_comp_of_comp_eq (pullback.snd f (κ ≫ ι)) (Tx_q L hc _ x hx) (Tx_q L hc _ y hy)
    (Tx_over L _ x) h12 (beta0 L N T κ h) _ _
    (hasValue_rawVal L hc hA N T κ h x hx _) (hasValue_rawVal L hc hA N T κ h y hy _)
  have key : HasValue (pullback.snd f (κ ≫ ι)) (Tx_q L hc _ (L.mul (κ ≫ ι) x y) hxy) (beta0 L N T κ h)
      (rawVal L hc hA N T κ h x hx * rawVal L hc hA N T κ h y hy) :=
    hasValue_of_eq' (pullback.snd f (κ ≫ ι)) (Tx_mul L (κ ≫ ι) x y).symm h12 _ (beta0 L N T κ h) _ hprod
  exact (rawVal_unique L hc hA N T κ h _ hxy _ _ key).symm

end Test

variable (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)

theorem rawVal_natural {R : Type} [CommRing R] {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (h : KER2 L ι N)
    (T T' : Type) [CommRing T] [CommRing T']
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R)) (κ' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R))
    (φ : T →+* T') (hκ : Spec.map (CommRingCat.ofHom φ) ≫ κ = κ')
    (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
    (x' : SchemeHomOver (κ' ≫ ι) f) (hx' : L.IsTorsionPoint (κ' ≫ ι) 2 x')
    (hxx : x'.1 = Spec.map (CommRingCat.ofHom φ) ≫ x.1) :
    rawVal L hc hA N T' κ' h x' hx' = φ (rawVal L hc hA N T κ h x hx) := by

  let ψ : SchemeHomOver (κ' ≫ ι) (κ ≫ ι) := ⟨Spec.map (CommRingCat.ofHom φ), by rw [← Category.assoc, hκ]⟩
  have hq : baseChangeSnd f ψ ≫ (L.baseChange (κ ≫ ι)).schemeNsmul 2 =
      (L.baseChange (κ' ≫ ι)).schemeNsmul 2 ≫ baseChangeSnd f ψ := (schemeNsmul_comp_baseChangeSnd L ψ 2).symm
  have hT : Tx L (κ' ≫ ι) x' ≫ baseChangeSnd f ψ = baseChangeSnd f ψ ≫ Tx L (κ ≫ ι) x :=
    Tx_comp_baseChangeSnd L ψ x x' hxx
  have hf : baseChangeSnd f ψ ≫ pullback.snd f (κ ≫ ι) = pullback.snd f (κ' ≫ ι) ≫ Spec.map (CommRingCat.ofHom φ) :=
    baseChangeSnd_snd ψ
  have hv := hasValue_map_pullback_of_comm_sq (pullback.snd f (κ ≫ ι)) (pullback.snd f (κ' ≫ ι)) φ
    (Tx_q L hc _ x hx) (Tx_q L hc _ x' hx') (baseChangeSnd f ψ) (baseChangeSnd f ψ) hq hT hf
    (beta0 L N T κ h) _ (hasValue_rawVal L hc hA N T κ h x hx _)

  have hbcs : baseChangeSnd f ψ ≫ baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι) = baseChangeSnd f (⟨κ', rfl⟩ : SchemeHomOver (κ' ≫ ι) ι) := by
    rw [baseChangeSnd_comp]; congr 1; exact Subtype.ext hκ
  let eN : (Scheme.Modules.pullback (baseChangeSnd f ψ)).obj (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅ (N.pullbackAlong (⟨κ', rfl⟩ : SchemeHomOver (κ' ≫ ι) ι)).L :=
    (Scheme.Modules.pullbackComp (baseChangeSnd f ψ) (baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))).app N.L ≪≫
      (Scheme.Modules.pullbackCongr hbcs).app N.L
  let eM : (Scheme.Modules.pullback (baseChangeSnd f ψ)).obj (𝟙_ _) ≅
      (𝟙_ (pullback f (κ' ≫ ι)).Modules) := Scheme.Modules.pullbackTensorUnitObjIso _
  have h1 := hasValue_pullback_mapIso_one (pullback.snd f (κ' ≫ ι)) (Tx_q L hc _ x' hx') eN.symm
  have h3 := hasValue_pullback_mapIso_one (pullback.snd f (κ' ≫ ι)) (Tx_q L hc _ x' hx') eM
  have h13 := hasValue_trans _ _ _ _ _ _ (hasValue_trans _ _ _ _ _ _ h1 hv) h3
  rw [_root_.one_mul, _root_.mul_one] at h13
  exact (rawVal_unique L hc hA N T' κ' h x' hx' _ _ h13).symm

noncomputable def Phi {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) : L.TorsionCharacter 2 ι where
  val T _ κ x hx := unitVal L hc hA N T κ x hx
  val_mul T _ κ x y hx hy hxy := by
    by_cases h : KER2 L ι N
    · apply Units.ext
      rw [Units.val_mul, unitVal_of_ker2 L hc hA N T κ h, unitVal_of_ker2 L hc hA N T κ h, unitVal_of_ker2 L hc hA N T κ h]
      exact rawVal_mul L hc hA N T κ h x y hx hy hxy
    · rw [unitVal_of_not_ker2 L hc hA N T κ h, unitVal_of_not_ker2 L hc hA N T κ h, unitVal_of_not_ker2 L hc hA N T κ h,
        _root_.mul_one]
  val_natural T T' _ _ κ κ' φ hκ x hx x' hx' hxx := by
    by_cases h : KER2 L ι N
    · apply Units.ext
      rw [Units.coe_map, MonoidHom.coe_coe, unitVal_of_ker2 L hc hA N T' κ' h, unitVal_of_ker2 L hc hA N T κ h]
      exact rawVal_natural L hc hA N h T T' κ κ' φ hκ x hx x' hx' hxx
    · rw [unitVal_of_not_ker2 L hc hA N T' κ' h, unitVal_of_not_ker2 L hc hA N T κ h, map_one]

theorem Phi_val {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (T : Type) [CommRing T]
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) :
    (Phi L hc hA ι N).val T κ x hx = unitVal L hc hA N T κ x hx := rfl

end PhiMain

namespace PhiMain

p2m_open "P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial.PhiCore P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial.PhiSetup GoodReductionJacobian.RelativeGroupLaw"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
  {R : Type} [CommRing R] {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}

theorem ker2_of_iso (N N' : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (e : N.L ≅ N'.L) (h : KER2 L ι N) : KER2 L ι N' := by
  obtain ⟨β⟩ := h
  exact ⟨((Scheme.Modules.pullback _).mapIso e).symm ≪≫ β⟩

theorem unitVal_congr (N N' : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (e : N.L ≅ N'.L)
    (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) :
    unitVal L hc hA N T κ x hx = unitVal L hc hA N' T κ x hx := by
  by_cases h : KER2 L ι N
  · have h' : KER2 L ι N' := ker2_of_iso L N N' e h
    apply Units.ext
    rw [unitVal_of_ker2 L hc hA N T κ h, unitVal_of_ker2 L hc hA N' T κ h']

    let eT : (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅ (N'.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L :=
      (Scheme.Modules.pullback (baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))).mapIso e
    have h1 := hasValue_pullback_mapIso_one (pullback.snd f (κ ≫ ι)) (Tx_q L hc _ x hx)
      (q := (L.baseChange (κ ≫ ι)).schemeNsmul 2) eT
    have h2 := hasValue_rawVal L hc hA N' T κ h' x hx (beta0 L N' T κ h')
    have h12 := hasValue_trans _ _ _ _ _ _ h1 h2
    rw [_root_.one_mul] at h12
    exact (rawVal_unique L hc hA N T κ h x hx _ _ h12).symm
  · have h' : ¬ KER2 L ι N' := fun h' => h (ker2_of_iso L N' N e.symm h')
    rw [unitVal_of_not_ker2 L hc hA N T κ h, unitVal_of_not_ker2 L hc hA N' T κ h']

theorem unitVal_of_iso_unit (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (e : N.L ≅ 𝟙_ _)
    (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) :
    unitVal L hc hA N T κ x hx = 1 := by
  have h : KER2 L ι N := ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _⟩
  apply Units.ext
  rw [unitVal_of_ker2 L hc hA N T κ h, Units.val_one]
  let eT : (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅ 𝟙_ _ :=
    (Scheme.Modules.pullback (baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))).mapIso e ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  have h1 := hasValue_pullback_mapIso_one (pullback.snd f (κ ≫ ι)) (Tx_q L hc _ x hx)
    (q := (L.baseChange (κ ≫ ι)).schemeNsmul 2) eT
  exact (rawVal_unique L hc hA N T κ h x hx _ _ h1).symm

theorem unitVal_tensor (N N' N'' : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (hN : KER2 L ι N) (hN' : KER2 L ι N')
    (e : N''.L ≅ N.L ⊗ N'.L)
    (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x) :
    unitVal L hc hA N'' T κ x hx = unitVal L hc hA N T κ x hx * unitVal L hc hA N' T κ x hx := by
  obtain ⟨b⟩ := hN
  obtain ⟨b'⟩ := hN'
  have hN'' : KER2 L ι N'' :=
    ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (b ⊗ᵢ b') ≪≫ λ_ (𝟙_ _)⟩
  apply Units.ext
  rw [Units.val_mul, unitVal_of_ker2 L hc hA N'' T κ hN'', unitVal_of_ker2 L hc hA N T κ ⟨b⟩,
    unitVal_of_ker2 L hc hA N' T κ ⟨b'⟩]

  let g := baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)
  let q := (L.baseChange (κ ≫ ι)).schemeNsmul 2
  let eT : (N''.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
      (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ⊗ (N'.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L :=
    (Scheme.Modules.pullback g).mapIso e ≪≫ Scheme.Modules.pullbackTensorObjIso g N.L N'.L
  have h1 := hasValue_pullback_mapIso_one (pullback.snd f (κ ≫ ι)) (Tx_q L hc _ x hx) (q := q) eT
  have h2 := hasValue_tensor (pullback.snd f (κ ≫ ι)) (Tx_q L hc _ x hx)
    (beta0 L N T κ ⟨b⟩) (beta0 L N' T κ ⟨b'⟩) _ _
    (hasValue_rawVal L hc hA N T κ ⟨b⟩ x hx _) (hasValue_rawVal L hc hA N' T κ ⟨b'⟩ x hx _)
  have h3 := hasValue_pullback_mapIso_one (pullback.snd f (κ ≫ ι)) (Tx_q L hc _ x hx) (q := q)
    (λ_ (𝟙_ (pullback f (κ ≫ ι)).Modules))
  have h123 := hasValue_trans _ _ _ _ _ _ (hasValue_trans _ _ _ _ _ _ h1 h2) h3
  rw [_root_.one_mul, _root_.mul_one] at h123
  exact (rawVal_unique L hc hA N'' T κ hN'' x hx _ _ h123).symm

end PhiMain

open PhiCore PhiSetup PhiMain in
theorem solution
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2))
    (h2fl : IsAffineHom (L.schemeNsmul 2) ∧ Flat (L.schemeNsmul 2) ∧ Surjective (L.schemeNsmul 2)) :
    ∃ Φ : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
        RigidifiedLineBundle f (L.one (𝟙 _)) ι → L.TorsionCharacter 2 ι,
      let Adm : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
          RigidifiedLineBundle f (L.one (𝟙 _)) ι → Prop :=
        fun R _ ι N =>
          Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _)
      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Adm R ι N →
          ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
            (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
            (hTq : (L.baseChange (κ ≫ ι)).translate
                (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
                  ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫ (L.baseChange (κ ≫ ι)).schemeNsmul 2 =
              (L.baseChange (κ ≫ ι)).schemeNsmul 2)
            (β : (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj
                  (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
                (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _)),
            HasValue (pullback.snd f (κ ≫ ι)) hTq β (((Φ R ι N).val T κ x hx : Tˣ) : T) ∧
            ∀ c : T, HasValue (pullback.snd f (κ ≫ ι)) hTq β c → c = (((Φ R ι N).val T κ x hx : Tˣ) : T)) ∧
      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (N N' : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Nonempty (N.L ≅ N'.L) → Φ R ι N = Φ R ι N') ∧
      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (N N' N'' : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Adm R ι N → Adm R ι N' →
          Nonempty (N''.L ≅ N.L ⊗ N'.L) →
          ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
            (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x),
            (Φ R ι N'').val T κ x hx = (Φ R ι N).val T κ x hx * (Φ R ι N').val T κ x hx) ∧
      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Nonempty (N.L ≅ 𝟙_ _) →
          ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
            (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x),
            (Φ R ι N).val T κ x hx = 1) := by
  refine ⟨fun R _ ι N => Phi L hc hA ι N, ?_, ?_, ?_, ?_⟩
  · intro R _ ι N hAdm T _ κ x hx hTq β
    rw [Phi_val, unitVal_of_ker2 L hc hA N T κ hAdm x hx]
    exact ⟨hasValue_rawVal L hc hA N T κ hAdm x hx β, fun c hcv => rawVal_unique L hc hA N T κ hAdm x hx β c hcv⟩
  · intro R _ ι N N' hNN'
    obtain ⟨e⟩ := hNN'
    apply RelativeGroupLaw.TorsionCharacter.ext
    funext T instT κ x hx
    exact unitVal_congr L hc hA N N' e T κ x hx
  · intro R _ ι N N' N'' hN hN' hNN'' T _ κ x hx
    obtain ⟨e⟩ := hNN''
    exact unitVal_tensor L hc hA N N' N'' hN hN' e T κ x hx
  · intro R _ ι N hN T _ κ x hx
    obtain ⟨e⟩ := hN
    exact unitVal_of_iso_unit L hc hA N e T κ x hx

end S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial (solution)
