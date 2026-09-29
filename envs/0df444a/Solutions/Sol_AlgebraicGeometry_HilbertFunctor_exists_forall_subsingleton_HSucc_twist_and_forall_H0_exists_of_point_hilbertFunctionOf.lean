-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ca312f1d-7eb3-5efc-992f-e02e81601c51

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le
import Theorems.Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
import Theorems.Thm_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth
import Theorems.Thm_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_isHomogeneous_of_baseChange_field
import Theorems.Thm_AlgebraicGeometry_ProjSpace_subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field
import Theorems.Thm_AlgebraicGeometry_ProjSpace_mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec"

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RegCohAdapter

variable {n : ℕ}

theorem homogeneous_of_span {K : Type} [CommRing K] {e : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) :
    ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  have hh : (Ideal.span s).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) := by
    apply Ideal.homogeneous_span
    intro x hx
    exact ⟨e, (mem_homogeneousSubmodule e x).mpr (hs x hx)⟩
  intro p hp i
  have := hh i hp
  rw [show ((DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) K) p i : MvPolynomial (Fin (n + 1)) K))
      = homogeneousComponent i p from decomposition.decompose'_apply p i] at this
  exact this

theorem finrank_piece_eq {K : Type} [Field K] {h : ℕ → ℕ} (p : Point K n h) (e : ℕ) :
    Module.finrank K (piece p.I e) = h e := by
  haveI := p.finite_piece e
  have h1 := p.rankAtStalk_piece e ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1
  exact h1

end RegCohAdapter

open RegCohAdapter in
theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m → ∀ (k : Type) [Field k] (Zk : Scheme.{0})
      (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
      (q : Point k n (hilbertFunctionOf n P m)),
      (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ q.I ↔ ∀ i : Fin (n + 1),
          (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0)) →
      ∀ d : ℕ, m ≤ d →
        (∀ i : ℕ, Subsingleton
          ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).HSucc (ProjSpace.stdCoverPullback ιk) i)) ∧
        (∀ c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk),
          ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
            ∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
              (c s).val i =
                ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i ≤
                    ProjSpace.pullbackChart ιk i)
                  ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) := by
  classical
  obtain ⟨Dg, hDg⟩ := MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval n P hP
  obtain ⟨K₀, _, I₀, hI₀, d₁, hd₁⟩ := hP

  set H : ℕ → ℕ := fun e => Int.toNat ⌊P.eval (e : ℚ)⌋ with hH
  have hHcast : ∀ e : ℕ, d₁ ≤ e → ((H e : ℕ) : ℚ) = P.eval (e : ℚ) := by
    intro e he
    rw [hH]; dsimp only
    rw [← hd₁ e he, Int.floor_natCast, Int.toNat_natCast]

  have hMac : ∀ e, max Dg (max d₁ 1) ≤ e → H (e + 1) ≤ Nat.macaulayPow e (H e) := by
    intro e he
    have heg : Dg ≤ e := le_trans (le_max_left _ _) he
    have he1 : d₁ ≤ e := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) he
    have he2 : 1 ≤ e := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) he
    obtain ⟨K₂, _, J₂, hJ₂, hJm, hJm1⟩ := (hDg e heg).2
    have hhom := homogeneous_of_span J₂ hJ₂
    have hM := MvPolynomial.finrank_piece_succ_le_macaulayPow n e he2 K₂ J₂ hhom
    have h1 : Module.finrank K₂ (piece J₂ e) = H e := by
      exact_mod_cast (hJm.trans (hHcast e he1).symm)
    have h2 : Module.finrank K₂ (piece J₂ (e + 1)) = H (e + 1) := by
      have := hHcast (e + 1) (by omega)
      push_cast at this hJm1
      exact_mod_cast (hJm1.trans this.symm)
    rw [← h1, ← h2]; exact hM
  obtain ⟨D₁, hD₁⟩ := Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow H (max Dg (max d₁ 1)) (le_trans (le_max_right _ _) (le_max_right _ _)) hMac
  refine ⟨max D₁ (max Dg (max d₁ 1)), fun m hm k _ Zk ιk _ q hZ => ?_⟩
  have hmD₁ : D₁ ≤ m := le_trans (le_max_left _ _) hm
  have hmg : Dg ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hm₁ : d₁ ≤ m := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hm

  have hhH : ∀ e, m ≤ e → hilbertFunctionOf n P m e = H e := by
    intro e he; simp [hilbertFunctionOf, not_lt.mpr he, hH]
  have hcast : ∀ e : ℕ, m ≤ e → ((hilbertFunctionOf n P m e : ℕ) : ℚ) = P.eval (e : ℚ) := by
    intro e he; rw [hhH e he]; exact hHcast e (le_trans hm₁ he)

  have hgen : ∀ (K : Type) [Field K] (p : Point K n (hilbertFunctionOf n P m)),
      p.I = Ideal.span {f | f ∈ p.I ∧ f.IsHomogeneous m} := by
    intro K _ p
    refine AlgebraicGeometry.HilbertFunctor.Point.I_eq_span_of_forall_finrank_piece_succ_le n m (hilbertFunctionOf n P m) ?_ ?_ K p
    · intro d hd; simp [hilbertFunctionOf, hd]
    · intro e he K' _ J hJ hJe
      have he1 : m ≤ e + 1 := Nat.le_succ_of_le he
      have h1 := (hDg e (le_trans hmg he)).1 K' J hJ (by rw [hJe]; exact hcast e he)
      rw [show ((e : ℚ) + 1) = ((e + 1 : ℕ) : ℚ) by push_cast; ring, ← hcast (e + 1) he1] at h1
      exact_mod_cast h1
  have hmax : Nat.macaulayPow m (hilbertFunctionOf n P m m) = hilbertFunctionOf n P m (m + 1) := by
    rw [hhH m le_rfl, hhH (m + 1) (Nat.le_succ m)]; exact (hD₁ m hmD₁).symm

  have hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) k), (∀ f ∈ s, f.IsHomogeneous m) ∧ q.I = Ideal.span s :=
    ⟨{f | f ∈ q.I ∧ f.IsHomogeneous m}, fun f hf => hf.2, hgen k q⟩
  have hmaxk : Module.finrank k (piece q.I (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece q.I m)) := by
    rw [finrank_piece_eq, finrank_piece_eq, hmax]

  let K' : Type := AlgebraicClosure k
  obtain ⟨Zk', ιk', hcl, e, hpb, hcomp⟩ :=
    AlgebraicGeometry.ProjSpace.exists_isClosedImmersion_isPullback_comp_eq_map ιk K'
  haveI := hcl
  obtain ⟨-, hbc⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n k K' q.I q.homogeneous
  have hJ' : ∃ s : Set (MvPolynomial (Fin (n + 1)) K'), (∀ f ∈ s, f.IsHomogeneous m) ∧
      q.I.map (MvPolynomial.map (algebraMap k K')) = Ideal.span s := by
    obtain ⟨s, hs, hqs⟩ := hJ
    refine ⟨MvPolynomial.map (algebraMap k K') '' s, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩; exact (hs f hf).map _
    · rw [hqs, Ideal.map_span]
  have hfr : ∀ d : ℕ, Module.finrank K' (piece (q.I.map (MvPolynomial.map (algebraMap k K'))) d)
      = Module.finrank k (piece q.I d) := by
    intro d
    obtain ⟨ε, -⟩ := hbc d
    haveI := q.finite_piece d
    rw [← ε.finrank_eq, Module.finrank_baseChange]
  have hmax' : Module.finrank K' (piece (q.I.map (MvPolynomial.map (algebraMap k K'))) (m + 1))
      = Nat.macaulayPow m (Module.finrank K' (piece (q.I.map (MvPolynomial.map (algebraMap k K'))) m)) := by
    rw [hfr, hfr, hmaxk]
  have hZ' := AlgebraicGeometry.ProjSpace.mem_map_iff_forall_app_awayToSection_eq_zero_of_baseChange_field
    ιk K' ιk' e hpb hcomp m q.I q.homogeneous hZ
  have main' := AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth
    n m hm1 K' (q.I.map (MvPolynomial.map (algebraMap k K'))) hJ' hmax' Zk' ιk' hZ'
  intro d hd
  obtain ⟨ha', hb'⟩ := main' d hd
  exact ⟨fun i => AlgebraicGeometry.ProjSpace.subsingleton_HSucc_twist_of_subsingleton_HSucc_twist_baseChange_field
      ιk K' ιk' e hpb hcomp d i (ha' i),
    AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_isHomogeneous_of_baseChange_field ιk K' ιk' e hpb hcomp d hb'⟩

end
end S_AlgebraicGeometry_HilbertFunctor_exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf (solution)
