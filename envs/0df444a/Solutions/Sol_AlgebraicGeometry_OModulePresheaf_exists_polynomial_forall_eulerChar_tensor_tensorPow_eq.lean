-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b53d0b8c-6d7d-5e65-971d-b4c565c3e508

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry TensorProduct Opposite"

noncomputable section

namespace P2mChiSheaf

p2m_open "AlgebraicGeometry.OModulePresheaf~zero"

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem isInvertible_tensorPow (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) (n : ℕ) :
    Scheme.Modules.IsInvertible (L.tensorPow n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit V
  | succ n ih => exact ih.tensor ⟨hL⟩

section Compare

variable (M N : V.Modules)

abbrev cmp (U : V.Opens) : Γ(M, U) ⊗[Γ(V, U)] Γ(N, U) →ₗ[Γ(V, U)] Γ(M ⊗ N, U) :=
  TensorProduct.lift (Scheme.Modules.tensorSectionsBilin M N U)

theorem cmp_tmul (U : V.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    cmp M N U (s ⊗ₜ t) = Scheme.Modules.tensorSections s t := by
  simp [cmp]

def resTw {U U' : V.Opens} (h : U ≤ U') :
    Γ(M, U') ⊗[Γ(V, U')] Γ(N, U') →ₛₗ[(V.presheaf.map (homOfLE h).op).hom] Γ(M, U) ⊗[Γ(V, U)] Γ(N, U) :=
  (ofModules π M).tensorResₛₗ (ofModules π N) h

theorem resTw_tmul {U U' : V.Opens} (h : U ≤ U') (x : Γ(M, U')) (y : Γ(N, U')) :
    resTw π M N h (x ⊗ₜ y) = M.presheaf.map (homOfLE h).op x ⊗ₜ N.presheaf.map (homOfLE h).op y := rfl

theorem cmp_resTw {U U' : V.Opens} (h : U ≤ U') (t : Γ(M, U') ⊗[Γ(V, U')] Γ(N, U')) :
    cmp M N U (resTw π M N h t) = (M ⊗ N).presheaf.map (homOfLE h).op (cmp M N U' t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [resTw_tmul, cmp_tmul, cmp_tmul]
    exact (Scheme.Modules.map_homOfLE_tensorSections h x y).symm
  | add a b ha hb => simp only [map_add, ha, hb]

theorem cmp_res {U U' : V.Opens} (h : U ≤ U') (t : ((ofModules π M).twist N).obj U') :
    cmp M N U (((ofModules π M).twist N).res h t) = (M ⊗ N).presheaf.map (homOfLE h).op (cmp M N U' t) :=
  cmp_resTw π M N h t

def cmpHom : AffHom ((ofModules π M).twist N) (ofModules π (M ⊗ N)) where
  app U :=
    { toFun := cmp M N U.1
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r t => map_smul (cmp M N U.1)
        ((Scheme.TwoAffineOpenCover.algebraOfHom π U.1).algebraMap r) t }
  app_smul U a t := map_smul (cmp M N U.1) a t
  naturality h := LinearMap.ext fun t => cmp_res π M N h t

theorem cmpHom_app (U : V.affineOpens) (t : ((ofModules π M).twist N).obj U.1) :
    (cmpHom π M N).app U t = cmp M N U.1 t := rfl

theorem cmpHom_bijective (hM : (ofModules π M).IsQuasicoherent) (hN : (ofModules π N).IsQuasicoherent)
    (U : V.affineOpens) : Function.Bijective ((cmpHom π M N).app U) :=
  Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent π hM hN U

end Compare

theorem eulerChar_eq_of_bijective [IsSeparated π] (K : V.OrderedAffineCover) {F G : OModulePresheaf π}
    (φ : AffHom F G) (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U)) :
    F.eulerChar K = G.eulerChar K := by
  obtain ⟨⟨e0⟩, hS⟩ := AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective φ hφ K
  have h : ∀ i, F.cechFinrank K i = G.cechFinrank K i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem eulerChar_ofModules_tensor_eq [IsSeparated π] (K : V.OrderedAffineCover) (M N : V.Modules)
    (hM : (ofModules π M).IsQuasicoherent) (hN : (ofModules π N).IsQuasicoherent) :
    (ofModules π (M ⊗ N)).eulerChar K = ((ofModules π M).twist N).eulerChar K :=
  (eulerChar_eq_of_bijective π K (cmpHom π M N) (cmpHom_bijective π M N hM hN)).symm

theorem main {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (M : V.Modules)
    (hc : (OModulePresheaf.ofModules π M).IsCoherent) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (OModulePresheaf.ofModules π M).SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℕ, ((OModulePresheaf.ofModules π (M ⊗ L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ) := by
  obtain ⟨p, hp, hpn⟩ :=
    OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq π K (ofModules π M) hc hq Y hY d hd L hL
  refine ⟨p, hp, fun n => ?_⟩
  have hqn : (ofModules π (L.tensorPow n)).IsQuasicoherent :=
    isQuasicoherent_ofModules_of_locallyTrivial π (L.tensorPow n) (isInvertible_tensorPow L hL n).1
  rw [eulerChar_ofModules_tensor_eq π K M (L.tensorPow n) hq hqn]
  exact hpn n

end P2mChiSheaf

end

theorem solution
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (M : V.Modules)
    (hc : (OModulePresheaf.ofModules π M).IsCoherent) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (OModulePresheaf.ofModules π M).SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℕ, ((OModulePresheaf.ofModules π (M ⊗ L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ) :=
  P2mChiSheaf.main π K M hc hq Y hY d hd L hL

end S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq (solution)
