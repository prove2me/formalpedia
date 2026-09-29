-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6b2a96b7-1761-5216-aeb4-51549847c389

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AddCommGroup_exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsProper Spec Scheme Scheme.Modules Scheme.Modules.tensorPow_zero Scheme.Modules.tensorPow_succ Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.ofModules Scheme.Modules.tensorSections Scheme.Modules.tensorSectionsBilin Scheme.Modules.map_homOfLE_tensorSections OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2 Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso Scheme.Modules.IsInvertible.exists_tensor_inverse_monoidalV2 Scheme.Modules.IsInvertible.tensor_monoidalV2" namespace OModulePresheaf p2m_export "AlgebraicGeometry.OModulePresheaf" "cechFinrank eulerChar eulerChar_def d IsCoherent IsQuasicoherent SupportedIn unit res module obj ofModules tensorResₛₗ tensor twist AffHom exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2 isQuasicoherent_isCoherent_supportedIn_tensor isQuasicoherent_ofModules_of_locallyTrivial isCoherent_ofModules_of_locallyTrivial nonempty_cechEquiv_ofModules_of_iso" end AlgebraicGeometry.OModulePresheaf
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.OModulePresheaf" in
alias AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq := AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2
namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsProper Spec Scheme Scheme.Modules Scheme.Modules.tensorPow_zero Scheme.Modules.tensorPow_succ Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.ofModules Scheme.Modules.tensorSections Scheme.Modules.tensorSectionsBilin Scheme.Modules.map_homOfLE_tensorSections OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2 Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso Scheme.Modules.IsInvertible.exists_tensor_inverse_monoidalV2 Scheme.Modules.IsInvertible.tensor_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Γ affineOpens basicOpen Modules Opens basicOpen_le Modules.tensorPow_zero Modules.tensorPow_succ Modules.IsInvertible Modules.isInvertible_unit OrderedAffineCover TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom Modules.tensorSections Modules.tensorSectionsBilin Modules.map_homOfLE_tensorSections Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 Modules.IsInvertible.exists_tensor_inverse_monoidalV2 Modules.IsInvertible.tensor_monoidalV2" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf map_smul tensor tensorPow tensorPow_zero tensorPow_succ IsInvertible isInvertible_unit tensorSections tensorSectionsBilin map_homOfLE_tensorSections bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 IsInvertible.exists_tensor_inverse_monoidalV2 IsInvertible.tensor_monoidalV2" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
alias AlgebraicGeometry.Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent := AlgebraicGeometry.Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2
namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsProper Spec Scheme Scheme.Modules Scheme.Modules.tensorPow_zero Scheme.Modules.tensorPow_succ Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit OModulePresheaf Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.ofModules Scheme.Modules.tensorSections Scheme.Modules.tensorSectionsBilin Scheme.Modules.map_homOfLE_tensorSections OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2 Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso Scheme.Modules.IsInvertible.exists_tensor_inverse_monoidalV2 Scheme.Modules.IsInvertible.tensor_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Γ affineOpens basicOpen Modules Opens basicOpen_le Modules.tensorPow_zero Modules.tensorPow_succ Modules.IsInvertible Modules.isInvertible_unit OrderedAffineCover TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom Modules.tensorSections Modules.tensorSectionsBilin Modules.map_homOfLE_tensorSections Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 Modules.IsInvertible.exists_tensor_inverse_monoidalV2 Modules.IsInvertible.tensor_monoidalV2" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf map_smul tensor tensorPow tensorPow_zero tensorPow_succ IsInvertible isInvertible_unit tensorSections tensorSectionsBilin map_homOfLE_tensorSections bijective_lift_tensorSectionsBilin_of_isQuasicoherent_monoidalV2 IsInvertible.exists_tensor_inverse_monoidalV2 IsInvertible.tensor_monoidalV2" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "exists_tensor_inverse_monoidalV2 tensor_monoidalV2" end AlgebraicGeometry.Scheme.Modules.IsInvertible
namespace AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
private alias _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse_monoidalV2
end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse"
namespace AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
private alias _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor := AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2

end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor"
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2.AlgebraicGeometry TensorProduct Opposite"

noncomputable section

namespace P2mSnapperMulti

p2m_open "AlgebraicGeometry.OModulePresheaf~zero P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2.AlgebraicGeometry.OModulePresheaf Polynomial AlgebraicGeometry.Polynomial"

theorem exists_poly_of_forall_sub {F : ℤ → ℚ} {d : ℕ}
    (h : ∀ b : ℕ, ∃ P : ℚ[X], P.natDegree ≤ d ∧ ∀ a : ℕ, F ((a : ℤ) - b) = P.eval (a : ℚ)) :
    ∃ G : ℚ[X], G.natDegree ≤ d ∧ ∀ n : ℤ, F n = G.eval (n : ℚ) := by
  obtain ⟨P₀, hP₀, h0⟩ := h 0
  refine ⟨P₀, hP₀, fun n => ?_⟩
  obtain ⟨P, -, hP⟩ := h (-n).toNat
  set b := (-n).toNat with hb

  have hcomp : P = P₀.comp (X - C (b : ℚ)) := by
    apply Polynomial.eq_of_infinite_eval_eq P (P₀.comp (X - C (b : ℚ))) (Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => ((k + b : ℕ) : ℚ)) (fun x y hxy => by simpa using hxy) (fun k => ?_))
    simp only [Set.mem_setOf_eq, eval_comp, eval_sub, eval_X, eval_C]
    rw [← hP (k + b)]
    have e1 : ((k + b : ℕ) : ℤ) - (b : ℤ) = ((k : ℕ) : ℤ) - ((0 : ℕ) : ℤ) := by push_cast; ring
    have e2 : ((k + b : ℕ) : ℚ) - (b : ℚ) = (k : ℚ) := by push_cast; ring
    rw [e1, h0 k, e2]
  have hn : n = ((n.toNat : ℕ) : ℤ) - (b : ℤ) := by rw [hb]; omega
  have hq : (n : ℚ) = ((n.toNat : ℕ) : ℚ) - (b : ℚ) := by exact_mod_cast hn
  calc F n = F ((n.toNat : ℤ) - b) := by rw [← hn]
    _ = P.eval (n.toNat : ℚ) := hP _
    _ = P₀.eval ((n.toNat : ℚ) - b) := by rw [hcomp]; simp [eval_comp]
    _ = P₀.eval (n : ℚ) := by rw [hq]

section Compare

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M N : V.Modules)

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

theorem cmpHom_bijective (hM : (ofModules π M).IsQuasicoherent) (hN : (ofModules π N).IsQuasicoherent)
    (U : V.affineOpens) : Function.Bijective ((cmpHom π M N).app U) :=
  Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent π hM hN U

end Compare

section Transport

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
  (φ : AffHom F G) (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U))

theorem naturality_apply {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (x : F.obj U'.1) :
    φ.app U (F.res h x) = G.res h (φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (φ.naturality h)) x

include hφ

theorem isCoherent_of_bijective (hF : F.IsCoherent) : G.IsCoherent := by
  intro U
  haveI := hF U
  let e : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1 :=
    { toFun := φ.app U, map_add' := (φ.app U).map_add, map_smul' := φ.app_smul U }
  exact Module.Finite.of_surjective e (hφ U).2

theorem supportedIn_of_bijective (Y : TopologicalSpace.Closeds V) (hF : F.SupportedIn Y) : G.SupportedIn Y := by
  intro U hU
  haveI := hF U hU
  exact (hφ U).2.subsingleton

theorem isQuasicoherent_of_bijective (hF : F.IsQuasicoherent) : G.IsQuasicoherent := by
  intro U f
  let D : V.affineOpens := ⟨V.basicOpen f, U.2.basicOpen f⟩
  have hle : D.1 ≤ U.1 := V.basicOpen_le f
  obtain ⟨h1, h2⟩ := hF U f
  refine ⟨fun x' => ?_, fun y' hy' => ?_⟩
  · obtain ⟨x, rfl⟩ := (hφ D).2 x'
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨n, φ.app U y, ?_⟩
    have := naturality_apply φ (U := D) (U' := U) hle y
    change G.res hle (φ.app U y) = _
    rw [← this]
    change φ.app D (F.res (V.basicOpen_le f) y) = _
    rw [hy, φ.app_smul]
  · obtain ⟨y, rfl⟩ := (hφ U).2 y'
    have hn := naturality_apply φ (U := D) (U' := U) hle y
    change G.res hle (φ.app U y) = 0 at hy'
    rw [← hn] at hy'
    have h0 : F.res (V.basicOpen_le f) y = 0 :=
      (hφ D).1 (by change φ.app D (F.res hle y) = φ.app D 0; rw [hy', map_zero])
    obtain ⟨n, hn0⟩ := h2 y h0
    exact ⟨n, by rw [← φ.app_smul, hn0, map_zero]⟩

end Transport

section Chi

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k))

theorem eulerChar_congr {M M' : V.Modules} (e : M ≅ M') (K : V.OrderedAffineCover) :
    (ofModules π M).eulerChar K = (ofModules π M').eulerChar K := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso π e K
  have h : ∀ i, (ofModules π M).cechFinrank K i = (ofModules π M').cechFinrank K i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem props_tensor (M N : V.Modules) (hc : (ofModules π M).IsCoherent) (hq : (ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (ofModules π M).SupportedIn Y) (hN : Scheme.Modules.IsInvertible N) :
    (ofModules π (M ⊗ N)).IsCoherent ∧ (ofModules π (M ⊗ N)).IsQuasicoherent ∧ (ofModules π (M ⊗ N)).SupportedIn Y := by
  have hNq := isQuasicoherent_ofModules_of_locallyTrivial π N hN.1
  have hNc := isCoherent_ofModules_of_locallyTrivial π N hN.1
  obtain ⟨tq, tc, ts⟩ := isQuasicoherent_isCoherent_supportedIn_tensor (ofModules π M) (ofModules π N)
  have hb := cmpHom_bijective π M N hq hNq
  exact ⟨isCoherent_of_bijective _ hb (tc hc hNc), isQuasicoherent_of_bijective _ hb (tq hq hNq),
    supportedIn_of_bijective _ hb Y (ts Y (Or.inl hY))⟩

end Chi

section Pic

variable {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
  (K : V.OrderedAffineCover) (M : V.Modules)

theorem cls_tensor {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] (X Y : C) :
    toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y :=
  Skeleton.toSkeleton_tensorObj X Y

theorem cls_unit {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] :
    toSkeleton (𝟙_ C) = (1 : Skeleton C) := Skeleton.one_eq.symm

theorem cls_tensorPow (N : V.Modules) (n : ℕ) : toSkeleton (N.tensorPow n) = toSkeleton N ^ n := by
  induction n with
  | zero => rw [Scheme.Modules.tensorPow_zero, cls_unit, pow_zero]
  | succ n ih => rw [Scheme.Modules.tensorPow_succ, cls_tensor, ih, pow_succ]

variable (V) in

def picSubgroup : Subgroup (Skeleton V.Modules)ˣ where
  carrier := {w | ∃ N : V.Modules, Scheme.Modules.IsInvertible N ∧ toSkeleton N = w.val}
  mul_mem' := by
    rintro w w' ⟨N, hN, hNw⟩ ⟨N', hN', hNw'⟩
    exact ⟨N ⊗ N', hN.tensor hN', by rw [cls_tensor, hNw, hNw', Units.val_mul]⟩
  one_mem' := ⟨𝟙_ V.Modules, Scheme.Modules.isInvertible_unit V, by rw [cls_unit, Units.val_one]⟩
  inv_mem' := by
    rintro w ⟨N, hN, hNw⟩
    obtain ⟨N', hN', ⟨e⟩⟩ := hN.exists_tensor_inverse
    refine ⟨N', hN', ?_⟩
    have h1 : w.val * toSkeleton N' = 1 := by
      rw [← hNw, ← cls_tensor, ← cls_unit]; exact toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩
    exact (Units.inv_eq_of_mul_eq_one_right h1).symm

def unitOf {N : V.Modules} (hN : Scheme.Modules.IsInvertible N) : (Skeleton V.Modules)ˣ :=
  (show IsUnit (toSkeleton N) from by
    obtain ⟨N', -, ⟨e⟩⟩ := hN.exists_tensor_inverse
    have h := toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩
    rw [cls_tensor, cls_unit] at h
    exact IsUnit.of_mul_eq_one _ h).unit

theorem unitOf_val {N : V.Modules} (hN : Scheme.Modules.IsInvertible N) : (unitOf hN).val = toSkeleton N := rfl

theorem unitOf_mem {N : V.Modules} (hN : Scheme.Modules.IsInvertible N) : unitOf hN ∈ picSubgroup V :=
  ⟨N, hN, rfl⟩

def rep (w : picSubgroup V) : V.Modules := Classical.choose w.2

theorem rep_isInvertible (w : picSubgroup V) : Scheme.Modules.IsInvertible (rep w) := (Classical.choose_spec w.2).1

theorem toSkeleton_rep (w : picSubgroup V) : toSkeleton (rep w) = (w : (Skeleton V.Modules)ˣ).val :=
  (Classical.choose_spec w.2).2

def chiFun (x : Additive (picSubgroup V)) : ℚ :=
  ((ofModules π (M ⊗ rep (Additive.toMul x))).eulerChar K : ℚ)

theorem chiFun_eq (x : Additive (picSubgroup V)) (N : V.Modules)
    (hN : toSkeleton N = ((Additive.toMul x : picSubgroup V) : (Skeleton V.Modules)ˣ).val) :
    chiFun π K M x = ((ofModules π (M ⊗ N)).eulerChar K : ℚ) := by
  rw [← toSkeleton_rep] at hN
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.mp hN
  rw [chiFun, eulerChar_congr π (whiskerLeftIso M e) K]

variable (hc : (ofModules π M).IsCoherent) (hq : (ofModules π M).IsQuasicoherent)
  (Y : TopologicalSpace.Closeds V) (hY : (ofModules π M).SupportedIn Y) (d : ℕ) (hd : topologicalKrullDim Y ≤ d)

include hc hq hY hd

theorem chiFun_nsmul_add (x y : Additive (picSubgroup V)) :
    ∃ P : ℚ[X], P.natDegree ≤ d ∧ ∀ a : ℕ, chiFun π K M (a • x + y) = P.eval (a : ℚ) := by
  set Nx := rep (Additive.toMul x)
  set Ny := rep (Additive.toMul y)
  obtain ⟨hc', hq', hY'⟩ := props_tensor π M Ny hc hq Y hY (rep_isInvertible _)
  obtain ⟨P, hP, hPa⟩ := OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq π K (M ⊗ Ny)
    hc' hq' Y hY' d hd Nx (rep_isInvertible _).1
  refine ⟨P, hP, fun a => ?_⟩
  rw [← hPa a, eulerChar_congr π (α_ M Ny (Nx.tensorPow a)) K]
  apply chiFun_eq
  rw [cls_tensor, cls_tensorPow, toSkeleton_rep, toSkeleton_rep, toMul_add, toMul_nsmul]
  rw [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm]

theorem chiFun_zsmul_add (x y : Additive (picSubgroup V)) :
    ∃ P : ℚ[X], P.natDegree ≤ d ∧ ∀ n : ℤ, chiFun π K M (n • x + y) = P.eval (n : ℚ) := by
  apply exists_poly_of_forall_sub
  intro b
  obtain ⟨P, hP, hPa⟩ := chiFun_nsmul_add π K M hc hq Y hY d hd x ((-(b : ℤ)) • x + y)
  refine ⟨P, hP, fun a => ?_⟩
  rw [sub_eq_add_neg, add_zsmul, natCast_zsmul, add_assoc]
  exact hPa a

theorem main {ι : Type v} [Fintype ι] (L : ι → V.Modules) (hL : ∀ i, Scheme.Modules.IsInvertible (L i)) :
    ∃ P : MvPolynomial ι ℚ, P.totalDegree ≤ d ∧
      ∀ (a b : ι → ℕ) (N : V.Modules),
        toSkeleton N * ∏ i, toSkeleton (L i) ^ b i = ∏ i, toSkeleton (L i) ^ a i →
          ((ofModules π (M ⊗ N)).eulerChar K : ℚ) = MvPolynomial.eval (fun i => (a i : ℚ) - (b i : ℚ)) P := by
  let e : ι → Additive (picSubgroup V) := fun i => Additive.ofMul ⟨unitOf (hL i), unitOf_mem (hL i)⟩
  obtain ⟨P, hP, hPe⟩ :=
    AddCommGroup.exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add
      (chiFun π K M) d (chiFun_zsmul_add π K M hc hq Y hY d hd) e
  refine ⟨P, hP, fun a b N hN => ?_⟩
  have h := hPe (fun i => (a i : ℤ) - b i)
  simp only [Int.cast_sub, Int.cast_natCast] at h
  rw [h]
  symm
  apply chiFun_eq

  rw [toMul_sum]
  simp only [toMul_zsmul, e, toMul_ofMul, Subgroup.val_finsetProd, Subgroup.coe_zpow]
  set u : ι → (Skeleton V.Modules)ˣ := fun i => unitOf (hL i)
  have hu : ∀ i, toSkeleton (L i) = (u i).val := fun i => rfl
  simp only [hu, ← Units.val_pow_eq_pow_val, ← Units.coe_prod] at hN
  change toSkeleton N = (∏ i, u i ^ ((a i : ℤ) - b i)).val
  have hN' : toSkeleton N = ((∏ i, u i ^ a i) * (∏ i, u i ^ b i)⁻¹ : (Skeleton V.Modules)ˣ).val := by
    rw [Units.val_mul, ← hN, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [hN']
  congr 1
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_sub, zpow_natCast, zpow_natCast]

end Pic

end P2mSnapperMulti

theorem solution
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (M : V.Modules)
    (hc : (OModulePresheaf.ofModules π M).IsCoherent) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (OModulePresheaf.ofModules π M).SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    {ι : Type*} [Fintype ι] (L : ι → V.Modules) (hL : ∀ i, Scheme.Modules.IsInvertible (L i)) :
    ∃ P : MvPolynomial ι ℚ, P.totalDegree ≤ d ∧
      ∀ (a b : ι → ℕ) (N : V.Modules),
        toSkeleton N * ∏ i, toSkeleton (L i) ^ b i = ∏ i, toSkeleton (L i) ^ a i →
          ((OModulePresheaf.ofModules π (M ⊗ N)).eulerChar K : ℚ) =
            MvPolynomial.eval (fun i => (a i : ℚ) - (b i : ℚ)) P :=
  P2mSnapperMulti.main π K M hc hq Y hY d hd L hL

end

end S_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensor_eq_monoidalV2 (solution)
