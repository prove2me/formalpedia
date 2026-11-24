-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:13:08.998827+00:00
-- url     : https://prove2.me/theorems/e4d0d772-0049-404e-b9da-412d4b50d052
-- title:
--   Lift Mat Map Same
-- statement:
--   Definitions and structural lemmas for Lift Mat Map Same, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LiftMatMapSame.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
def liftMat (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
    Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  fun i j => PI.FinKW.liftOne I v (g i j) + if i = j then 1 - PI.FinKW.liftOne I v 1 else 0
theorem evalV_singleV_self' {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v c) = c := by
  classical
  first
  | (simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV, AlgHom.coe_mk]
     done)
  | (unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV
     simp only [AlgHom.coe_mk, RestrictedProduct.evalRingHom_apply, RestrictedProduct.single_eq_same]
     done)
  | (change (RestrictedProduct.evalRingHom (fun w => HeightOneSpectrum.adicCompletion F w) v)
      (RestrictedProduct.single (fun w => HeightOneSpectrum.adicCompletionIntegers F w) v c) = c
     simp
     done)
  | (change (RestrictedProduct.single (fun w => HeightOneSpectrum.adicCompletionIntegers F w) v c) v = c
     simp
     done)
  | (change (RestrictedProduct.single (fun w => HeightOneSpectrum.adicCompletionIntegers F w) v c) v = c
     exact RestrictedProduct.single_eq_same _ v c)
  | (change (RestrictedProduct.single (fun w => HeightOneSpectrum.adicCompletionIntegers F w) v c) v = c
     rfl)
theorem evalV_singleV_of_ne {F : Type} [Field F] [NumberField F]
    {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v c) = 0 := by
  classical
  first
  | (simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV, AlgHom.coe_mk, hw]
     done)
  | (unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV
     simp only [AlgHom.coe_mk, RestrictedProduct.evalRingHom_apply, RestrictedProduct.single_eq_of_ne _ _ hw]
     done)
  | (change (RestrictedProduct.evalRingHom (fun u => HeightOneSpectrum.adicCompletion F u) w)
      (RestrictedProduct.single (fun u => HeightOneSpectrum.adicCompletionIntegers F u) v c) = 0
     simp [hw]
     done)
  | (change (RestrictedProduct.single (fun u => HeightOneSpectrum.adicCompletionIntegers F u) v c) w = 0
     simp [hw]
     done)
  | (change (RestrictedProduct.single (fun u => HeightOneSpectrum.adicCompletionIntegers F u) v c) w = 0
     exact RestrictedProduct.single_eq_of_ne _ c hw)
  | (change (RestrictedProduct.single (fun u => HeightOneSpectrum.adicCompletionIntegers F u) v c) w = 0
     exact Pi.single_eq_of_ne hw c)
theorem psiV_liftOne_self (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    PI.FinKW.psiV I v (PI.FinKW.liftOne I v y) = y := by
  classical
  have hy := LinearEquiv.symm_apply_apply (TensorProduct.equivFinsuppOfBasisRight
    (M := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Module.Basis.ofVectorSpace I.F I.E)) y
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply] at hy
  conv_rhs => rw [← hy]
  unfold PI.FinKW.liftOne
  simp only [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [PI.FinKW.psiV, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom,
    Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, evalV_singleV_self', AlgHom.coe_id, id_eq,
    TensorProduct.zero_tmul]
theorem psiV_liftOne_of_ne (I : AutInst) {v w : HeightOneSpectrum (𝓞 I.F)} (hw : w ≠ v)
    (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    PI.FinKW.psiV I w (PI.FinKW.liftOne I v y) = 0 := by
  classical
  unfold PI.FinKW.liftOne
  simp only [Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp only [PI.FinKW.psiV, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom,
    Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, evalV_singleV_of_ne hw, AlgHom.coe_id, id_eq,
    TensorProduct.zero_tmul]
theorem liftMat_map_same (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
    (liftMat I v g).map (PI.FinKW.psiV I v).toRingHom = g := by
  ext i j
  have h1 := fun a => psiV_liftOne_self I v a
  have h2 := psiV_liftOne_self I v 1
  simp only [Matrix.map_apply, liftMat, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add]
  split_ifs with h <;> simp [h1, h2]
theorem liftMat_map_ne (I : AutInst) {v w : HeightOneSpectrum (𝓞 I.F)} (hw : w ≠ v)
    (g : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
    (liftMat I v g).map (PI.FinKW.psiV I w).toRingHom = 1 := by
  ext i j
  have h1 := fun a => psiV_liftOne_of_ne I hw a
  have h2 := psiV_liftOne_of_ne I hw 1
  simp only [Matrix.map_apply, liftMat, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add]
  split_ifs with h <;> simp [h1, h2, h, Matrix.one_apply]
theorem equivFinsuppOfBasisRight_psiV_eq_evalV (I : AutInst) (w : HeightOneSpectrum (𝓞 I.F))
    [DecidableEq (Module.Basis.ofVectorSpaceIndex I.F I.E)]
    (x : I.E ⊗[I.F] Af I.F) (i : Module.Basis.ofVectorSpaceIndex I.F I.E) :
    TensorProduct.equivFinsuppOfBasisRight (Module.Basis.ofVectorSpace I.F I.E)
        (PI.FinKW.psiV I w x) i =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F w
        (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E) x i) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp only [PI.FinKW.psiV, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
      AlgEquiv.coe_algHom, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]
    first
    | exact (map_smul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F w) _ a).symm
    | exact (AlgHom.map_smul_of_tower (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F w) _ a).symm
    | simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
theorem eq_of_forall_psiV_eq (I : AutInst) {x y : I.E ⊗[I.F] Af I.F}
    (h : ∀ w, PI.FinKW.psiV I w x = PI.FinKW.psiV I w y) : x = y := by
  classical
  apply (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E)).injective
  refine Finsupp.ext fun i => ?_
  have key : ∀ w, TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E) x i w =
      TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E) y i w := by
    intro w
    have hw := equivFinsuppOfBasisRight_psiV_eq_evalV I w x i
    rw [h w, equivFinsuppOfBasisRight_psiV_eq_evalV] at hw
    exact hw.symm
  first
  | exact RestrictedProduct.ext key
  | exact Subtype.ext (funext key)
theorem liftMat_mul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g h : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
    liftMat I v g * liftMat I v h = liftMat I v (g * h) := by
  ext i j
  apply eq_of_forall_psiV_eq I
  intro w
  have e1 : ((liftMat I v g * liftMat I v h).map (PI.FinKW.psiV I w).toRingHom) i j =
      ((liftMat I v (g * h)).map (PI.FinKW.psiV I w).toRingHom) i j := by
    rw [Matrix.map_mul]
    by_cases hw : w = v
    · subst hw
      rw [liftMat_map_same, liftMat_map_same, liftMat_map_same]
    · rw [liftMat_map_ne I hw, liftMat_map_ne I hw, liftMat_map_ne I hw, one_mul]
  simpa using e1
theorem liftMat_one (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    liftMat I v 1 = 1 := by
  ext i j
  apply eq_of_forall_psiV_eq I
  intro w
  have e1 : ((liftMat I v 1).map (PI.FinKW.psiV I w).toRingHom) i j =
      ((1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)).map (PI.FinKW.psiV I w).toRingHom) i j := by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    by_cases hw : w = v
    · subst hw
      rw [liftMat_map_same]
    · rw [liftMat_map_ne I hw]
  simpa using e1
def liftGL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  ⟨liftMat I v g.val, liftMat I v g⁻¹.val,
    by rw [liftMat_mul, Units.mul_inv, liftMat_one],
    by rw [liftMat_mul, Units.inv_mul, liftMat_one]⟩
end PI.UnitaryGroupMassFormula.AdIndexEq
end


