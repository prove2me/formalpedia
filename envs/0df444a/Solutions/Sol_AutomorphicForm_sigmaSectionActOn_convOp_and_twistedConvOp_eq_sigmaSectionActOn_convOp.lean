-- Prove2me | solution 1 for AutomorphicForm.sigmaSectionActOn_convOp_and_twistedConvOp_eq_sigmaSectionActOn_convOp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0ea76971-9715-504f-ac8c-872cc82045b3

import Mathlib
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_measurePreserving_sigmaAdelicAct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sigmaSectionActOn_convOp_and_twistedConvOp_eq_sigmaSectionActOn_convOp
p2m_attr_erase "simp" "FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm

noncomputable section

namespace R4KitOperator

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem sigmaAdelicAct_inv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) : sigmaAdelicAct K L D σ (sigmaAdelicAct K L D σ⁻¹ g) = g := by
  rw [← MonoidHom.comp_apply, ← sigmaAdelicAct_mul, mul_inv_cancel, sigmaAdelicAct_one]; rfl

theorem sigmaAdelicAct_apply_inv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) : sigmaAdelicAct K L D σ⁻¹ (sigmaAdelicAct K L D σ g) = g := by
  rw [← MonoidHom.comp_apply, ← sigmaAdelicAct_mul, inv_mul_cancel, sigmaAdelicAct_one]; rfl

def sigmaHomeo (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdelicGL2 (𝓞 L) L ≃ₜ AdelicGL2 (𝓞 L) L where
  toFun := sigmaAdelicAct K L D σ
  invFun := sigmaAdelicAct K L D σ⁻¹
  left_inv := sigmaAdelicAct_apply_inv D σ
  right_inv := sigmaAdelicAct_inv_apply D σ
  continuous_toFun := continuous_sigmaAdelicAct K L D σ
  continuous_invFun := continuous_sigmaAdelicAct K L D σ⁻¹

theorem integral_comp_sigmaAdelicAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (F : AdelicGL2 (𝓞 L) L → ℂ) :
    ∫ x, F (sigmaAdelicAct K L D σ x) ∂adelicGLHaar (Fin 2) (𝓞 L) L = ∫ y, F y ∂adelicGLHaar (Fin 2) (𝓞 L) L := by
  have hmp : MeasurePreserving (sigmaHomeo D σ).toMeasurableEquiv (adelicGLHaar (Fin 2) (𝓞 L) L)
      (adelicGLHaar (Fin 2) (𝓞 L) L) := AutomorphicForm.measurePreserving_sigmaAdelicAct K L D σ
  exact hmp.integral_comp' F

theorem sigmaSectionActOn_convOp (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (f u : AdelicGL2 (𝓞 L) L → ℂ) :
    sigmaSectionActOn K L D σ (convOp L f u) =
      convOp L (sigmaSectionActOn K L D σ f) (sigmaSectionActOn K L D σ u) := by
  funext g
  show rightConv L u f (sigmaAdelicAct K L D σ g) =
    rightConv L (fun x => u (sigmaAdelicAct K L D σ x)) (fun x => f (sigmaAdelicAct K L D σ x)) g
  rw [rightConv_apply, rightConv_apply]
  show ∫ x, u (sigmaAdelicAct K L D σ g * x) * f x ∂adelicGLHaar (Fin 2) (𝓞 L) L =
    ∫ x, u (sigmaAdelicAct K L D σ (g * x)) * f (sigmaAdelicAct K L D σ x) ∂adelicGLHaar (Fin 2) (𝓞 L) L
  simp_rw [map_mul]
  exact (integral_comp_sigmaAdelicAct D σ (fun y => u (sigmaAdelicAct K L D σ g * y) * f y)).symm

theorem twistedConvOp_eq (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (f u : AdelicGL2 (𝓞 L) L → ℂ) :
    twistedConvOp K L D σ f u =
      sigmaSectionActOn K L D σ (convOp L (sigmaSectionActOn K L D σ⁻¹ f) u) := by
  rw [sigmaSectionActOn_convOp, twistedConvOp_apply, ← convOp_apply]
  congr 1
  funext x
  show f x = f (sigmaAdelicAct K L D σ⁻¹ (sigmaAdelicAct K L D σ x))
  rw [sigmaAdelicAct_apply_inv]

end R4KitOperator

end

open R4KitOperator in

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (f u : AdelicGL2 (𝓞 L) L → ℂ) :
    sigmaSectionActOn K L D σ (convOp L f u) =
      convOp L (sigmaSectionActOn K L D σ f) (sigmaSectionActOn K L D σ u) ∧
    twistedConvOp K L D σ f u =
      sigmaSectionActOn K L D σ (convOp L (sigmaSectionActOn K L D σ⁻¹ f) u) :=
  ⟨sigmaSectionActOn_convOp D σ f u, twistedConvOp_eq D σ f u⟩

end S_AutomorphicForm_sigmaSectionActOn_convOp_and_twistedConvOp_eq_sigmaSectionActOn_convOp
end P2MW
export P2MW.S_AutomorphicForm_sigmaSectionActOn_convOp_and_twistedConvOp_eq_sigmaSectionActOn_convOp (solution)
