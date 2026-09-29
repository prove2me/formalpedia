-- Prove2me | solution 1 for AutomorphicForm.exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d08c0d0a-7289-5915-95db-430e6cbc8d6d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

namespace K42GP

open NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))

noncomputable abbrev piRE : Matrix (Fin 2) (Fin 2) ((v : InfinitePlace K) → L ⊗[K] v.Completion) ≃+*
    ((v : InfinitePlace K) → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) :=
  Matrix.piRingEquiv

noncomputable def theta :
    GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :=
  ((Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) Ξ).toMulEquiv).trans
    (Units.mapEquiv (piRE K L).toMulEquiv)).trans MulEquiv.piUnits

omit [NumberField K] [NumberField L] in
theorem theta_val (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K) (i j : Fin 2) :
    ((theta K L Ξ g v : GL (Fin 2) (L ⊗[K] v.Completion)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) i j =
      Ξ ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j) v :=
  rfl

omit [NumberField K] [NumberField L] in
theorem theta_apply (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K) :
    theta K L Ξ g v = Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g :=
  Units.ext (Matrix.ext fun i j => by rw [theta_val]; rfl)

omit [NumberField K] [NumberField L] in
theorem theta_symm_apply (F : (v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :
    (theta K L Ξ).symm F = (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) Ξ).toMulEquiv).symm
      ((Units.mapEquiv (piRE K L).toMulEquiv).symm (MulEquiv.piUnits.symm F)) :=
  rfl

theorem continuous_theta (hΞ : Continuous Ξ) : Continuous (theta K L Ξ) := by
  refine continuous_pi fun v => ?_
  have hfun : (fun g => theta K L Ξ g v) = Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) :=
    funext fun g => theta_apply K L Ξ g v
  rw [hfun]
  exact Continuous.units_map _ (continuous_id.matrix_map ((continuous_apply v).comp hΞ))

theorem continuous_theta_symm (hΞ' : Continuous Ξ.symm) : Continuous (theta K L Ξ).symm := by
  have h1 : Continuous (MulEquiv.piUnits (M := fun v : InfinitePlace K => Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion))).symm := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact continuous_pi fun v => Units.continuous_val.comp (continuous_apply v)
    · exact continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v)
  have h2 : Continuous (Units.mapEquiv (piRE K L).toMulEquiv).symm := by
    refine Continuous.units_map _ ?_
    refine continuous_matrix fun i j => continuous_pi fun v => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply v)))
  have h3 : Continuous (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) Ξ).toMulEquiv).symm :=
    Continuous.units_map _ (continuous_id.matrix_map hΞ')
  have hfun : ⇑(theta K L Ξ).symm = fun F => (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) Ξ).toMulEquiv).symm
      ((Units.mapEquiv (piRE K L).toMulEquiv).symm (MulEquiv.piUnits.symm F)) :=
    funext fun F => theta_symm_apply K L Ξ F
  rw [hfun]
  exact h3.comp (h2.comp h1)

omit [NumberField K] [NumberField L] in
theorem sigmaTensor_tmul (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (x : L) (a : A) :
    sigmaTensor K L A σ (x ⊗ₜ[K] a) = σ x ⊗ₜ[K] a := by
  show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)) (x ⊗ₜ a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

omit [NumberField K] [NumberField L] in
theorem sigma_comm (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v))
    (σ : L ≃ₐ[K] L) (v : InfinitePlace K) (z : L ⊗[K] InfiniteAdeleRing K) :
    Ξ (sigmaTensor K L (InfiniteAdeleRing K) σ z) v = sigmaTensor K L v.Completion σ (Ξ z v) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [(sigmaTensor K L (InfiniteAdeleRing K) σ).map_zero, RingEquiv.map_zero, Pi.zero_apply,
      (sigmaTensor K L v.Completion σ).map_zero]
  | tmul x a => rw [sigmaTensor_tmul, hΞt, hΞt, sigmaTensor_tmul]
  | add z w hz hw =>
    rw [(sigmaTensor K L (InfiniteAdeleRing K) σ).map_add, RingEquiv.map_add, Pi.add_apply, hz, hw,
      RingEquiv.map_add, Pi.add_apply, (sigmaTensor K L v.Completion σ).map_add]

end K42GP

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
    (hΞ : Continuous Ξ) (hΞ' : Continuous Ξ.symm)
    (hΞt : ∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v)) :
    ∃ Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)),
      Continuous Θ ∧ Continuous Θ.symm ∧
      (∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ g v = Matrix.GeneralLinearGroup.map
          ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g) ∧
      (∀ (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v)) ∧
      (∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (toTensorGL K L (InfiniteAdeleRing K) g) v =
          toTensorGL K L v.Completion
            (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) v) g)) := by
  refine ⟨K42GP.theta K L Ξ, K42GP.continuous_theta K L Ξ hΞ, K42GP.continuous_theta_symm K L Ξ hΞ',
    K42GP.theta_apply K L Ξ, ?_, ?_⟩
  · intro σ g v
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [K42GP.theta_val]
    show Ξ (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ
        ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j)) v =
      AutomorphicForm.sigmaTensor K L v.Completion σ
        (((K42GP.theta K L Ξ g v : GL (Fin 2) (L ⊗[K] v.Completion)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.Completion)) i j)
    rw [K42GP.theta_val]
    exact K42GP.sigma_comm K L Ξ hΞt σ v _
  · intro g v
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [K42GP.theta_val]
    show Ξ ((1 : L) ⊗ₜ[K] ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j)) v =
      (1 : L) ⊗ₜ[K] ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j v)
    rw [hΞt]

end S_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi
end P2MW
export P2MW.S_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi (solution)
