-- Prove2me | solution 1 for AutomorphicForm.isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/aa59d79f-9859-5656-9e91-a52d4b95e6fc

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom) u))
      (AutomorphicForm.tensorPlace K L v δ) := by
  refine ⟨1, ?_⟩
  show AutomorphicForm.toTensorGL K L (v.adicCompletion K) _ =
    1⁻¹ * AutomorphicForm.normString K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ) * 1
  rw [inv_one, one_mul, mul_one]

  have hns : AutomorphicForm.normString K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ) =
      AutomorphicForm.tensorPlace K L v (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ) := by
    unfold AutomorphicForm.normString
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    show ((⇑(AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ))^[i]) (AutomorphicForm.tensorPlace K L v δ) =
      AutomorphicForm.tensorPlace K L v (((⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i]) δ)
    exact (Function.Semiconj.iterate_right
      (f := ⇑(AutomorphicForm.tensorPlace K L v))
      (ga := ⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))
      (gb := ⇑(AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ))
      (fun x => AutomorphicForm.tensorPlace_sigmaGL K L σ v x) i δ).symm

  have hsc : AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((AutomorphicForm.adelePlaceAlgHom K v).toRingHom.toMonoidHom) u) := by
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [AdelicLevel.finComponent, AdelicLevel.glFin, AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.scalar,
        AdelicLevel.finAdeleEval, AdelicLevel.adeleFin]
    · simp [AdelicLevel.finComponent, AdelicLevel.glFin, AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.scalar,
        AdelicLevel.finAdeleEval, AdelicLevel.adeleFin, hij]
      rfl
  rw [hns, hN, AutomorphicForm.tensorPlace_toTensorGL, hsc]

#print axioms solution

end S_AutomorphicForm_isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar
end P2MW
export P2MW.S_AutomorphicForm_isNormOf_scalar_tensorPlace_of_normString_eq_toTensorGL_centralScalar (solution)
