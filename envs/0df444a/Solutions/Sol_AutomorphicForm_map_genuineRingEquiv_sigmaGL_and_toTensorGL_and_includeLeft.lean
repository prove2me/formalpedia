-- Prove2me | solution 1 for AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a1bf8267-9959-5501-bca8-8c7e153b6bfd

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

namespace R2FafCuTS

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev e : (L ⊗[K] AdeleRing (𝓞 K) K) ≃+* AdeleRing (𝓞 L) L :=
  ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L))

theorem e_tmul (l : L) (a : AdeleRing (𝓞 K) K) :
    e K L (l ⊗ₜ a) = M4aHerbrand.Bridge.genuineRingEquiv K L (a ⊗ₜ l) := rfl

theorem e_one_tmul (a : AdeleRing (𝓞 K) K) :
    e K L (1 ⊗ₜ a) = M4aHerbrand.Bridge.genuineβ K L a := by
  rw [e_tmul, M4aHerbrand.Bridge.genuineRingEquiv_tmul_one]

theorem e_tmul_one (l : L) :
    e K L (l ⊗ₜ 1) = algebraMap L (AdeleRing (𝓞 L) L) l := by
  rw [e_tmul, M4aHerbrand.Bridge.genuineRingEquiv_one_tmul]

theorem genuineDescentDatum_act_e (τ : L ≃ₐ[K] L) (x : L ⊗[K] AdeleRing (𝓞 K) K) :
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act τ (e K L x) =
      e K L (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) τ x) := by
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act]
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra

  induction x using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul l a =>
      show M4aHerbrand.Bridge.genuineTensorEquiv K L
          ((Algebra.TensorProduct.congr AlgEquiv.refl τ)
            ((M4aHerbrand.Bridge.genuineTensorEquiv K L).symm
              (M4aHerbrand.Bridge.genuineRingEquiv K L (a ⊗ₜ l)))) =
        M4aHerbrand.Bridge.genuineRingEquiv K L
          ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K))
            (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) τ (l ⊗ₜ a)))
      have h1 : M4aHerbrand.Bridge.genuineRingEquiv K L (a ⊗ₜ l) =
          M4aHerbrand.Bridge.genuineTensorEquiv K L (a ⊗ₜ l) := rfl
      rw [h1, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul]
      rfl
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, map_add]

theorem map_e_sigmaGL (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L)
    (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (e K L).toRingHom
        (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) τ g) =
      AutomorphicForm.sigmaAdelicAct K L D τ (Matrix.GeneralLinearGroup.map (e K L).toRingHom g) := by
  have hD : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L :=
    haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
    Subsingleton.elim _ _
  subst hD
  ext i j
  show e K L (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) τ (g.val i j)) =
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act τ (e K L (g.val i j))
  rw [genuineDescentDatum_act_e]

theorem map_e_toTensorGL (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Matrix.GeneralLinearGroup.map (e K L).toRingHom (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) g) =
      Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β g := by
  ext i j
  exact e_one_tmul K L (g.val i j)

theorem map_e_toTensorGL_globalPoints (γ : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.map (e K L).toRingHom
        (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ)) =
      AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (algebraMap K L) γ) := by
  rw [map_e_toTensorGL]
  ext i j
  exact M4aHerbrand.Bridge.genuineβ_compat K L (γ.val i j)

theorem map_e_includeLeft (δ : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.map (e K L).toRingHom
        (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ) =
      AutomorphicForm.globalPoints (𝓞 L) L δ := by
  ext i j
  exact e_tmul_one K L (δ.val i j)

end R2FafCuTS

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :
    (∀ (τ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
          (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) τ g) =
        AutomorphicForm.sigmaAdelicAct K L D τ
          (Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) g)) ∧
    (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
          (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) g) =
        Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β g) ∧
    (∀ δ : GL (Fin 2) L,
      Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ) =
        AutomorphicForm.globalPoints (𝓞 L) L δ) := by
  refine ⟨fun τ g => ?_, fun g => ?_, fun δ => ?_⟩
  · exact R2FafCuTS.map_e_sigmaGL K L D τ g
  · exact R2FafCuTS.map_e_toTensorGL K L g
  · exact R2FafCuTS.map_e_includeLeft K L δ

end S_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
end P2MW
export P2MW.S_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft (solution)
