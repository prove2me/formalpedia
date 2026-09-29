-- Prove2me | solution 1 for AutomorphicForm.semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/28748d20-f055-5fb4-8f53-7ad68d88343a

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace S1B

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem eq_genuine (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :
    D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L :=
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  Subsingleton.elim D _

theorem genuine_act_apply (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ : RingAut (AdeleRing (𝓞 L) L)) x =
      M4aHerbrand.Bridge.genuineTensorEquiv K L
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : AdeleRing (𝓞 K) K ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 K) K) σ)
          ((M4aHerbrand.Bridge.genuineTensorEquiv K L).symm x)) := by
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act]
  rfl

variable (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalEval_eq (y : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v y =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => y w.1) := rfl

theorem semiLocalEval_genuineβ (a : AdeleRing (𝓞 K) K) :
    AutomorphicForm.semiLocalEval K L v (M4aHerbrand.Bridge.genuineβ K L a).2 = (1 : L) ⊗ₜ[K] (a.2 v) := by
  rw [semiLocalEval_eq, AlgEquiv.symm_apply_eq]
  funext w
  obtain ⟨w₁, hw⟩ := w
  subst hw
  show (M4aHerbrand.Bridge.genuineβ K L a).2 w₁ = HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) _ ((1 : L) ⊗ₜ[K] _) ⟨w₁, rfl⟩
  rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul, M4aHerbrand.Bridge.genuineβ_snd,
    M4aHerbrand.Bridge.finiteConorm_apply]
  rfl

theorem semiLocalEval_algebraMap (ℓ : L) :
    AutomorphicForm.semiLocalEval K L v (algebraMap L (AdeleRing (𝓞 L) L) ℓ).2 = ℓ ⊗ₜ[K] (1 : v.adicCompletion K) := by
  rw [semiLocalEval_eq, AlgEquiv.symm_apply_eq]
  funext w
  show (algebraMap L (AdeleRing (𝓞 L) L) ℓ).2 w.1 = HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v (ℓ ⊗ₜ[K] _) w
  rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, mul_one]
  rfl

theorem clause_a_genuine (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v
        (((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ : RingAut (AdeleRing (𝓞 L) L)) x).2 =
      (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
        (AutomorphicForm.semiLocalEval K L v x.2) := by
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  set te := M4aHerbrand.Bridge.genuineTensorEquiv K L with hte
  set τσ := (Algebra.TensorProduct.congr
      (AlgEquiv.refl : AdeleRing (𝓞 K) K ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 K) K) σ) with hτσ
  set σv := (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)) with hσv
  rw [genuine_act_apply]
  obtain ⟨z, rfl⟩ : ∃ z, x = te z := ⟨te.symm x, (te.apply_symm_apply x).symm⟩
  rw [← hte, ← hτσ, te.symm_apply_apply]

  let fin : AdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L := RingHom.snd _ _
  let F : AdeleRing (𝓞 K) K ⊗[K] L →+* L ⊗[K] v.adicCompletion K :=
    (AutomorphicForm.semiLocalEval K L v).comp (fin.comp (te.toRingEquiv.toRingHom.comp τσ.toRingEquiv.toRingHom))
  let G : AdeleRing (𝓞 K) K ⊗[K] L →+* L ⊗[K] v.adicCompletion K :=
    σv.toRingEquiv.toRingHom.comp ((AutomorphicForm.semiLocalEval K L v).comp (fin.comp te.toRingEquiv.toRingHom))
  have hFa : ∀ a : AdeleRing (𝓞 K) K, F (a ⊗ₜ[K] (1 : L)) = (1 : L) ⊗ₜ[K] (a.2 v) := by
    intro a
    show AutomorphicForm.semiLocalEval K L v (te (τσ (a ⊗ₜ[K] (1 : L)))).2 = _
    rw [hτσ, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    show AutomorphicForm.semiLocalEval K L v (te (a ⊗ₜ[K] σ 1)).2 = _
    rw [map_one, hte, M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one]
    exact semiLocalEval_genuineβ K L v a
  have hFl : ∀ ℓ : L, F ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] ℓ) = (σ ℓ) ⊗ₜ[K] (1 : v.adicCompletion K) := by
    intro ℓ
    show AutomorphicForm.semiLocalEval K L v (te (τσ ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] ℓ))).2 = _
    rw [hτσ, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    show AutomorphicForm.semiLocalEval K L v (te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] σ ℓ)).2 = _
    rw [hte, M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul]
    exact semiLocalEval_algebraMap K L v (σ ℓ)
  have hGa : ∀ a : AdeleRing (𝓞 K) K, G (a ⊗ₜ[K] (1 : L)) = (1 : L) ⊗ₜ[K] (a.2 v) := by
    intro a
    show σv (AutomorphicForm.semiLocalEval K L v (te (a ⊗ₜ[K] (1 : L))).2) = _
    rw [hte, M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one, semiLocalEval_genuineβ, hσv,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    show σ 1 ⊗ₜ[K] (a.2 v) = _
    rw [map_one]
  have hGl : ∀ ℓ : L, G ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] ℓ) = (σ ℓ) ⊗ₜ[K] (1 : v.adicCompletion K) := by
    intro ℓ
    show σv (AutomorphicForm.semiLocalEval K L v (te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] ℓ)).2) = _
    rw [hte, M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul, semiLocalEval_algebraMap, hσv,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have hFG : ∀ z, F z = G z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | tmul a ℓ =>
      have e : a ⊗ₜ[K] ℓ = (a ⊗ₜ[K] (1 : L)) * ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] ℓ) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e, map_mul, map_mul, hFa, hFl, hGa, hGl]
  exact hFG z

theorem clause_a (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) x).2 =
      (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
        (AutomorphicForm.semiLocalEval K L v x.2) := by
  rw [eq_genuine K L D]
  exact clause_a_genuine K L v σ x

end S1B

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) :
    (∀ x : AdeleRing (𝓞 L) L,
      AutomorphicForm.semiLocalEval K L v ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) x).2 =
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
          (AutomorphicForm.semiLocalEval K L v x.2)) ∧
    (∀ t : (AdeleRing (𝓞 L) L)ˣ,
      ((AutomorphicForm.TransversalMeasure.semiLocalIdele K L v (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t) :
          (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) =
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
          ((AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t : (L ⊗[K] v.adicCompletion K)ˣ) :
            L ⊗[K] v.adicCompletion K)) ∧
    (∀ (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (i j : Fin 2),
      ((AutomorphicForm.semiLocalComponent K L v
          (NumberField.AdelicLevel.glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
          (((AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L g) :
            GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j)) := by
  refine ⟨fun x => S1B.clause_a K L v D σ x, fun t => ?_, fun g i j => ?_⟩
  · exact S1B.clause_a K L v D σ (t : AdeleRing (𝓞 L) L)
  · exact S1B.clause_a K L v D σ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j)

end S_AutomorphicForm_semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
end P2MW
export P2MW.S_AutomorphicForm_semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct (solution)
