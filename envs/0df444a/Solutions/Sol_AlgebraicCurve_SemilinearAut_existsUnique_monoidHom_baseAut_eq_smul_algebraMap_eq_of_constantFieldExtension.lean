-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/99f13fb7-8110-59fd-b968-9ce165106139

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_SemilinearAut_existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension

open AlgebraicCurve

set_option autoImplicit false

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (S : Type*) [Group S] (galF : S →* SemilinearAut K F) (τ : S →* (K' ≃+* K'))
    (hτ : ∀ (σ : S) (a : K), τ σ (algebraMap K K' a) = algebraMap K K' (SemilinearAut.baseAut (galF σ) a)) :
    ∃! galF' : S →* SemilinearAut K' F',
      (∀ (σ : S) (c : K'), SemilinearAut.baseAut (galF' σ) c = τ σ c) ∧
      ∀ (σ : S) (y : F), galF' σ • algebraMap F F' y = algebraMap F F' (galF σ • y) := by
  classical

  have H : ∀ σ : S, ∃! g' : SemilinearAut K' F',
      (∀ c : K', SemilinearAut.baseAut g' c = τ σ c) ∧
      ∀ y : F, g' • algebraMap F F' y = algebraMap F F' (galF σ • y) := fun σ =>
    AlgebraicCurve.SemilinearAut.existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen (galF σ) (τ σ) (hτ σ)
  let f : S → SemilinearAut K' F' := fun σ => (H σ).exists.choose
  have hf : ∀ σ, (∀ c : K', SemilinearAut.baseAut (f σ) c = τ σ c) ∧
      ∀ y : F, f σ • algebraMap F F' y = algebraMap F F' (galF σ • y) := fun σ => (H σ).exists.choose_spec

  have h1 : f 1 = 1 := (H 1).unique (hf 1) ⟨fun c => by simp, fun y => by simp⟩
  have hmul : ∀ σ σ' : S, f (σ * σ') = f σ * f σ' := fun σ σ' =>
    (H (σ * σ')).unique (hf (σ * σ'))
      ⟨fun c => by
        rw [SemilinearAut.baseAut_mul, map_mul, RingAut.mul_apply, RingAut.mul_apply, (hf σ').1, (hf σ).1],
       fun y => by
        rw [mul_smul, (hf σ').2, (hf σ).2, map_mul, mul_smul]⟩
  let galF' : S →* SemilinearAut K' F' := { toFun := f, map_one' := h1, map_mul' := hmul }
  refine ⟨galF', ⟨fun σ c => (hf σ).1 c, fun σ y => (hf σ).2 y⟩, ?_⟩
  rintro G ⟨hGb, hGF⟩
  ext σ : 1
  exact (H σ).unique ⟨hGb σ, hGF σ⟩ (hf σ)

end S_AlgebraicCurve_SemilinearAut_existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_existsUnique_monoidHom_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension (solution)
