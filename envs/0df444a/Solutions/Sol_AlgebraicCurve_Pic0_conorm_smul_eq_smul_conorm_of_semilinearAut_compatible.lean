-- Prove2me | solution 1 for AlgebraicCurve.Pic0.conorm_smul_eq_smul_conorm_of_semilinearAut_compatible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0031b64e-b4f5-59c1-bea3-6315c036b4dd

import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

theorem solution
    {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F'] [Algebra F F']
    (ι : Pic0 K F →+ Pic0 K' F')
    (hpin : ∀ (D : Divisor.degZero (K := K) (F := F)) (D' : Divisor.degZero (K := K') (F := F')),
      (∀ (v' : Place K' F') (v : Place K F),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          (D' : Divisor K' F') v' = (D : Divisor K F) v) →
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          (D' : Divisor K' F') v' = 0) →
      ι (Pic0.mk D) = Pic0.mk D')
    (hex : ∀ D : Divisor.degZero (K := K) (F := F), ∃ D' : Divisor.degZero (K := K') (F := F'),
      (∀ (v' : Place K' F') (v : Place K F),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          (D' : Divisor K' F') v' = (D : Divisor K F) v) ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          (D' : Divisor K' F') v' = 0))
    (σ : SemilinearAut K F) (σ' : SemilinearAut K' F')
    (hcompat : ∀ f : F, σ' • algebraMap F F' f = algebraMap F F' (σ • f)) :
    ∀ x : Pic0 K F, ι (σ • x) = σ' • ι x := by

  have hcompat' : ∀ f : F, σ'⁻¹ • algebraMap F F' f = algebraMap F F' (σ⁻¹ • f) := by
    intro f
    rw [inv_smul_eq_iff, hcompat, smul_inv_smul]

  have hcomap : ∀ (τ : SemilinearAut K F) (τ' : SemilinearAut K' F'),
      (∀ f : F, τ'⁻¹ • algebraMap F F' f = algebraMap F F' (τ⁻¹ • f)) →
      ∀ v' : Place K' F',
        (τ' • v').toValuationSubring.comap (algebraMap F F') =
          τ • (v'.toValuationSubring.comap (algebraMap F F')) := by
    intro τ τ' h v'
    ext f
    rw [ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap, h]
  have hσ := hcomap σ σ' hcompat'
  have hσinv : ∀ v' : Place K' F',
      (σ'⁻¹ • v').toValuationSubring.comap (algebraMap F F') =
        σ⁻¹ • (v'.toValuationSubring.comap (algebraMap F F')) := by
    refine hcomap σ⁻¹ σ'⁻¹ (fun f => ?_)
    rw [inv_inv, inv_inv, hcompat]
  intro x
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨D', hD'1, hD'2⟩ := hex D
  have e1 : ι (Pic0.mk D) = Pic0.mk D' := hpin D D' hD'1 hD'2
  rw [SemilinearAut.pic0_smul_mk, e1, SemilinearAut.pic0_smul_mk]
  refine hpin (SemilinearAut.degZeroSMulHom σ D) (SemilinearAut.degZeroSMulHom σ' D') ?_ ?_
  · intro w' w hw
    rw [SemilinearAut.coe_degZeroSMulHom, SemilinearAut.coe_degZeroSMulHom,
      SemilinearAut.divisor_smul_apply, SemilinearAut.divisor_smul_apply]
    apply hD'1
    rw [hσinv, hw, ← SemilinearAut.smul_toValuationSubring]
  · intro w' hw'
    rw [SemilinearAut.coe_degZeroSMulHom, SemilinearAut.divisor_smul_apply]
    apply hD'2
    intro v hv
    apply hw' (σ • v)
    have h2 : w' = σ' • (σ'⁻¹ • w') := (smul_inv_smul σ' w').symm
    rw [h2, hσ, hv, SemilinearAut.smul_toValuationSubring]

end S_AlgebraicCurve_Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible (solution)
