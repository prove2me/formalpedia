-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:51:44.510495+00:00
-- url     : https://prove2.me/theorems/a05a6e4c-5897-432c-b34d-db0c3eaae713
-- title:
--   PSurj A
-- statement:
--   Definitions and structural lemmas for PSurj A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjA.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Fam
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : Type} [Fintype n]
  [DecidableEq n]
theorem fam_mul (e : ι → R) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (A B : ι → Matrix n n R) :
    (∑ i, e i • A i) * (∑ j, e j • B j) = ∑ i, e i • (A i * B i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he i, ite_smul, zero_smul]
  simp
theorem fam_one (e : ι → R) (hs : ∑ i, e i = 1) (X : Matrix n n R) : ∑ i, e i • X = X := by
  rw [← Finset.sum_smul, hs, one_smul]
theorem cT_fam (s : R →+* R) (e : ι → R) (A : ι → Matrix n n R) :
    cT s (∑ i, e i • A i) = ∑ i, s (e i) • cT s (A i) := by
  ext a c
  simp [cT, Matrix.sum_apply, map_sum, Matrix.smul_apply, map_mul]
end Fam
section Patch
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (F E) in

abbrev finE : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
def incM (U : GL (Fin M) E) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  (U : Matrix (Fin M) (Fin M) E).map (inclR (AF F))
theorem incM_mul_inv (U : GL (Fin M) E) : incM (F := F) U * incM (F := F) U⁻¹ = 1 := by
  unfold incM
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem incM_inv_mul (U : GL (Fin M) E) : incM (F := F) U⁻¹ * incM (F := F) U = 1 := by
  unfold incM
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem incM_unitary (U : GL (Fin M) E) (hU : U ∈ UJ (σ : E →+* E) J) :
    cT (sigR (AF F) σ) (incM (F := F) U) * JR (AF F) J * incM (F := F) U = JR (AF F) J := by
  have := PI.UnitaryGroupMassFormula.UJClassFin.bc_mem (F := F) σ J U hU
  exact this
def patchGL (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (γ : ι → GL (Fin M) E) : GL (Fin M) (AF F ⊗[F] E) where
  val := ∑ i, e i • incM (γ i)
  inv := ∑ i, e i • incM (γ i)⁻¹
  val_inv := by
    rw [fam_mul e he]
    simp_rw [incM_mul_inv]
    exact fam_one e hs 1
  inv_val := by
    rw [fam_mul e he]
    simp_rw [incM_inv_mul]
    exact fam_one e hs 1
theorem patchGL_mem (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) : patchGL e he hs γ ∈ HR (AF F) σ J := by
  show cT (sigR (AF F) σ) (∑ i, e i • incM (γ i)) * JR (AF F) J * (∑ i, e i • incM (γ i)) = JR (AF F) J
  rw [cT_fam]
  simp_rw [hσe]
  conv_lhs => rw [← fam_one e hs (JR (AF F) J)]
  rw [fam_mul e he, fam_mul e he]
  simp_rw [incM_unitary σ J _ (hγ _)]
  exact fam_one e hs _
def patchHA (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) : HA (AF F) σ J :=
  (⟨patchGL e he hs γ, patchGL_mem σ J e he hs hσe γ hγ⟩ : HR (AF F) σ J)
end Patch
section Split
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Split
end PI.UnitaryGroupMassFormula.UJClassMass
end


