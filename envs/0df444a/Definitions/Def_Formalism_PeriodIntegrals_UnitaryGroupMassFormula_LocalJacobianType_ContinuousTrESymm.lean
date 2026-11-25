-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:32.131478+00:00
-- url     : https://prove2.me/theorems/d5a11392-a717-48dd-8cca-2d73e498e1a8
-- title:
--   Continuous Tr ESymm
-- statement:
--   Definitions and structural lemmas for Continuous Tr ESymm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ContinuousTrESymm.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
theorem finDim (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
attribute [local instance] finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
theorem oev_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := Submodule.zero_mem _
theorem oev_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := Submodule.add_mem _ hx hy
theorem oev_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v :=
  Submodule.neg_mem _ hx
def Osub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  add_mem' := oev_add v
  zero_mem' := oev_zero v
  neg_mem' := oev_neg v
theorem exists_intBasis : ∃ b : Module.Basis (Fin (Module.finrank F E)) F E,
    ∀ i, IsIntegral ℤ (b i) := by
  classical
  let b0 := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b0)
  have hu : ∀ i : Fin (Module.finrank F E), IsUnit ((y : F)) := fun _ =>
    isUnit_iff_ne_zero.2 (by exact_mod_cast hy0)
  refine ⟨b0.isUnitSMul hu, fun i => ?_⟩
  have h := hy (b0 i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [Module.Basis.isUnitSMul_apply]
  have e : ((y : F)) • b0 i = y • b0 i := by
    rw [← Int.cast_smul_eq_zsmul F y (b0 i)]
  rw [e]
  exact h
theorem trace_inclR (x : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      algebraMap F (Fv F v) (Algebra.trace F E x) := by
  have e : Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      (Algebra.lmul F E x).baseChange (Fv F v) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext a e
    simp [inclR]
  rw [Algebra.trace_apply, e, LinearMap.trace_baseChange]
  rfl
def ib : Module.Basis (Fin (Module.finrank F E)) F E := (exists_intBasis (F := F) (E := E)).choose
def bas : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (ib (F := F) (E := E))
theorem bas_apply (i : Fin (Module.finrank F E)) :
    bas (E := E) v i = inclR (F := F) (Fv F v) (ib (F := F) (E := E) i) := by
  simp [bas, Algebra.TensorProduct.basis_apply, inclR]
def trC : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin (Module.finrank F E) → Fv F v) where
  toFun y i := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (bas (E := E) v i * y)
  map_add' x y := by funext i; simp [mul_add, map_add]
  map_smul' c x := by funext i; simp [map_smul]
theorem trC_apply (y : Fv F v ⊗[F] E) (i : Fin (Module.finrank F E)) :
    trC (E := E) v y i = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (bas (E := E) v i * y) := rfl
theorem trC_injective : Function.Injective (trC (E := E) v) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  set c := (bas (E := E) v).equivFun y with hc
  set M : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) (Fv F v) :=
    (algebraMap F (Fv F v)).mapMatrix (Algebra.traceMatrix F (ib (F := F) (E := E))) with hM
  have hmv : M.mulVec c = 0 := by
    funext i
    have h1 := congrFun hy i
    rw [trC_apply, ← (bas (E := E) v).sum_equivFun y, Finset.mul_sum] at h1
    simp only [mul_smul_comm, map_sum, map_smul, smul_eq_mul] at h1
    rw [Pi.zero_apply] at h1
    rw [Pi.zero_apply, ← h1, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bas_apply, bas_apply, ← map_mul, trace_inclR, mul_comm]
    simp [hM, Algebra.traceMatrix_apply, Algebra.traceForm_apply, hc]
  have hdet : M.det ≠ 0 := by
    rw [hM, ← RingHom.map_det, ← Algebra.discr_def]
    exact (map_ne_zero _).2 (Algebra.discr_not_zero_of_basis F _)
  have h0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
  rw [← (bas (E := E) v).sum_equivFun y]
  simp [← hc, h0]
theorem trC_bijective : Function.Bijective (trC (E := E) v) := by
  refine ⟨trC_injective v, ?_⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact trC_injective v
  · rw [Module.finrank_eq_card_basis (bas (E := E) v), Module.finrank_fin_fun, Fintype.card_fin]
def trE : (Fv F v ⊗[F] E) ≃ₗ[Fv F v] (Fin (Module.finrank F E) → Fv F v) :=
  LinearEquiv.ofBijective (trC (E := E) v) (trC_bijective v)
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd


