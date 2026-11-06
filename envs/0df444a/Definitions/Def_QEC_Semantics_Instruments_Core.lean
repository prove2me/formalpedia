-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Core
-- name    : QEC_Semantics_Instruments_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:15:48.667214+00:00
-- url     : https://prove2.me/theorems/65e79ae2-1efe-44ee-a178-d0b298392751
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Core.lean

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
universe u v w
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
structure FiniteInstrument (κ : Type v) [Fintype κ] (Ω : Type w) [Fintype Ω]
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  kraus : FiniteKrausFamily κ H K
  observe : κ → Ω
namespace FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
local instance _p2m_local_instance_a5f1a79248_39 : DecidableEq Ω := Classical.decEq Ω
noncomputable def branchOperator (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (A : Operator H) : Operator K :=
  ∑ i : κ, if I.observe i = outcome then
    (I.kraus.operator i).comp
      (A.comp (LinearMap.adjoint (I.kraus.operator i)))
  else 0
@[simp]
theorem branchOperator_apply (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (A : Operator H) :
    I.branchOperator outcome A =
      ∑ i : κ, if I.observe i = outcome then
        (I.kraus.operator i).comp
          (A.comp (LinearMap.adjoint (I.kraus.operator i)))
      else 0 :=
  rfl
theorem branchOperator_positive (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    {A : Operator H} (hA : LinearMap.IsPositive A) :
    LinearMap.IsPositive (I.branchOperator outcome A) := by
  classical
  unfold branchOperator
  apply LinearMap.isPositive_sum Finset.univ
  intro i _hi
  split_ifs
  · simpa [LinearMap.comp_assoc] using
      hA.adjoint_conj (LinearMap.adjoint (I.kraus.operator i))
  · exact LinearMap.isPositive_zero
noncomputable def bornWeight (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) : ℝ :=
  Complex.re
    (LinearMap.trace Complex K (I.branchOperator outcome rho.toOperator))
theorem trace_branchOperator_eq_bornWeight
    (I : FiniteInstrument κ Ω H K) (outcome : Ω) (rho : DensityOperator H) :
    LinearMap.trace Complex K (I.branchOperator outcome rho.toOperator) =
      (I.bornWeight outcome rho : Complex) := by
  have htrace :=
    (I.branchOperator_positive outcome rho.positive).trace_nonneg
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    exact (Complex.nonneg_iff.mp htrace).2.symm
noncomputable def conditionalDensity (I : FiniteInstrument κ Ω H K)
    (outcome : Ω) (rho : DensityOperator H)
    (hpos : 0 < I.bornWeight outcome rho) :
    DensityOperator K where
  toOperator :=
    ((I.bornWeight outcome rho : Complex)⁻¹) •
      I.branchOperator outcome rho.toOperator
  positive := by
    apply (I.branchOperator_positive outcome rho.positive).smul_of_nonneg
    simp [Complex.nonneg_iff, hpos.le]
  trace_one := by
    rw [map_smul, I.trace_branchOperator_eq_bornWeight outcome rho]
    simp [hpos.ne']
end FiniteInstrument
end
end Semantics
end QEC


