-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:14:42.475878+00:00
-- url     : https://prove2.me/theorems/9a106878-4e08-44a5-9556-d1026a815b0a
-- title:
--   Adelic Lattice To Local Lattices
-- statement:
--   Definitions and structural lemmas for Adelic Lattice To Local Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FinKW.LocTo
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
def mulSet (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Subring (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) where
  carrier := {c | ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
    psiV I v c • z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))}
  mul_mem' := fun {a b} ha hb z hz => by
    rw [map_mul, mul_smul]
    exact ha _ (hb z hz)
  one_mem' := fun z hz => by
    rw [map_one, one_smul]
    exact hz
  add_mem' := fun {a b} ha hb z hz => by
    rw [map_add, add_smul]
    exact add_mem (ha z hz) (hb z hz)
  zero_mem' := fun z _ => by
    rw [map_zero, zero_smul]
    exact zero_mem _
  neg_mem' := fun {a} ha z hz => by
    rw [map_neg, neg_smul]
    exact neg_mem (ha z hz)
end PI.FinKW.LocTo


