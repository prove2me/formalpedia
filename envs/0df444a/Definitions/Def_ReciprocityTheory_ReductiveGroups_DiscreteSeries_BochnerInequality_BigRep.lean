-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:40:50.446834+00:00
-- url     : https://prove2.me/theorems/216946e4-0f5a-422b-9805-3a1eb107d6f5
-- title:
--   Big Rep
-- statement:
--   Definitions and structural lemmas for Big Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigRep.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section BigRepA
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
variable {E : Fin n → Fin n → Module.End ℂ M}
end BigRepA
section BigRepB
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
def swFst {k : ℕ} (i : Fin k) (a b : Fin n) : Equiv.Perm (Fin k → Fin n × Fin n) :=
  Function.Involutive.toPerm (fun κ => Function.update κ i (Equiv.swap a b (κ i).1, (κ i).2))
    (fun κ => by simp [Function.update_idem])
def swSnd {k : ℕ} (i : Fin k) (a b : Fin n) : Equiv.Perm (Fin k → Fin n × Fin n) :=
  Function.Involutive.toPerm (fun κ => Function.update κ i ((κ i).1, Equiv.swap a b (κ i).2))
    (fun κ => by simp [Function.update_idem])
end BigRepB
section BigRep
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
end BigRep
end ReciprocityTheory.ChartRestriction.DS


