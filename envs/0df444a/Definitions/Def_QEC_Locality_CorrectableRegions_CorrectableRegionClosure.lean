-- Prove2me | Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
-- name    : QEC_Locality_CorrectableRegions_CorrectableRegionClosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:59:05.624198+00:00
-- url     : https://prove2.me/theorems/b9d84214-8acd-4e3a-ace5-da60ac67436d
-- title:
--   Correctable Region Closure
-- statement:
--   Definitions and structural lemmas for Correctable Region Closure, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def restrictBinaryTo (R : Finset ι) (E : Binary ι) : Binary ι :=
  { phase := 0
    vector :=
      { xPart := fun i => if i ∈ R then E.vector.xPart i else 0
        zPart := fun i => if i ∈ R then E.vector.zPart i else 0 } }
def localIndexOfBinary (S : FiniteSubsystem ι) (E : Binary ι) :
    LocalPauliWordIndex S :=
  (fun i => E.vector.xPart i, fun i => E.vector.zPart i)
def unionSubsystem (A B : FiniteSubsystem ι) : FiniteSubsystem ι :=
  ⟨A.selected ∪ B.selected⟩
def familyUnionSubsystem {α : Type w} (regions : α → FiniteSubsystem ι)
    (s : Finset α) : FiniteSubsystem ι :=
  ⟨s.biUnion fun a => (regions a).selected⟩
end QEC.Locality


