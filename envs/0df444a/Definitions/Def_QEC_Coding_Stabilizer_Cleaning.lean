-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_Cleaning
-- name    : QEC_Coding_Stabilizer_Cleaning
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:19:33.656973+00:00
-- url     : https://prove2.me/theorems/ebdb2bd8-a759-4b09-b696-c21852ea31f2
-- title:
--   Cleaning
-- statement:
--   Definitions and structural lemmas for Cleaning, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Cleaning.lean

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def GeneratorMeets
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (j : κ) : Prop :=
  ¬ Disjoint (H.generatorSupport j) R
def MeetingIndex
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :=
  {j : κ // H.GeneratorMeets R j}
instance instFiniteMeetingIndex
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) : Finite (H.MeetingIndex R) :=
  Finite.of_injective Subtype.val Subtype.val_injective
noncomputable instance instFintypeMeetingIndex
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) : Fintype (H.MeetingIndex R) :=
  Fintype.ofFinite _
def GeneratedByMeeting
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (S : Binary ι) : Prop :=
  GeneratedStabilizer
    (fun j : H.MeetingIndex R => H.generators j.1) S
def meetingGeneratorSubspace
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :
    Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι) :=
  Submodule.span (ZMod 2)
    (Set.range fun j : H.MeetingIndex R => (H.generators j.1).vector)
end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC


