-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPriority
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPriority
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:14:43.515553+00:00
-- url     : https://prove2.me/theorems/79308a1c-e1d7-48c7-a740-c598b4e1030b
-- title:
--   Event Priority
-- statement:
--   Definitions and structural lemmas for Event Priority, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/EventPriority.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_eventScanKey_injective

set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
def eventPriorityLE (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) : Prop := eventScanKey P J r e ≤ eventScanKey P J r f
noncomputable instance eventPriorityDecidable (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) : DecidableRel (eventPriorityLE P J r) := fun e f =>
  inferInstanceAs (Decidable (eventScanKey P J r e ≤ eventScanKey P J r f))
instance eventPriorityTrans (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ) :
    IsTrans (Event P J r) (eventPriorityLE P J r) :=
  ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
instance eventPriorityAntisymm (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ) :
    Std.Antisymm (eventPriorityLE P J r) :=
  ⟨fun _ _ h1 h2 => eventScanKey_injective P J r (le_antisymm h1 h2)⟩
instance eventPriorityTotal (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ) :
    Std.Total (eventPriorityLE P J r) := ⟨fun _ _ => le_total _ _⟩
end QEC.Coding.BDL26RandomPerturbation


