-- Prove2me | Definitions.Def_APFPaper1_OccupantOf
-- name    : APFPaper1_OccupantOf
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-17T03:36:00.198285+00:00
-- url     : https://prove2.me/theorems/4401eceb-6de5-4175-ab36-e9f340083bb4
-- title:
--   Proposed exact occupant and availability predicates
-- statement:
--   An exact occupant serves a given family, keeps exactly its needed records, pays their finite sum, and minimizes the serving bill. EveryFamilyOccupied is an existence hypothesis for nonempty admissible families. These proposed predicates do not identify B06's actual alignment or assert any occupant exists; no input revision is installed.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper1_OccupantOf; Pullbacks v46, SHA-256 6b902ccc170cbc0793f8de2b7001d7c3fd3306a3ebefa9b9d424ed381076ede6. Definitions.Def_APFPaper1_OccupantOf; pullbacks v46; SHA-256 6b902ccc170cbc0793f8de2b7001d7c3fd3306a3ebefa9b9d424ed381076ede6

import Definitions.Def_APFPaper5_K1_SourcePartyScore

set_option autoImplicit false

open APFPaper5.K1

namespace APFPaper1.Source

variable {D P R Record : Type*}

/-- An occupant of a family, for a given cost of each record: a protocol that serves the family, keeps no
record the family does not need, bills exactly the cost of the records it keeps, and bills no more than
any protocol serving the family. -/
def IsOccupantOf (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (cost : Record → ℝ) (p : P) (S : Finset D) : Prop :=
  SourceServes maintained sufficient usesToRealize p S ∧
    maintained p ⊆ sourceNeeds maintained sufficient usesToRealize S ∧
    (∃ N : Finset Record, (↑N : Set Record) = maintained p ∧
      (calibration (wholeResource p) : ℝ) = ∑ a ∈ N, cost a) ∧
    ∀ q : P, SourceServes maintained sufficient usesToRealize q S →
      (calibration (wholeResource p) : ℝ) ≤ (calibration (wholeResource q) : ℝ)

/-- The availability sentence in the occupant's words: every nonempty family within capacity has an
occupant. A CLAIM about the data, not a definition of anything: it is typed here so that theorems can
name it as a hypothesis. -/
def EveryFamilyOccupied (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (cost : Record → ℝ) (C : ℝ) : Prop :=
  ∀ S : Finset D, S.Nonempty →
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S →
    ∃ p : P, IsOccupantOf wholeResource calibration maintained sufficient usesToRealize cost p S

end APFPaper1.Source


