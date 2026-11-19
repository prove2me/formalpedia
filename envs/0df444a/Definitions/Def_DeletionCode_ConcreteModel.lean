-- Prove2me | Definitions.Def_DeletionCode_ConcreteModel
-- name    : DeletionCode_ConcreteModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:08:22.702667+00:00
-- url     : https://prove2.me/theorems/ac04c14b-852d-42a4-8c8a-5358b637d349
-- title:
--   Concrete Model
-- statement:
--   Definitions and structural lemmas for Concrete Model, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteModel.lean

import Definitions.Def_DeletionCode_ConcreteDecoder
import Definitions.Def_DeletionCode_RootSelection
set_option autoImplicit true
namespace DeletionCode.ConcreteModel
open Windows HeaderRecovery SelectedWindows PartialWords PathMemory ConcreteDecoder
structure Model (B : Type*) (x : Letters) (n k : ℕ) where
  header : B → Header
  long : B → Letters
  schedule : Recovery.Data B
  rho_lower : ∀ b, 1 ≤ (header b).rho
  rho_upper : ∀ b, (header b).rho ≤ k + 1
  header_bit : ∀ b, long b (editOffset k) = (header b).bit
  base_occurrence : ∀ b w, schedule.source b w = none →
    ∃ a, a + windowLength k ≤ n ∧
      Agree x a (negativePath k (header b) (long b))
        (windowStart (negativeExtra k (header b)) w) (windowLength k)
  supplier_occurrence : ∀ b w a, schedule.source b w = some a →
    ∃ side j, j + windowLength k ≤ pathLength k (header a) side ∧
      Agree (negativePath k (header b) (long b))
        (windowStart (negativeExtra k (header b)) w)
        (pathLetters k (header a) (long a) side) j (windowLength k)
  adjacent_seed : ∀ a b, schedule.adjacent a b →
    ∃ sideA sideB i j, i + k ≤ pathLength k (header a) sideA ∧
      j + k ≤ pathLength k (header b) sideB ∧
      Agree (pathLetters k (header a) (long a) sideA) i
        (pathLetters k (header b) (long b) sideB) j k
  root_occurrence : ∀ b, schedule.root b →
    ∃ a, a + negativeLength k (header b) ≤ n ∧
      Agree x a (negativePath k (header b) (long b)) 0 (negativeLength k (header b))
variable {B : Type*} {x : Letters} {n k : ℕ}
def Model.Sound (M : Model B x n k) (mem : Bank B) : Prop :=
  ∀ b, PartialWords.Sound (mem b) (negativePath k (M.header b) (M.long b))
    (negativeLength k (M.header b))
def Model.Realizes (M : Model B x n k) (s : Recovery.State B) (mem : Bank B) : Prop :=
  SelectedWindows.Realizes s mem (fun b => negativeExtra k (M.header b)) k
structure Model.Invariant [DecidableEq B] (M : Model B x n k)
    (s : Recovery.State B) (mem : Bank B) : Prop where
  wellFormed : s.WellFormed M.schedule
  sound : M.Sound mem
  realizes : M.Realizes s mem
end DeletionCode.ConcreteModel


