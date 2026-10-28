-- Prove2me | Definitions.Def_Sensitivity213303_Q2CandidateTypes
-- name    : Sensitivity213303_Q2CandidateTypes
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:01:47.252781+00:00
-- url     : https://prove2.me/theorems/b2bb9834-7d13-40c1-9e34-39c01dacffe4
-- title:
--   Eight actual high-head types for tolerance at most two
-- statement:
--   TargetCandidate records a row whose target test can be repaired in one child; PositiveCandidate additionally has the guard acceptance needed for a high head. GuardCandidate records a row repairable by removing one failed guard. High is the union of the relevant positive and guard conditions, and OfKind splits it into eight mutually usable cases: positive-only levels 0, 1, 2; pure-guard branches 0, 1, 2; and overlap levels 1, 2. Each kind fixes the failed-guard budget used by the tournament enumerator.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module Q2CandidateTypes; source SHA256 7e8db07c231331862a069853ead1b29e5e7fab51f5c60add93e739c5f3441575.

/-
Exact eight-type decomposition for equal-target graded rows through tolerance 2.

The predicates below refer to the actual child truth values and actual failed
guard count. The classification does not assume a sensitivity bound. It can be
instantiated with target b z := F (threshold b) z, and guard := F g.
-/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
namespace TournamentHighRows
end TournamentHighRows


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Q2CandidateTypes
open scoped Classical
open TournamentHighRows

variable {X V : Type}

/-- One lower target is false and its partner is true, at the exact tier. -/
def TargetCandidate (target : ℕ → X → Prop) (Q d b : ℕ) (x y : X) : Prop :=
  b ≤ Q ∧ d = b ∧
    ((¬ target b x ∧ target b y) ∨ (target b x ∧ ¬ target b y))

/-- The positive part of a target candidate has two guard-true children. -/
def PositiveCandidate (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d b : ℕ) (x y : X) : Prop :=
  TargetCandidate target Q d b x y ∧ guard x ∧ guard y

/-- A guard candidate would accept after removal of one actual failed guard. -/
def GuardCandidate (target : ℕ → X → Prop) (Q d b : ℕ) (x y : X) : Prop :=
  b ≤ Q ∧ d = b+1 ∧ target b x ∧ target b y

def High (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X) : Prop :=
  (∃ b, PositiveCandidate guard target Q d b x y) ∨
    (∃ b, GuardCandidate target Q d b x y)

/-- Fixed checkpoint order: P0, P1-only, P2-only, G0-only, G1-only,
    G2, H1=P1∩G0, H2=P2∩G1. -/
def budget (k : Fin 8) : ℕ :=
  match k.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 1
  | 4 => 2 | 5 => 3 | 6 => 1 | _ => 2





def OfKind (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X) (k : Fin 8) : Prop :=
  let P := fun b => PositiveCandidate guard target Q d b x y
  let G := fun b => GuardCandidate target Q d b x y
  match k.val with
  | 0 => P 0
  | 1 => P 1 ∧ ¬ G 0
  | 2 => P 2 ∧ ¬ G 1
  | 3 => G 0 ∧ ¬ P 1
  | 4 => G 1 ∧ ¬ P 2
  | 5 => G 2
  | 6 => P 1 ∧ G 0
  | _ => P 2 ∧ G 1

















def Accepted (target : ℕ → X → Prop) (Q d : ℕ) (x y : X) : Prop :=
  d ≤ Q ∧ target d x ∧ target d y



section ActualRows
variable [Fintype V]

noncomputable def highRows (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (target : ℕ → X → Prop) (Q : ℕ)
    (children : V → Bool → X) : Finset V := by
  classical
  exact Finset.univ.filter fun v => High guard target Q
    (guardFailures R ell guard children v).card (children v false) (children v true)









end ActualRows
end Q2CandidateTypes


