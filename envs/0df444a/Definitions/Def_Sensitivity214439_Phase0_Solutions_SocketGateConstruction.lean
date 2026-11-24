-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
-- name    : Sensitivity214439_Phase0_Solutions_SocketGateConstruction
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:48:25.993808+00:00
-- url     : https://prove2.me/theorems/85858fef-0377-444f-bb6b-b578f72900bc
-- title:
--   Actual socket-based Boolean gate construction
-- statement:
--   A guard family assigns to each parent row a finite collection of finite socket sets. The input at socket $(v,s)$ is the restriction of the parent input to that socket's child coordinates. Non-self guards contain only sockets whose row differs from the source row.
--
--   A gate recipe supplies soft and hard cutoffs, a soft allowance, and a nonempty finite set of target assignments for every rank and failure count. A guard is active when at least one inspected child passes its cutoff; the guard count is the number of active checks.
--
--   The parent row $v$ accepts rank $j$ exactly when its soft count is within allowance, every hard check is quiet, and some permitted target assignment is accepted on all own sockets by a common child color. A unary recipe specializes this construction to one side and the singleton assignment at its target rank.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/SocketGateConstruction.lean lines 20–74; SHA256 7893251a6100af5ab7d50e6ec73890158da06b3df5fdca802b4704a38bd92800; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
# Actual socket gates and canonical blocks

A guard inspects a finite set of child sockets. It is positive exactly when
at least one inspected child passes the cutoff. Thus singleton guards give the
external labeled checks, and two-socket guards give the internal OR checks.

Every target option requires all target sockets to accept the same child row
identity. Unary options contain one threshold. Paired options contain the two
assignments of the weak and strong thresholds to the two target sockets.
-/

namespace SensitivityRankedConstruction

noncomputable section
open scoped Classical

abbrev GuardFamily (V S : Type) := V → Finset (Finset (V × S))

def socketInput {V S I : Type} (x : ((V × S) × I) → Bool)
    (socket : V × S) : I → Bool := fun i => x (socket, i)



def NoSelfGuards {V S : Type} (guards : GuardFamily V S) : Prop :=
  ∀ v check, check ∈ guards v → ∀ socket ∈ check, socket.1 ≠ v

structure GateRecipe (S : Type) (L : ℕ) where
  soft : Fin L → ℕ
  hard : Fin L → ℕ
  allowance : Fin L → ℕ
  targets : Fin L → ℕ → Finset (S → Fin L)
  targets_nonempty : ∀ j failures, (targets j failures).Nonempty

def guardActive {V S I Color : Type} {L : ℕ}
    (row : RowFamily I Color L) (cutoff : ℕ)
    (x : ((V × S) × I) → Bool) (check : Finset (V × S)) : Prop :=
  ∃ socket ∈ check, passes row cutoff (socketInput x socket)

def guardCount {V S I Color : Type} {L : ℕ}
    (row : RowFamily I Color L) (guards : GuardFamily V S)
    (v : V) (cutoff : ℕ) (x : ((V × S) × I) → Bool) : ℕ :=
  ((guards v).filter (guardActive row cutoff x)).card

/-- The actual row predicate: the soft-failure count is affordable, no hard
guard is positive, and one target assignment works with a common child color.
The disabled hard cutoff `L` makes the hard condition automatic for an ordinary
row; a modified warm row uses allowance one and a finite hard cutoff. -/
def gateRow {V S I Color : Type} {L : ℕ}
    (row : RowFamily I Color L) (guards : GuardFamily V S)
    (recipe : GateRecipe S L) : RowFamily ((V × S) × I) V L :=
  fun v j x =>
    guardCount row guards v (recipe.soft j) x ≤ recipe.allowance j ∧
    (∀ check ∈ guards v, ¬ guardActive row (recipe.hard j) x check) ∧
    ∃ c assignment,
      assignment ∈ recipe.targets j (guardCount row guards v (recipe.soft j) x) ∧
      ∀ s, row c (assignment s) (socketInput x (v, s))

def unaryRecipe {L : ℕ} (soft hard allowance : Fin L → ℕ)
    (target : Fin L → ℕ → Fin L) : GateRecipe Unit L where
  soft := soft
  hard := hard
  allowance := allowance
  targets := fun j failures => {fun _ => target j failures}
  targets_nonempty := by intro j failures; exact Finset.singleton_nonempty _


































end
end SensitivityRankedConstruction


