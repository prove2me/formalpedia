-- Prove2me | Definitions.Def_APFPaper1_free_ways_under_the_per_realignment_floor_Vocabulary
-- name    : APFPaper1_free_ways_under_the_per_realignment_floor_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-17T03:35:40.234684+00:00
-- url     : https://prove2.me/theorems/dfe61770-1930-422f-aba5-b1479bf82d85
-- title:
--   Model vocabulary — Free chains under explicit concatenation and floor laws
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   Identity, unconditional cross-context Concat and a positive Floor on distinct alignments are explicit hypotheses. Under them free chains returning to a context fix its alignment, and reversible free reach is a renaming. Concat is stronger than the paper's conditional admissible-composition clause; these laws are not adopted inputs or assertions of physical connectivity.
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
--   Theorems.Thm_APFPaper1_free_ways_under_the_per_realignment_floor; Pullbacks v46, SHA-256 529f30c5a3bf2cde9840cd61eb28752149341bafeb1b37a568e95251a8592976. Theorems.Thm_APFPaper1_free_ways_under_the_per_realignment_floor; pullbacks v46; SHA-256 529f30c5a3bf2cde9840cd61eb28752149341bafeb1b37a568e95251a8592976

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper1.FreeWays

universe u v

/-- A place: a context together with one of its alignments. -/
abbrev Place {Ctx : Type u} (Al : Ctx → Type v) : Type (max u v) := Sigma Al

section Laws
variable {Ctx : Type u} {Al : Ctx → Type v}

/-- (P1) Doing nothing joins a place to itself at no cost. -/
def Identity (Conn : Place Al → Place Al → ℝ → Prop) : Prop := ∀ p, Conn p p 0

/-- (P2 with P3) One way after another is a way, at no more than the sum of the two costs. Asked here of
every pair of ways that meet, through whatever contexts. -/
def Concat (Conn : Place Al → Place Al → ℝ → Prop) : Prop :=
  ∀ p q r c c', Conn p q c → Conn q r c' → ∃ c'', c'' ≤ c + c' ∧ Conn p r c''

/-- (P4) The per-realignment floor, context by context: every way that joins two different alignments
of one context costs at least that context's floor, and the floor is positive. -/
def Floor (Conn : Place Al → Place Al → ℝ → Prop) (eps : Ctx → ℝ) : Prop :=
  (∀ g, 0 < eps g) ∧
    ∀ (g : Ctx) (a b : Al g) (c : ℝ), a ≠ b → Conn ⟨g, a⟩ ⟨g, b⟩ c → eps g ≤ c

/-- A chain of ways, leg after leg, with the sum of the legs' costs. -/
inductive Chain (Conn : Place Al → Place Al → ℝ → Prop) : Place Al → Place Al → ℝ → Prop
  | nil (p : Place Al) : Chain Conn p p 0
  | cons {p q r : Place Al} {c s : ℝ} : Conn p q c → Chain Conn q r s → Chain Conn p r (c + s)

/-- A chain of free ways. -/
inductive FreeChain (Conn : Place Al → Place Al → ℝ → Prop) : Place Al → Place Al → Prop
  | nil (p : Place Al) : FreeChain Conn p p
  | cons {p q r : Place Al} : Conn p q 0 → FreeChain Conn q r → FreeChain Conn p r

variable {Conn : Place Al → Place Al → ℝ → Prop} {eps : Ctx → ℝ}























end Laws

/-! ### Three supplied models -/

section Models
variable {Ctx : Type u} {Al : Ctx → Type v}

/-- Every two places joined at one price `e`, and doing nothing free. -/
def PricedConn (e : ℝ) : Place Al → Place Al → ℝ → Prop :=
  fun p q c => (p = q ∧ c = 0) ∨ c = e



/-- Every way free. -/
def FreeConn : Place Al → Place Al → ℝ → Prop := fun _ _ c => c = 0



end Models

/-- Contexts without end, two alignments (sides) each. Free ways keep the side; every other way costs
`e`. -/
def SideKeepingConn (e : ℝ) : Place (fun _ : ℤ => Bool) → Place (fun _ : ℤ => Bool) → ℝ → Prop :=
  fun p q c => (q.2 = p.2 ∧ c = 0) ∨ c = e





end APFPaper1.FreeWays


