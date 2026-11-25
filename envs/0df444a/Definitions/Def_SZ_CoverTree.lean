-- Prove2me | Definitions.Def_SZ_CoverTree
-- name    : SZ_CoverTree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:47:17.523814+00:00
-- url     : https://prove2.me/theorems/cfc56d7e-d9c7-4373-9f88-a4aec61061fc
-- title:
--   Cover Tree
-- statement:
--   Definitions and structural lemmas for Cover Tree, from Ralf Stephan (rwst/Square-Roots; see pinned CC0-1.0 LICENSE and source headers)'s pinned Even integral parts of powers of square roots and Dubickas Problem 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
set_option autoImplicit false
namespace SZ
open Filter Topology
noncomputable def valS (s : ℤ × ℤ) : ℝ := (s.1 : ℝ) + (s.2 : ℝ) * Real.sqrt 3
def stepS (s d : ℤ × ℤ) : ℤ × ℤ := (3 * (s.1 - d.1), 3 * (s.2 - d.2))
def EvenDigit (d : ℤ × ℤ) : Prop := (d.1 = 0 ∨ d.1 = 2) ∧ (d.2 = 0 ∨ d.2 = 2)
def Adm (s d : ℤ × ℤ) : Prop :=
  EvenDigit d ∧ 0 ≤ valS s - valS d ∧ valS s - valS d ≤ 1 + Real.sqrt 3
def runState (s₀ : ℤ × ℤ) (d : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => s₀
  | k + 1 => stepS (runState s₀ d k) (d k)
def IsRun (s₀ : ℤ × ℤ) (d : ℕ → ℤ × ℤ) : Prop := ∀ k, Adm (runState s₀ d k) (d k)
noncomputable def gState (s : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => s
  | k + 1 => stepS (gState s k) (pick (valS (gState s k)))
noncomputable def gDigit (s : ℤ × ℤ) (k : ℕ) : ℤ × ℤ := pick (valS (gState s k))
def GStart (s : ℤ × ℤ) : Prop :=
  0 ≤ valS s ∧ valS s ≤ 3 + 3 * Real.sqrt 3 ∧ 4 ≤ s.2
def InO (w : ℝ) : Prop :=
  (2 ≤ w ∧ w ≤ 1 + Real.sqrt 3) ∨
  (2 * Real.sqrt 3 ≤ w ∧ w ≤ 3 + Real.sqrt 3) ∨
  (2 + 2 * Real.sqrt 3 ≤ w ∧ w ≤ 1 + 3 * Real.sqrt 3)
noncomputable def branchDigit (w : ℝ) (b : Bool) : ℤ × ℤ :=
  if w ≤ 1 + Real.sqrt 3 then cond b (2, 0) (0, 0)
  else if w ≤ 3 + Real.sqrt 3 then cond b (2, 0) (0, 2)
  else cond b (2, 2) (0, 2)
structure Node where
  /-- the cover state -/
  st : ℤ × ℤ
  /-- an `a = 0` has been emitted since the last branching -/
  g0 : Bool
  /-- a `b = 2` has been emitted since the last branching -/
  g2 : Bool
  /-- bits of `β` consumed so far -/
  used : ℕ
def Branching (n : Node) : Prop := n.g0 = true ∧ n.g2 = true ∧ InO (valS n.st)
open Classical in
/-- The offset played at a node. -/
noncomputable def nodeDigit (β : ℕ → Bool) (n : Node) : ℤ × ℤ :=
  if Branching n then branchDigit (valS n.st) (β n.used) else pick (valS n.st)
open Classical in
/-- The successor node: branch and reset the flags, or follow the rule and bank. -/
noncomputable def nodeNext (β : ℕ → Bool) (n : Node) : Node :=
  if Branching n then
    { st := stepS n.st (nodeDigit β n),
      g0 := decide ((nodeDigit β n).1 = 0),
      g2 := decide ((nodeDigit β n).2 = 2),
      used := n.used + 1 }
  else
    { st := stepS n.st (nodeDigit β n),
      g0 := n.g0 || decide ((nodeDigit β n).1 = 0),
      g2 := n.g2 || decide ((nodeDigit β n).2 = 2),
      used := n.used }
noncomputable def node (β : ℕ → Bool) (k : ℕ) : Node :=
  (nodeNext β)^[k] { st := (-12, 9), g0 := false, g2 := false, used := 0 }
noncomputable def treeDigit (β : ℕ → Bool) (k : ℕ) : ℤ × ℤ := nodeDigit β (node β k)
def runY (d : ℕ → ℤ × ℤ) (i : ℕ) : ℤ := 2 - (d i).2
noncomputable def runXi (d : ℕ → ℤ × ℤ) : ℝ := (4 + digitReal 3 (fun i => (d i).1)) / 3
def witnessSet : Set ℝ := {ξ : ℝ | 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * Real.sqrt 3 ^ n⌋}
noncomputable def treeXi (β : ℕ → Bool) : ℝ := runXi (treeDigit β)
end SZ


