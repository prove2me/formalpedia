-- Prove2me | Definitions.Def_ValiantBorder_tapeAutomata
-- name    : ValiantBorder_tapeAutomata
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:03:45.628626+00:00
-- url     : https://prove2.me/theorems/e8bc1e0b-6437-422a-8718-4ffc68c5fd18
-- title:
--   Weighted tape automata and their run values
-- statement:
--   A letter specifies an operation at a tape or input channel. A matched word respects the tape constraints and the given inputs. Its contribution is a matrix coefficient of the product of its transition matrices. The run value is the sum of these contributions over all matched words of the given length.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Universal.lean#L19-L47).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Universal.lean#L19-L47.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_programWord

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026).
Source: `anthropics/formal-math`, revision
11b6c7e3c927df2658f513b6b68ea7f8929c62c5, `vp-vnp/Paper/{Universal,UniversalSteps,CircuitPhi,Circuit}.lean`.
The construction uses the weighted universal automaton, its tape semantics and the grid representation of its run polynomial.
Apache-2.0. -/
namespace Nc
variable {Z Γ : Type*} [DecidableEq Z]
/-- The words on the channels. -/
def proj (o : List (Z × Γ)) : Z → List Γ := fun z => (o.filter fun a => a.1 = z).map Prod.snd

/-- Channels: the two sides of the tapes, and the inputs. -/
inductive Ch (S J : Type*) where
  /-- a side of a tape -/
  | tp (s : S) (b : Bool)
  /-- an input -/
  | inp (j : J)
  deriving DecidableEq, Fintype

end Nc
namespace Nc

variable {F : Type*} [CommRing F] {Γ S J Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]

/-- A letter of a run. -/
abbrev Letter (S J Γ : Type*) := Option (Ch S J × Γ)

/-- What a run emits. -/
def emit (o : List (Letter S J Γ)) : Ch S J → List Γ := proj o.reduceOption

/-- The run is matched: both sides of every tape agree, and the inputs are `u`. -/
def Matched (o : List (Letter S J Γ)) (u : J → List Γ) : Prop :=
  (∀ s, emit o (.tp s false) = emit o (.tp s true)) ∧ ∀ j, emit o (.inp j) = u j

instance (o : List (Letter S J Γ)) (u : J → List Γ) : Decidable (Matched o u) := by
  unfold Matched; infer_instance

/-- The value of an automaton with transition matrices `mu`, initial state `i` and final state `e` at the input
`u`: the sum over the matched runs of length `t`. -/
def runVal (mu : Letter S J Γ → Matrix Q Q F) (i e : Q) (t : ℕ) (u : J → List Γ) : F :=
  ∑ o : Fin t → Letter S J Γ, if Matched (List.ofFn o) u then ((List.ofFn o).map mu).prod i e else 0

end Nc

namespace Nc.Dl
open NS1 NS1.Tree
/-- The brackets of a tree, as letters. -/
def wordG {Γ : Type} (b0 b1 : Γ) : Tree → List Γ
  | .nil => [b0]
  | .cons a b => b1 :: (wordG b0 b1 a ++ wordG b0 b1 b)

end Nc.Dl


