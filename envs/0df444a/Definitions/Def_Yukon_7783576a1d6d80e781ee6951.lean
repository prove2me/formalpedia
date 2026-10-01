-- Prove2me | Definitions.Def_Yukon_7783576a1d6d80e781ee6951
-- name    : Yukon_7783576a1d6d80e781ee6951
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:21:30.892993+00:00
-- url     : https://prove2.me/theorems/42ce664b-e70d-4ab6-b735-5afe966d969c
-- title:
--   YukonModule.PolyFun.Interaction.Basic.Shape.part0
-- statement:
--   Source module PolyFun.Interaction.Basic.Shape.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/Interaction/Basic/Shape.lean
--
--   yukon-proof-operation:6e078b219c6922c5e02080925937fcd9eacb2fc63b2aa325c6ee0a817e4638bf
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NmUwNzhiMjE5YzY5MjJjNWUwMjA4MDkyNTkzN2ZjZDllYWNiMmZjNjNiMmFhMzI1YzZlZTBhODE3ZTQ2MzhiZiIsImhhc2giOiIzYzQ4YmUzNDhiYjY3ZjFhN2QzMjJiYzI1YjMwNTgzMmRjYWM0MTE4M2Q5YmJhYjhkNWE5OWFhMDU4NzA0MTM3Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl83NzgzNTc2YTFkNmQ4MGU3ODFlZTY5NTEiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

import all Definitions.Def_Yukon_effa30856d357bd1a68eda4a

public import Definitions.Def_Yukon_7e83e3578ee9b9bb2d29903a

public import Definitions.Def_Yukon_effa30856d357bd1a68eda4a



public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Init
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.CategoryTheory.Category.Basic
meta import Definitions.Def_Yukon_7e83e3578ee9b9bb2d29903a
meta import Definitions.Def_Yukon_effa30856d357bd1a68eda4a
set_option backward.isDefEq.respectTransparency.types false
/-!
# Functorial local syntax over interaction trees

This file introduces the functorial refinement of the local syntax core.

`SyntaxOver` in `Basic/Syntax` is the most general local syntax object: it
describes which node object an agent has at one protocol node, with no
assumption that recursive continuations can be reindexed generically.

`ShapeOver` is the functorial refinement of that base notion:
it equips a `SyntaxOver` with a continuation map. This is exactly the extra
structure needed to define generic output transport such as
`ShapeOver.mapOutput`.

Many important interaction objects are syntax without being shapes in this
sense: if recursive continuations are hidden under an opaque outer constructor,
then a generic continuation map may not exist. This is why `SyntaxOver` is the
semantic base layer, while `ShapeOver` is the stronger interface used when
continuations are exposed functorially enough.

Naming note:
`ShapeOver` keeps the suffix form because it is the primary *functorial*
refinement of syntax, with plain `Shape` recovered as the trivial-context
specialization. This differs from `Decoration.Over`, which is literally
dependent data over a fixed base decoration value.
-/

public section

universe a vΓ vΔ vΛ w uA uB uA₂ uB₂

namespace Interaction

open PFunctor

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB₂}}

/--
`ShapeOver l Agent Γ` is functorial local syntax over an arbitrary control
polynomial executed through a runtime lens `l`.

It refines `SyntaxOver l Agent Γ` with a node-level continuation map. At a
control position `pos : P.A`, recursive continuations are indexed by runtime
directions `Q.B (l.toFunA pos)`, and the lens determines which control child
each runtime direction selects.
-/
structure ShapeOver
    (l : PFunctor.Lens P Q)
    (Agent : Type a)
    (Γ : P.A → Type vΓ) extends SyntaxOver l Agent Γ where
  /--
  Transform the recursive continuation payload of one local node object.
  The agent, control position, node-local context, and runtime move shape are
  unchanged.
  -/
  map :
    {agent : Agent} →
    {pos : P.A} →
    {γ : Γ pos} →
    {A B : Q.B (l.toFunA pos) → Type w} →
    (∀ d, A d → B d) →
    Node agent pos γ A →
    Node agent pos γ B

namespace ShapeOver

variable {l : PFunctor.Lens P Q}
variable {Agent : Type a} {Γ : P.A → Type vΓ}

instance  _root_.Interaction.ShapeOver.instCoeSyntaxOver : Coe (ShapeOver l Agent Γ) (SyntaxOver l Agent Γ) where
  coe := ShapeOver.toSyntaxOver

/--
Restrict a participant-indexed shape to one fixed agent.

The resulting singleton-agent shape has the same node objects and continuation
map as `shape` at `agent`; the dummy `PUnit` agent argument is ignored.
-/
@[expose]
def forAgent (shape : ShapeOver l Agent Γ) (agent : Agent) :
    ShapeOver l PUnit Γ where
  toSyntaxOver := SyntaxOver.forAgent shape.toSyntaxOver agent
  map f node := shape.map (agent := agent) f node

/--
Reindex a functorial local syntax object contravariantly along a node metadata
map.
-/
@[expose]
def comap {Δ : P.A → Type vΔ}
    (f : ∀ pos, Γ pos → Δ pos) (shape : ShapeOver l Agent Δ) :
    ShapeOver l Agent Γ where
  toSyntaxOver := SyntaxOver.comap f shape.toSyntaxOver
  map h := shape.map h

@[simp]
theorem comap_id (shape : ShapeOver l Agent Γ) :
    comap (fun _ γ => γ) shape = shape := by
  cases shape
  rfl

theorem comap_comp {Δ : P.A → Type vΔ} {Λ : P.A → Type vΛ}
    (shape : ShapeOver l Agent Λ)
    (g : ∀ pos, Δ pos → Λ pos) (f : ∀ pos, Γ pos → Δ pos) :
    comap f (comap g shape) = comap (fun pos => g pos ∘ f pos) shape := by
  cases shape
  rfl

end ShapeOver

end Interaction


