-- Prove2me | Definitions.Def_Yukon_a90bed0360280b6145f16a15
-- name    : Yukon_a90bed0360280b6145f16a15
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:20:46.731968+00:00
-- url     : https://prove2.me/theorems/54642743-c285-4806-8c74-20e14b50c863
-- title:
--   YukonModule.PolyFun.Interaction.Basic.Sampler.part0
-- statement:
--   Source module PolyFun.Interaction.Basic.Sampler.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/Interaction/Basic/Sampler.lean
--
--   yukon-proof-operation:67c41774c3c7bc2f41e70daac9fd33119b6f3a6b25029c1d9b85659ef3f1cc75
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NjdjNDE3NzRjM2M3YmMyZjQxZTcwZGFhYzlmZDMzMTE5YjZmM2E2YjI1MDI5YzFkOWI4NTY1OWVmM2YxY2M3NSIsImhhc2giOiJhZTcyMzdmMjI4ZmQyNDRhNTNiZTExNGEwOThlMWUxMGE1NzU5OGU0Zjk5Y2VjZGVmZjI5ODRjYzY3Yzg1MzUyIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9hOTBiZWQwMzYwMjgwYjYxNDVmMTZhMTUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Definitions.Def_Yukon_412e5b809148ac542f47bc32



public import Mathlib.Logic.Equiv.Defs
public import Init
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.CategoryTheory.Category.Basic
meta import Definitions.Def_Yukon_412e5b809148ac542f47bc32
set_option backward.isDefEq.respectTransparency.types false
/-!
# Monadic samplers on interaction type trees

A `TypeTree.Sampler m spec` equips every node of a protocol tree `spec : TypeTree.{w}`
with an `m`-computation producing that node's move. Structurally it is a
`PFunctor.FreeM.Displayed.Decoration` whose per-node context is `fun X => m X`, so the full
`Decoration` API (map, map_id, map_comp, …) applies unchanged.

This file defines the `Sampler` abbreviation, the universal `samplePath`
routine that threads a sampler through a type tree to produce a full path,
and `Sampler.interleave`, which is the sampling counterpart of
`ProcessOver.interleave`: combine a scheduler sampler (`m (ULift Bool)`)
with two branch samplers into a sampler for the binary-choice interleaving
tree. The latter is the structural ingredient that lets `openTheory m`'s
`par`, `wire`, and `plug` operations thread per-node samplers compositionally.

Everything here is monad-generic and universe-polymorphic: the intermediate
monad is `m : Type w → Type w'`, the tree lives at the move universe `TypeTree.{w}`,
and the sampler's decoration values live at `Type w'`. Probability-monad-specific
constructions (e.g., `Sampler.uniform` over a `TypeTree.Fintype` ornament) live in
the runtime layer where `ProbComp` is in scope.
-/

public section

universe w w'

namespace Interaction

namespace TypeTree

/--
A `Sampler` for `spec : TypeTree.{w}` provides an `m X` computation at each
node whose move space is `X`, plus recursive samplers for every subtree.

Structurally this is exactly a `PFunctor.FreeM.Displayed.Decoration` whose node context is
`fun X => m X`: the per-node decoration stores an `m`-computation in
the move type of that node, and the functorial `Decoration.map` /
`Decoration.map_id` / `Decoration.map_comp` API applies immediately.

The intermediate monad `m : Type w → Type w'` carries the execution
effects. Typical choices:
* `ProbComp : Type → Type` for coin-flip-only protocols.
* `OracleComp (unifSpec + roSpec) : Type → Type` for protocols with
  shared random oracle access, where samplers can issue oracle queries
  via `query`.
* `OptionT ProbComp : Type → Type` for observation-style semantics that
  need to inject failure mass.
-/
abbrev Sampler (m : Type w → Type w') (spec : TypeTree.{w}) : Type (max w w') :=
  Decoration (fun X => m X) spec

/--
Execute a sampler to produce a full path of `spec` in the monad `m`.

At each node the sampler monadically chooses a move; that move determines
which subtree to continue sampling.
-/
def samplePath {m : Type w → Type w'} [Monad m] :
    (spec : TypeTree.{w}) → Sampler m spec → m (Path spec)
  | .done, _ => pure ⟨⟩
  | .node _ rest, ⟨samp, sampRest⟩ => do
      let x ← samp
      let tr ← samplePath (rest x) (sampRest x)
      return ⟨x, tr⟩

/--
Combine a scheduler sampler with two per-branch samplers into a sampler
for the binary-choice interleaving tree
`TypeTree.node (ULift Bool) (fun ⟨true⟩ => spec₁ | ⟨false⟩ => spec₂)`.

This is the sampling counterpart of `Concurrent.ProcessOver.interleave`:
the scheduler flips a coin in `m` to pick a branch, and then the chosen
branch's sampler runs to produce the remainder of the path.

`openTheory m`'s `par`, `wire`, and `plug` all combine two open processes
via a binary-choice scheduling node, and `Sampler.interleave` threads the
per-step samplers through that node compositionally.
-/
def Sampler.interleave {m : Type w → Type w'}
    {spec₁ spec₂ : TypeTree.{w}}
    (schedulerSampler : m (ULift.{w, 0} Bool))
    (sampler₁ : Sampler m spec₁)
    (sampler₂ : Sampler m spec₂) :
    Sampler m (TypeTree.node (ULift.{w, 0} Bool) fun
      | ⟨true⟩ => spec₁
      | ⟨false⟩ => spec₂) :=
  ⟨schedulerSampler, fun
    | ⟨true⟩ => sampler₁
    | ⟨false⟩ => sampler₂⟩

end TypeTree

end Interaction


