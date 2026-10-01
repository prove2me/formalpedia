-- Prove2me | Definitions.Def_Yukon_39c99ed05a7eaf3e0a4fc6e0
-- name    : Yukon_39c99ed05a7eaf3e0a4fc6e0
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:57:58.234724+00:00
-- url     : https://prove2.me/theorems/32783212-02ef-4b2a-8f57-0520b66caf78
-- title:
--   YukonModule.PolyFun.PFunctor.Handler.Free.part0
-- statement:
--   Source module PolyFun.PFunctor.Handler.Free.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Handler/Free.lean
--
--   yukon-proof-operation:fe56908d0c7c16203b0df1adc734166a70f813e742ce5e8cc23ee9e1c71bea0c
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZmU1NjkwOGQwYzdjMTYyMDNiMGRmMWFkYzczNDE2NmE3MGY4MTNlNzQyY2U1ZThjYzIzZWU5ZTFjNzFiZWEwYyIsImhhc2giOiJmNzk4YmY4ZDM4NzQ5YzI5NGI0MzM4YTQ3ZjU4YWQyMjYwYWJjZGQ2MDQzNmE5YWQzZDRmZDE5YzFjNjEzZjUyIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8zOWM5OWVkMDVhN2VhZjNlMGE0ZmM2ZTAiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Definitions.Def_Yukon_724dee21e2f24de1aadc0f0e

public import Definitions.Def_Yukon_c7f6fc75577fee178fc2046e



public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
meta import Definitions.Def_Yukon_724dee21e2f24de1aadc0f0e
meta import Definitions.Def_Yukon_c7f6fc75577fee178fc2046e
set_option backward.isDefEq.respectTransparency.types false
/-!
# Identity and composition of free handlers

This module equips handlers valued in a free monad with their Kleisli identity
and categorical-order composition. The generic `PFunctor.Handler` definition
remains independent of `FreeM`.
-/

@[expose] public section

universe u u' uA uA' uA'' uA'''

namespace PFunctor
namespace Handler

/-- The identity free handler for a polynomial interface. -/
def id (P : PFunctor.{uA, u}) : Handler (FreeM P) P :=
  fun a => FreeM.lift a

/-- Regard a polynomial lens as the one-operation free handler that issues
the mapped operation and translates its answer through the lens. -/
def ofLens {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (f : Lens P Q) : Handler (FreeM Q) P :=
  fun a => FreeM.liftBind (f.toFunA a) fun answer =>
    FreeM.pure (f.toFunB a answer)

@[simp] theorem ofLens_apply
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (f : Lens P Q) (a : P.A) :
    ofLens f a = FreeM.liftBind (f.toFunA a) fun answer =>
      FreeM.pure (f.toFunB a answer) :=
  rfl

@[simp] theorem ofLens_id (P : PFunctor.{uA, u}) :
    ofLens (Lens.id P) = id P :=
  rfl

/-- Kleisli composition of free handlers, in categorical order:
`second.comp first` first interprets by `first`, then by `second`. The source
and intermediate direction universes agree because `FreeM.liftM` requires
them to; the final target direction universe remains independent. -/
def comp {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u'}}
    (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P) :
    Handler (FreeM R) P :=
  fun a => (first a).liftM second

@[simp]
theorem comp_apply {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u'}}
    (second : Handler (FreeM R) Q) (first : Handler (FreeM Q) P)
    (a : P.A) :
    second.comp first a = (first a).liftM second :=
  rfl

/-- The one-operation handler embedding preserves lens composition. -/
theorem ofLens_comp
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u'}}
    (second : Lens Q R) (first : Lens P Q) :
    ofLens (second ∘ₗ first) = (ofLens second).comp (ofLens first) := rfl

@[simp]
theorem id_comp {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    (first : Handler (FreeM Q) P) :
    (id Q).comp first = first := by
  funext a
  exact FreeM.liftM_lift_eq_self (first a)

@[simp]
theorem comp_id {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u'}}
    (second : Handler (FreeM Q) P) :
    second.comp (id P) = second := by
  funext a
  exact FreeM.liftM_lift second a

/-- Free-handler composition is associative in categorical order. -/
theorem comp_assoc
    {P : PFunctor.{uA, u}} {Q : PFunctor.{uA', u}}
    {R : PFunctor.{uA'', u}} {V : PFunctor.{uA''', u'}}
    (third : Handler (FreeM V) R)
    (second : Handler (FreeM R) Q)
    (first : Handler (FreeM Q) P) :
    (third.comp second).comp first = third.comp (second.comp first) := by
  funext a
  exact (FreeM.liftM_comp (first a) second third).symm

end Handler
end PFunctor


