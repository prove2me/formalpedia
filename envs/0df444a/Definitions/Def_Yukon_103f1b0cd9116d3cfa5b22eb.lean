-- Prove2me | Definitions.Def_Yukon_103f1b0cd9116d3cfa5b22eb
-- name    : Yukon_103f1b0cd9116d3cfa5b22eb
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:17:46.183993+00:00
-- url     : https://prove2.me/theorems/4964c7d6-e282-409e-ae70-a93cfb4fd958
-- title:
--   YukonModule.VCVio.OracleComp.RunIO.part0
-- statement:
--   Source module VCVio.OracleComp.RunIO.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/RunIO.lean
--
--   yukon-proof-operation:cb0e091080de19d7cdc1d1820d1cb15cfca79a322a980314a27d92ebf565e5bd
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Y2IwZTA5MTA4MGRlMTlkN2NkYzFkMTgyMGQxY2IxNWNmY2E3OWEzMjJhOTgwMzE0YTI3ZDkyZWJmNTY1ZTViZCIsImhhc2giOiJhYmRhYzMxMDZhMjNkY2QxZjk5YzA5NWIwNTkxMjMzZTU1ZTZlNjYzN2JmNDc0MmUwZmJiMjg3NDY4NWFhNGI5Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8xMDNmMWIwY2Q5MTE2ZDNjZmE1YjIyZWIiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee



public import Batteries.Control.OptionT
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
meta import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
set_option backward.isDefEq.respectTransparency.types false
/-!
# Executing Computations

This file defines a function `runIO` for executing a `ProbComp` in the `IO` monad.
We add this embedding as a `MonadLift` instance, so `#eval` notation works.
-/

@[expose] public section

open OracleSpec

namespace OracleComp

/-- Represent a `ProbComp` via the `IO` monad, allowing actual execution. -/
protected def runIO {α : Type} (oa : ProbComp α) : IO α :=
  simulateQ (spec := unifSpec) (fun n => Fin.ofNat (n + 1) <$> (IO.rand 0 n).toIO) oa

/-- Automatic lifting of probabilistic computations into `IO`. -/
instance  _root_.OracleComp.instMonadLiftProbCompIO : MonadLift ProbComp IO where monadLift := OracleComp.runIO

def test1 : ProbComp (ℕ × ℕ × ℕ) := do
  let x ← $[0..1618]
  let y ← $[0..3141]
  return (x, y, x + y)

def test2 (n : ℕ) : ProbComp (List ℕ) := do
  match n with
  | 0 => return []
  | n + 1 => return (← $[0..100]) :: (← test2 n)

def test3 (n : ℕ) : ProbComp (List ℕ) := do
  let mut xs := []
  for _ in List.range n do
    xs := (← $[0..100]) :: xs
  return xs

def test4 (n : ℕ) : ProbComp (List ℕ) := do
  (List.replicate n ()).mapM (fun () => Fin.val <$> ($[0..100]))

end OracleComp


