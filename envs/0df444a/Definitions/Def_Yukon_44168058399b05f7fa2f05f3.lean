-- Prove2me | Definitions.Def_Yukon_44168058399b05f7fa2f05f3
-- name    : Yukon_44168058399b05f7fa2f05f3
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:53:54.207846+00:00
-- url     : https://prove2.me/theorems/88e70b79-0cb5-4a50-a4a1-7ad04bbad181
-- title:
--   YukonModule.VCVio.EvalDist.Defs.Instances.part0
-- statement:
--   Source module VCVio.EvalDist.Defs.Instances.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Defs/Instances.lean
--
--   yukon-proof-operation:6f049dbef9d28f32152cea5439921ce5a5a3d1a0d158383ac5c7ae4cdee9c640
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NmYwNDlkYmVmOWQyOGYzMjE1MmNlYTU0Mzk5MjFjZTVhNWEzZDFhMGQxNTgzODNhYzVjN2FlNGNkZWU5YzY0MCIsImhhc2giOiJlY2JkYjJkY2I4ZmQyOGFiMDUyM2QyZjE2MmUxNjI0Y2IzNTQ2ZmE2MDg5MTIwMjViZmQ0NDJkOGRkZjE0YmViIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl80NDE2ODA1ODM5OWIwNWY3ZmEyZjA1ZjMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Definitions.Def_Yukon_10be02bf5325c192ea9b6156



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.Data.Vector.Defs
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
meta import Definitions.Def_Yukon_10be02bf5325c192ea9b6156
set_option backward.isDefEq.respectTransparency.types false
/-!
# Monad Evaluation Semantics Instances

This file defines various instances of evaluation semantics for different monads
-/

@[expose] public section

universe u v w

variable {α β γ : Type u}

namespace SetM

@[simp, grind =]
lemma support_eq_run (s : SetM α) : support s = s.run := rfl

end SetM

namespace SPMF

@[simp, grind =]
protected lemma evalDist_def (p : SPMF α) : evalDist p = p := rfl

@[grind =]
protected lemma support_eq_support (p : SPMF α) : support p = SPMF.support p := rfl

@[grind =]
lemma probOutput_eq_apply (p : SPMF α) (x : α) : Pr[= x | p] = p x := rfl

lemma evalDist_eq_iff {m} [Monad m] [MonadLiftT m SPMF] (mx : m α) (p : SPMF α) :
    𝒟[mx] = p ↔ ∀ x, Pr[= x | mx] = p x := by
  simp only [probOutput_def, DFunLike.ext_iff]

end SPMF

namespace PMF

@[simp] lemma evalDist_eq (p : PMF α) : evalDist p = liftM p := rfl

@[simp] lemma probOutput_eq_apply (p : PMF α) (x : α) : Pr[= x | p] = p x := by
  simp [probOutput_def]

end PMF

@[simp] lemma SPMF.evalDist_liftM (p : PMF α) :
    evalDist (m := SPMF) (liftM p) = 𝒟[p] := rfl

@[simp] lemma SPMF.probOutput_liftM (p : PMF α) (x : α) :
    Pr[= x | (liftM p : SPMF α)] = Pr[= x | p] := rfl

@[simp] lemma SPMF.probEvent_liftM (p : PMF α) (e : α → Prop) :
    Pr[ e | (liftM p : SPMF α)] = Pr[ e | p] := rfl

@[simp] lemma SPMF.probFailure_liftM (p : PMF α) :
    Pr[⊥ | (liftM p : SPMF α)] = Pr[⊥ | p] := rfl

namespace Id

/-- Lift `Id` into `PMF` (a `pure` of the result), giving `Id` the canonical total denotation. -/
noncomputable instance  _root_.Id.instMonadLiftPMF_vCVio : MonadLift Id PMF where
  monadLift x := pure x.run

noncomputable instance  _root_.Id.instLawfulMonadLiftPMF_vCVio : LawfulMonadLift Id PMF where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := by
    change (PMF.pure _ : PMF _) = (pure _ : PMF _).bind fun x => pure _
    simp

instance  _root_.Id.instHasEvalFinset : HasEvalFinset Id where
  finSupport x := {x}
  coe_finSupport x := by
    ext y
    change y ∈ (↑({x.run} : Finset _) : Set _) ↔ y ∈ SetM.run (pure x.run : SetM _)
    rw [Finset.coe_singleton]
    rfl

@[simp, grind =]
lemma support_eq_singleton (x : Id α) : support x = {x.run} := rfl

@[simp, grind =]
lemma finSupport_eq_singleton [DecidableEq α] (x : Id α) : finSupport x = {x.run} := rfl

@[simp, grind =]
lemma probOutput_eq_ite [DecidableEq α] (x : Id α) (y : α) :
    Pr[= y | x] = if y = x.run then 1 else 0 := by
  rw [← Id.pure_run x, probOutput_pure]
  rfl

@[simp, grind =]
lemma probEvent_eq_ite (x : Id α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | x] = if p x.run then 1 else 0 := by
  rw [← Id.pure_run x, probEvent_pure]
  rfl

lemma probFailure_eq_zero (x : Id α) : Pr[⊥ | x] = 0 := probFailure_pure _

end Id


