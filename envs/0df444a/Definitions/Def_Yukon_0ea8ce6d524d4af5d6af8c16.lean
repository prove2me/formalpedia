-- Prove2me | Definitions.Def_Yukon_0ea8ce6d524d4af5d6af8c16
-- name    : Yukon_0ea8ce6d524d4af5d6af8c16
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:59:19.701436+00:00
-- url     : https://prove2.me/theorems/ff4f7389-1d1d-4ddb-88ae-53f3e2f0ec85
-- title:
--   YukonModule.VCVio.EvalDist.Instances.FinRatPMF.part0
-- statement:
--   Source module VCVio.EvalDist.Instances.FinRatPMF.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Instances/FinRatPMF.lean
--
--   yukon-proof-operation:263c581a8d999fff2b7d4c059a7fbc32b5861065710b0265b49e8f9e282597a3
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MjYzYzU4MWE4ZDk5OWZmZjJiN2Q0YzA1OWE3ZmJjMzJiNTg2MTA2NTcxMGIwMjY1YjQ5ZThmOWUyODI1OTdhMyIsImhhc2giOiJjMjlhYjZmMGUwNjFmODhmNmEwYjAzMTdmODZkYTg0NTY2ZDY4MTY2YmY5YzliMDRlYWI3ZDM5NTNkNzU5YmY1Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8wZWE4Y2U2ZDUyNGQ0YWY1ZDZhZjhjMTYiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_2a2d046c1b983c45670d8b9f

public import Definitions.Def_Yukon_c042061a45cc167df49b6d76



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
public import Std.Data.HashMap.Lemmas
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.Data.FinEnum
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
meta import Definitions.Def_Yukon_2a2d046c1b983c45670d8b9f
meta import Definitions.Def_Yukon_c042061a45cc167df49b6d76
set_option backward.isDefEq.respectTransparency.types false
/-!
# EvalDist Instances for `FinRatPMF.Raw`

This file exposes the executable `FinRatPMF.Raw` monad to the generic `EvalDist` API.
-/

@[expose] public section

universe u

namespace FinRatPMF
namespace Raw

variable {α : Type u}

noncomputable instance  _root_.FinRatPMF.Raw.instMonadLiftPMF_vCVio : MonadLift Raw PMF where
  monadLift := Raw.toPMFHom.toFun _

noncomputable instance  _root_.FinRatPMF.Raw.instLawfulMonadLiftPMF_vCVio : LawfulMonadLift Raw PMF where
  monadLift_pure := Raw.toPMFHom.toFun_pure'
  monadLift_bind := Raw.toPMFHom.toFun_bind'

/-- Direct `MonadLiftT Raw SetM` defined via the underlying PMF support. The generic
`MonadLiftT SPMF SetM` is non-transitive (declared as `MonadLiftT`, not `MonadLift`,
so `monadLiftTrans` cannot chain through it), so every monad with probabilistic
semantics declares its `SetM` lift directly. -/
noncomputable instance instMonadLiftTRawSetM : MonadLiftT Raw SetM where
  monadLift mx := ((liftM mx : PMF _).support : Set _)

noncomputable instance instLawfulMonadLiftTRawSetM : LawfulMonadLiftT Raw SetM where
  monadLift_pure x := by
    change ((liftM (pure x : Raw _) : PMF _).support : Set _) = {x}
    have : (liftM (pure x : Raw _) : PMF _) = pure x :=
      LawfulMonadLift.monadLift_pure (m := Raw) (n := PMF) x
    rw [this]
    exact PMF.support_pure x
  monadLift_bind mx my := by
    change ((liftM (mx >>= my) : PMF _).support : Set _) =
      Bind.bind (m := SetM)
        ((liftM mx : PMF _).support : Set _)
        (fun x => ((liftM (my x) : PMF _).support : Set _))
    have hbind : (liftM (mx >>= my) : PMF _) =
        (liftM mx : PMF _) >>= fun x => (liftM (my x) : PMF _) :=
      LawfulMonadLift.monadLift_bind (m := Raw) (n := PMF) mx my
    rw [hbind]
    exact PMF.support_bind _ _

/-- Compatibility: `Raw`'s SetM support equals the SPMF support of its `evalDist`. -/
noncomputable instance  _root_.FinRatPMF.Raw.instEvalDistCompatible : EvalDistCompatible Raw where
  support_eq_SPMF_support mx := by
    change ((liftM mx : PMF _).support : Set _) =
      SPMF.support (liftM (liftM mx : PMF _) : SPMF _)
    rw [SPMF.support_liftM]

instance  _root_.FinRatPMF.Raw.instHasEvalFinset : HasEvalFinset Raw where
  finSupport := Raw.support
  coe_finSupport mx := by
    ext x
    rw [Finset.mem_coe, _root_.mem_support_iff, Raw.mem_support_iff, probOutput_def, evalDist_def]
    change mx.prob x ≠ 0 ↔ (liftM (liftM mx : PMF _) : SPMF _) x ≠ 0
    rw [SPMF.liftM_apply]
    change mx.prob x ≠ 0 ↔ ((@Raw.toPMF _ (Classical.decEq _) mx) x) ≠ 0
    simp [Raw.toPMF_apply, Raw.prob_eq_prob inferInstance (Classical.decEq _) mx x]

@[simp] lemma finSupport_eq_support [DecidableEq α] (mx : Raw α) :
    finSupport mx = mx.support := rfl

end Raw
end FinRatPMF


