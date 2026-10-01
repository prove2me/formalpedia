-- Prove2me | Definitions.Def_Yukon_3df7984cc5373c300a4b8062
-- name    : Yukon_3df7984cc5373c300a4b8062
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:21:59.558986+00:00
-- url     : https://prove2.me/theorems/af6c4fe6-03d9-49b4-b7f2-9b962ca7f6a0
-- title:
--   YukonModule.VCVio.OracleComp.Constructions.Replicate.part0
-- statement:
--   Source module VCVio.OracleComp.Constructions.Replicate.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/Constructions/Replicate.lean
--
--   yukon-proof-operation:d76854bda083f2584856c11b4961d667286c7c71839128868d190e34baabeefb
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZDc2ODU0YmRhMDgzZjI1ODQ4NTZjMTFiNDk2MWQ2NjcyODZjN2M3MTgzOTEyODg2OGQxOTBlMzRiYWFiZWVmYiIsImhhc2giOiJhODljYTQwNGIyOTI5YWI2ZTY2NzEwNGYxNDZlOWM2OGJlMTdkYzY4NmQ5Y2ZkYWQ0MjMwYWFiMGI2YjNmMTJhIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8zZGY3OTg0Y2M1MzczYzMwMGE0YjgwNjIiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee

public import Definitions.Def_Yukon_2b5744019605f484379c669d

public import Definitions.Def_Yukon_e88c9935225aedcca88ceb17

public import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7

public import Init.Data.Vector.Lemmas


public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.List.Sym
public import Init
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Vector.Defs
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Batteries.Control.OptionT
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
meta import Definitions.Def_Yukon_e88c9935225aedcca88ceb17
meta import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
meta import Definitions.Def_Yukon_2b5744019605f484379c669d
meta import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
set_option backward.isDefEq.respectTransparency.types false
/-!
# Running a Computation Multiple Times

This file defines a function `replicate oa n` that runs the computation `oa` a total of `n` times,
returning the result as a list of length `n`.

Note that while the executions are independent, they may no longer be after calling `simulate`.
-/

@[expose] public section

open OracleSpec

universe u v w

namespace OracleComp

/-- Run the computation `oa` repeatedly `n` times to get a list of `n` results. -/
def replicate {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  match n with
  | 0 => pure []
  | n + 1 => do
      let x ← oa
      let xs ← replicate n oa
      pure (x :: xs)

/-- Tail-recursive variant of `replicate`, running `oa` for each entry of a length-`n` list
built by `List.replicateTR`. Agrees with `replicate` via `replicateTR_eq_replicate`. -/
def replicateTR {ι} {spec : OracleSpec ι} {α : Type v}
    (n : ℕ) (oa : OracleComp spec α) : OracleComp spec (List α) :=
  (List.replicateTR n ()).mapM fun () => oa

variable {ι} {spec : OracleSpec ι} {α β : Type v}
  (oa : OracleComp spec α) (n : ℕ)

@[simp, grind =]
lemma replicate_zero : replicate 0 oa = return [] := rfl

@[simp, grind =]
lemma replicateTR_zero : replicateTR 0 oa = return [] := rfl

/-- Bind-style unfolding of `replicate`, convenient for program-logic proofs. -/
@[simp, grind =]
lemma replicate_succ_bind :
    replicate (n + 1) oa = (do
      let x ← oa
      let xs ← replicate n oa
      pure (x :: xs)) := rfl

/-- The tail-recursive `replicateTR` agrees with the recursive `replicate`. The
`@[simp]` annotation lets every later proof about `replicateTR` reduce to the
recursive form automatically. -/
@[simp, grind =]
lemma replicateTR_eq_replicate : replicateTR n oa = replicate n oa := by
  simp only [replicateTR, ← List.replicate_eq_replicateTR]
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, List.mapM_cons, ih]

lemma replicate_succ : replicate (n + 1) oa = List.cons <$> oa <*> replicate n oa := by
  simp [replicate_succ_bind, monad_norm, Function.comp]

@[simp, grind =]
lemma replicate_pure (x : α) :
    (pure x : OracleComp spec α).replicate n = pure (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n hn => simp [hn, List.replicate]

variable [IsUniformSpec spec]

lemma probFailure_replicate :
    Pr[⊥ | oa.replicate n] = 1 - (1 - Pr[⊥ | oa]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp

/-- The probability of getting a list from `replicate` is the product of the chances of
getting each of the individual elements. -/
@[simp]
lemma probOutput_replicate (xs : List α) :
    Pr[= xs | oa.replicate n] = if xs.length = n then (xs.map (Pr[= · | oa])).prod else 0 := by
  have : DecidableEq α := Classical.decEq α
  induction n generalizing xs with
  | zero => cases xs <;> simp [probOutput_eq_zero_of_not_mem_support]
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [replicate_succ, probOutput_cons_seq_map_cons_eq_mul oa (replicate n oa) y ys, ih]
      simp

lemma probEvent_replicate_of_probEvent_cons
    (p : List α → Prop) (hp : p []) (q : α → Prop) (hq : ∀ x xs, p (x :: xs) ↔ q x ∧ p xs) :
    Pr[ p | oa.replicate n] = Pr[ q | oa] ^ n := by
  induction n with
  | zero => simp [hp]
  | succ n ih =>
    rw [replicate_succ,
      probEvent_seq_map_eq_mul oa (replicate n oa) List.cons p q p
        (fun x _ xs _ => hq x xs),
      ih, pow_succ, mul_comm]

omit [IsUniformSpec spec] in
/-- Possible outputs of `replicate n oa` are lists of length `n` where
each element in the list is a possible output of `oa`. -/
@[simp]
lemma support_replicate :
    support (oa.replicate n) = {xs | xs.length = n ∧ ∀ x ∈ xs, x ∈ support oa} := by
  induction n with
  | zero => ext xs; aesop
  | succ n ih =>
    rw [replicate_succ]
    ext xs
    cases xs with
    | nil => simp
    | cons x xs => rw [cons_mem_support_seq_map_cons_iff, ih]; aesop

@[simp]
lemma mem_finSupport_replicate [spec.DecidableEq] [DecidableEq α]
    (xs : List α) : xs ∈ finSupport (oa.replicate n) ↔
      xs.length = n ∧ ∀ x ∈ xs, x ∈ finSupport oa := by
  simp [mem_finSupport_iff_mem_support]

lemma probOutput_replicate_uniformSample {α : Type} [Fintype α] [SampleableType α]
    {n : ℕ} {xs : List α} (hlen : xs.length = n) :
    Pr[= xs | replicate n ($ᵗ α)] = (↑(Fintype.card α ^ n) : ENNReal)⁻¹ := by
  simp only [probOutput_replicate, hlen, ite_true, probOutput_uniformSample]
  rw [List.prod_map_const, hlen]
  simpa [Nat.cast_pow] using
    (ENNReal.inv_pow (a := (Fintype.card α : ENNReal)) (n := n)).symm

/-! ## SimulateQ distributivity -/

section SimulateQ

variable {ι'} {spec' : OracleSpec ι'} {r : Type v → Type*}
  [Monad r] [LawfulMonad r] (impl : QueryImpl spec r)

omit [IsUniformSpec spec] in
/-- `simulateQ` distributes over `replicate`: simulating a replicated computation
equals running the simulated body `n` times via monadic recursion. -/
lemma simulateQ_replicate :
    simulateQ impl (replicate n oa) =
      (List.replicate n ()).mapM (fun _ => simulateQ impl oa) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replicate_succ_bind, simulateQ_bind, simulateQ_pure,
      List.replicate, List.mapM_cons, ih]

end SimulateQ

section VectorMapM

/-- Index-extraction for `(Vector.ofFn id).mapM` over an `OracleComp`: any element in the
support of the monadic `mapM` has each component lying in the support of the corresponding
inner computation. -/
lemma support_ofFn_mapM_index
    {ι α : Type} {spec : OracleSpec ι} {L : ℕ}
    (f : Fin L → OracleComp spec α)
    {v : Vector α L}
    (hv : v ∈ support ((Vector.ofFn (id : Fin L → Fin L)).mapM f))
    (i : Fin L) : v[i] ∈ support (f i) := by
  simpa using
    Vector.support_mapM_index (Vector.ofFn (id : Fin L → Fin L)) f hv i

end VectorMapM

end OracleComp


