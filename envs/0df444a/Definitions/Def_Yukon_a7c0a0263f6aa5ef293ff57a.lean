-- Prove2me | Definitions.Def_Yukon_a7c0a0263f6aa5ef293ff57a
-- name    : Yukon_a7c0a0263f6aa5ef293ff57a
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:38.880978+00:00
-- url     : https://prove2.me/theorems/f51b3bb6-a0b3-429f-b2c0-db0232940186
-- title:
--   YukonModule.VCVio.OracleComp.Constructions.BitVec.part0
-- statement:
--   Source module VCVio.OracleComp.Constructions.BitVec.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/Constructions/BitVec.lean
--
--   yukon-proof-operation:a908a5e07c03a327cd9b41fd1f9fef54e8efc2f1cc4846adb016335c263801e8
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YTkwOGE1ZTA3YzAzYTMyN2NkOWI0MWZkMWY5ZmVmNTRlOGVmYzJmMWNjNDg0NmFkYjAxNjMzNWMyNjM4MDFlOCIsImhhc2giOiIyZWE4NWU5OTI1MWViOGI2Y2FmYTU3ZmM1ODhlOWNmYTk3ODYyYTY2ZWUxODAxNWZmMjYwMjg3ODU5ZDlkOTVhIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9hN2MwYTAyNjNmNmFhNWVmMjkzZmY1N2EiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7

public import Definitions.Def_Yukon_cda3959af6f436acfe6b2dff

public import Definitions.Def_Yukon_2e7e800d480cc4c5ab2a0a15



public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Init
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Vector.Defs
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.List.Sym
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
meta import Definitions.Def_Yukon_cda3959af6f436acfe6b2dff
meta import Definitions.Def_Yukon_2e7e800d480cc4c5ab2a0a15
meta import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
set_option backward.isDefEq.respectTransparency.types false
/-!
# Probability lemmas for uniform `BitVec` sampling

Lemmas about `probOutput` for `ProbComp (BitVec n)` computations involving XOR with
uniformly sampled keys. These are reusable building blocks for encryption proofs
(e.g., one-time pad privacy).
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

lemma probOutput_xor_uniform (sp : ℕ) (msg σ : BitVec sp) :
    Pr[= σ | (fun k : BitVec sp => k ^^^ msg) <$> ($ᵗ BitVec sp)] =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[= σ | (fun k : BitVec sp => k ^^^ msg) <$> ($ᵗ BitVec sp)] =
        Pr[= σ | (msg ^^^ ·) <$> ($ᵗ BitVec sp)] := by
          simp [BitVec.xor_comm]
    _ = Pr[= msg ^^^ σ | ($ᵗ BitVec sp)] := by simp
    _ = (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
          simp [probOutput_uniformSample]

lemma probOutput_pair_xor_uniform (sp : ℕ) (mx : ProbComp (BitVec sp))
    (msg σ : BitVec sp) :
    Pr[= (msg, σ) | do
      let msg' ← mx
      let k ← $ᵗ BitVec sp
      return (msg', k ^^^ msg')] =
      Pr[= msg | mx] * (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  let inv : ℝ≥0∞ := (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹
  rw [probOutput_bind_eq_tsum]
  have hinner (msg' : BitVec sp) :
      Pr[= (msg, σ) | do
        let k ← $ᵗ BitVec sp
        return (msg', k ^^^ msg')] = if msg = msg' then inv else 0 := by
    calc
      Pr[= (msg, σ) | do
        let k ← $ᵗ BitVec sp
        return (msg', k ^^^ msg')] =
          Pr[= (msg, σ) |
            (msg', ·) <$> ((fun k : BitVec sp => k ^^^ msg') <$> ($ᵗ BitVec sp))] := by
            simp
      _ = if msg = msg' then
          Pr[= σ | (fun k : BitVec sp => k ^^^ msg') <$> ($ᵗ BitVec sp)] else 0 := by
            simpa using
              (probOutput_prod_mk_snd_map
                (my := (fun k : BitVec sp => k ^^^ msg') <$> ($ᵗ BitVec sp))
                (x := msg') (z := (msg, σ)))
      _ = if msg = msg' then inv else 0 := by
            by_cases h : msg = msg' <;> simp [h, inv, probOutput_xor_uniform]
  simp_rw [hinner]
  calc
    ∑' msg', Pr[= msg' | mx] * (if msg = msg' then inv else 0) =
        ∑' msg', (Pr[= msg' | mx] * (if msg = msg' then 1 else 0)) * inv := by
          refine tsum_congr fun msg' => ?_
          by_cases h : msg = msg' <;> simp [h, inv, mul_comm]
    _ = (∑' msg', Pr[= msg' | mx] * (if msg = msg' then 1 else 0)) * inv := by
          rw [ENNReal.tsum_mul_right]
    _ = Pr[= msg | mx] * inv := by simp

lemma probOutput_cipher_from_pair_uniform (sp : ℕ) (mx : ProbComp (BitVec sp))
    (σ : BitVec sp) :
    Pr[= σ | do
      let msg' ← mx
      let k ← $ᵗ BitVec sp
      return (k ^^^ msg')] =
      (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_bind_of_const (mx := mx)
    (y := σ) (r := (Fintype.card (BitVec sp) : ℝ≥0∞)⁻¹)]
  · simp
  · intro msg hmsg
    simpa using probOutput_xor_uniform sp msg σ


