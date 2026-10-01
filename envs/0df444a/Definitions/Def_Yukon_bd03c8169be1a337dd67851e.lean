-- Prove2me | Definitions.Def_Yukon_bd03c8169be1a337dd67851e
-- name    : Yukon_bd03c8169be1a337dd67851e
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:53:16.064695+00:00
-- url     : https://prove2.me/theorems/a39e60c9-893e-4b5a-a74f-00221ef7615e
-- title:
--   YukonModule.ArkLib.Data.CodingTheory.BerlekampWelch.ElocPoly.part0
-- statement:
--   Source module ArkLib.Data.CodingTheory.BerlekampWelch.ElocPoly.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/CodingTheory/BerlekampWelch/ElocPoly.lean
--
--   yukon-proof-operation:770bcad36187ce85cb77afa1e632d49c2a5981400d57eff68b60c717ac295cd6
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NzcwYmNhZDM2MTg3Y2U4NWNiNzdhZmExZTYzMmQ0OWMyYTU5ODE0MDBkNTdlZmY2OGI2MGM3MTdhYzI5NWNkNiIsImhhc2giOiJjYzA0MDc3MmYwMmQyMjY5NjcxZjA1ZjVkYjU3MzAxZmI3ZWI0NjkyNDhlNWY0YTExYmVjZjQ5NWI5YTY2MTdjIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9iZDAzYzgxNjliZTFhMzM3ZGQ2Nzg1MWUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Init.Data.List.FinRange
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Mul

import Definitions.Def_Yukon_940a9691b0192ef0397b04a2

import Definitions.Def_Yukon_2d0e6914e1f35ef62dbe39e4

import Definitions.Def_Yukon_06fd17bede7d9846a07acaa7

import Definitions.Def_Yukon_d283689b285597996aeda737

import Definitions.Def_Yukon_27544cfc264ef7c169a23dd9


import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Init
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
set_option backward.isDefEq.respectTransparency.types false
/-! # Berlekamp-Welch Error-Locator Polynomials -/


namespace BerlekampWelch

variable {F : Type} [Field F]
         {m n : ℕ} {p : Polynomial F}
variable [DecidableEq F]

section ElocPoly

open Polynomial

protected noncomputable def ElocPoly (n : ℕ) (ωs f : ℕ → F) (p : Polynomial F) : Polynomial F :=
  List.prod <| (List.range n).map fun i =>
    if f i = p.eval (ωs i)
    then 1
    else X - C (ωs i)

section

open BerlekampWelch (ElocPoly)

variable {ωs f : ℕ → F}

@[simp]
protected lemma elocPoly_zero : ElocPoly 0 ωs f p = 1 := rfl

@[simp]
protected lemma elocPoly_one :
    ElocPoly 1 ωs f p = if f 0 ≠ p.eval (ωs 0) then X - (C (ωs 0)) else 1 := by
  simp [ElocPoly, List.range_succ]

@[simp]
protected lemma elocPoly_two :
    ElocPoly 2 ωs f p =
  if f 1 = eval (ωs 1) p
  then if f 0 = eval (ωs 0) p then 1
       else X - C (ωs 0)
  else if f 0 = eval (ωs 0) p then X - C (ωs 1)
       else (X - C (ωs 0)) * (X - C (ωs 1)) := by
  simp [ElocPoly, List.range_succ]

@[simp]
protected lemma elocPoly_succ :
    ElocPoly (n + 1) ωs f p =
  ElocPoly n ωs f p *
    if f n = p.eval (ωs n)
    then 1
    else X - C (ωs n) := by
  conv_lhs => unfold ElocPoly
  rw [List.range_succ, List.map_append, List.prod_append, ←ElocPoly.eq_def]
  simp

open BerlekampWelch (elocPoly_succ) in
protected lemma roots_of_eloc_poly {x : F}
    (h : (ElocPoly n ωs f p).eval x = 0) :
  ∃ i, i < n ∧ f i ≠ p.eval (ωs i) := by
  induction n generalizing x with
  | zero => aesop
  | succ n ih =>
    rw [elocPoly_succ, Polynomial.eval_mul, mul_eq_zero] at h
    rcases h with heval | heval
    · obtain ⟨i, _⟩ := ih heval
      aesop (add safe [(by existsi i), (by omega)])
    · aesop (add safe (by use n))

protected lemma errors_are_roots_of_elocPoly {i : ℕ}
    (hi : i < n) (h : f i ≠ p.eval (ωs i)) : (ElocPoly n ωs f p).eval (ωs i) = 0 := by
  induction n with
  | zero => aesop
  | succ n ih =>
    by_cases i = n
    · aesop
    · have : i < n := by omega
      aesop

@[simp]
protected lemma elocPoly_ne_zero : ElocPoly n ωs f p ≠ 0 := by
  induction n with
  | zero => simp
  | succ n hn => aesop (add simp [sub_eq_zero]) (add safe forward (Polynomial.X_ne_C (ωs n)))

@[simp]
protected lemma elocPoly_leading_coeff_one : (ElocPoly n ωs f p).leadingCoeff = 1 := by
  induction n with
  | zero => simp
  | succ n _ => aesop

section

open Fin

protected lemma elocPoly_congr {ωs' f' : ℕ → F}
    (h₁ : ∀ {m}, m < n → ωs m = ωs' m) (h₂ : ∀ {m}, m < n → f m = f' m) :
  ElocPoly n ωs f = ElocPoly n ωs' f' := by
  ext p
  unfold ElocPoly
  rw [
    ←List.pmap_eq_map (p := (·<n)) (H := by simp),
    ←List.pmap_eq_map (p := (·<n)) (H := by simp),
    List.pmap_eq_map_attach, List.pmap_eq_map_attach
  ]
  aesop (add simp List.mem_range)

open BerlekampWelch (elocPoly_congr)

noncomputable def ElocPolyF (ωs f : Fin n → F) (p : Polynomial F) : Polynomial F :=
  ElocPoly n (liftF ωs) (liftF f) p

@[simp]
protected lemma elocPolyF_eq_elocPoly :
    ElocPolyF (n := n) (liftF' ωs) (liftF' f) = ElocPoly n ωs f :=
  elocPoly_congr liftF_liftF'_of_lt liftF_liftF'_of_lt

@[simp]
protected lemma elocPolyF_eq_elocPoly' {ωs f : Fin n → F} :
    ElocPolyF ωs f p = ElocPoly n (liftF ωs) (liftF f) p := rfl

protected lemma elocPoly_leftF_leftF_eq_contract {ωs f : Fin m → F} :
    ElocPoly n (liftF ωs) (liftF f) =
  ElocPoly n (contract n ωs) (contract n f) := by
  rw [elocPoly_congr contract_eq_liftF_of_lt contract_eq_liftF_of_lt]

protected lemma elocPolyF_ne_zero {ωs f : Fin m → F} :
    ElocPolyF ωs f p ≠ 0 := by
  aesop (add simp [BerlekampWelch.elocPoly_ne_zero])

protected lemma errors_are_roots_of_elocPolyF {i : Fin n} {ωs f : Fin n → F}
    (h : f i ≠ p.eval (ωs i)) : (ElocPolyF ωs f p).eval (ωs i) = 0 := by
  rw [←liftF_eval (f := ωs)]
  aesop (config := {warnOnNonterminal := false})
  rw [BerlekampWelch.errors_are_roots_of_elocPoly
    (i.isLt)
    (by aesop (add simp [liftF_eval]))]

@[simp]
protected lemma elocPolyF_leading_coeff_one {ωs f : Fin n → F} :
    (ElocPolyF ωs f p).leadingCoeff = 1 := by
  aesop

open BerlekampWelch
  (elocPolyF_eq_elocPoly' elocPoly_leftF_leftF_eq_contract
   elocPoly_zero elocPoly_succ)
open Fin

@[simp]
lemma elocPolyF_deg {ωs f : Fin n → F} : (ElocPolyF ωs f p).natDegree = Δ₀(f, p.eval ∘ ωs) := by
  rw [elocPolyF_eq_elocPoly']
  induction n with
  | zero =>
    simp only [elocPoly_zero, natDegree_one, hamming_zero_eq_dist]
    exact funext_iff.2 (Fin.elim0 ·)
  | succ n ih =>
    rw [
      elocPoly_succ,
      natDegree_mul (by simp)
                    (by aesop (erase simp liftF_succ)
                              (add simp [sub_eq_zero])
                              (add safe forward (X_ne_C (liftF ωs n)))),
      elocPoly_leftF_leftF_eq_contract
    ]
    aesop (config := {warnOnNonterminal := false}) (add simp [
      hammingDist.eq_def, Finset.card_filter, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ
    ]) <;> (apply Finset.sum_congr rfl; aesop (add safe (by omega)))

end

end

end ElocPoly

end BerlekampWelch


