-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
-- name    : OddOrder_Peterfalvi_S15_CharacterDegreeSupply
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:01:02.371207+00:00
-- url     : https://prove2.me/theorems/68fedfdb-484d-4a86-8f14-4339d05c8eeb
-- title:
--   Peterfalvi (13.3.b)/(13.4): the dichotomy supplies
-- statement:
--   Formalizes the `LambdaWitness`/`ThetaWitness` dichotomy layer of Peterfalvi (13.3.b)/(13.4) (pp. 75-86).
--
--   Main declarations: `LambdaWitness` (The `𝒮₁`-λ-witness predicate); `ThetaWitness` (The `T`-side (13.3.b) witness shape).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The `𝒮₁`-λ-witness predicate** (Pf (13.3.b)): `𝒮` contains a `uq`-degree `PC`-induced
irreducible — a linear `θ ∈ Irr(H.subgroupOf S)` with `P ⊄ Ker θ` whose induction is
irreducible.  Its existence is the conditional branch of the (13.3.b) dichotomy
(`lambdaClusterData_of_irr_witness` packages it into `LambdaClusterData`); its failure is the
Galois/`C = ⊥` case. -/
def LambdaWitness [Finite G] (hyp : Hypothesis (G := G)) : Prop :=
  haveI := hyp.finiteG
  ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
    OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
    ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)

open scoped FiniteInduce in
/-- **The `T`-side (13.3.b) witness shape**: a linear character of `K = QD` not containing
`Q` in its kernel whose induction to `T` is irreducible (a `vp`-degree `QD`-linear induced
irreducible).  Mirror of `LambdaWitness`. -/
def ThetaWitness [Finite G] (hyp : Hypothesis (G := G)) : Prop :=
  haveI := hyp.finiteG
  ∃ θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ,
    OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
    ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.K.subgroupOf hyp.T) :
        Set ↥(hyp.K.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) ∧
    OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ)

end OddOrder.Peterfalvi.S15


