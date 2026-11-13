-- Prove2me | Definitions.Def_OddOrder_BG_AppC_FrobeniusClassSum
-- name    : OddOrder_BG_AppC_FrobeniusClassSum
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:37:50.417422+00:00
-- url     : https://prove2.me/theorems/7b2624ae-f401-4b8d-9812-9c5577cd66b0
-- title:
--   BG Appendix C: the Frobenius class-sum bridge (Lemma C.2)
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Appendix C, Lemma C.2, pp. 145-152. This file connects the finite-field pair set to the conjugacy-class language used by the class-sum structure constants; it is the first class-sum-dependent layer for the $q\ge5$ branch of Lemma C.2.
--
--   Main definitions: `normOneClassAt` (the conjugacy class in $H=P\rtimes U$ of an additive-kernel element), `IsFixedProductClassPair` and `fixedProductClassPairSet` (fixed-product class pairs), `classPairSet`, `normOneFrobeniusKernelCharacterPred` and `normOneFrobeniusClassSumConcreteTerm` (the concrete summand of the $C_1*C_1\to C_2$ class-sum character formula).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_FrobeniusClassSum.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_FrobeniusClassSum.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_Mathlib_SemidirectProduct
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems
import Definitions.Def_OddOrder_BG_AppC_NormOneInduce
import Mathlib.Data.Set.Card.Arithmetic

namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable (p q : ℕ)

/-- The conjugacy class in `H = P ⋊ U` of the additive-kernel element attached to
`s ∈ 𝔽_{p^q}`.  BG Lemma C.2 uses the class of a nonzero `s ∈ P`. -/
noncomputable def normOneClassAt [Fact p.Prime] (s : GaloisField p q) :
    ConjClasses (normOneFrobeniusGroup p q) :=
  ConjClasses.mk
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q)

/-- Fixed-product version of `IsClassPair`: the two entries lie in prescribed
classes and their product is the chosen representative `z`, not merely an
element conjugate to `z`.  This is the fiber counted by the finite-field pair
set before multiplying by the size of the product conjugacy class. -/
def IsFixedProductClassPair [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q)
    (r : normOneFrobeniusGroup p q × normOneFrobeniusGroup p q) : Prop :=
  ConjClasses.mk r.1 = Ci ∧ ConjClasses.mk r.2 = Cj ∧ r.1 * r.2 = z

/-- The set of fixed-product class pairs. -/
def fixedProductClassPairSet [Fact p.Prime]
    (Ci Cj : ConjClasses (normOneFrobeniusGroup p q))
    (z : normOneFrobeniusGroup p q) :
    Set (normOneFrobeniusGroup p q × normOneFrobeniusGroup p q) :=
  {r | IsFixedProductClassPair (p := p) (q := q) Ci Cj z r}

/-- Set version of the class-pair predicate, used to partition the full
class-sum pair count by exact product. -/
def classPairSet [Fact p.Prime]
    (Ci Cj Cs : ConjClasses (normOneFrobeniusGroup p q)) :
    Set (normOneFrobeniusGroup p q × normOneFrobeniusGroup p q) :=
  {r | IsClassPair Ci Cj Cs r}

/-- Predicate selecting irreducible characters whose kernel contains the additive
kernel of the concrete Frobenius group. -/
def normOneFrobeniusKernelCharacterPred [Fact p.Prime]
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q)) : Prop :=
  (normOneFrobeniusKernel p q : Set (normOneFrobeniusGroup p q)) ⊆
    OddOrder.Peterfalvi.S03.characterKernel
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)

/-- The concrete summand in the `C_1 * C_1 -> C_2` class-sum character formula. -/
noncomputable def normOneFrobeniusClassSumConcreteTerm [Fact p.Prime]
    (χ : IrreducibleCharacter (normOneFrobeniusGroup p q)) : ℂ :=
  (((Nat.card (normOneUnits p q) : ℂ) *
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
          normOneFrobeniusGroup p q) *
    ((Nat.card (normOneUnits p q) : ℂ) *
      (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
        (SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q)) :
          normOneFrobeniusGroup p q))) /
    (χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (1 : normOneFrobeniusGroup p q)) *
    star ((χ : ClassFunction (normOneFrobeniusGroup p q) ℂ)
      (SemidirectProduct.inl (Multiplicative.ofAdd (2 : GaloisField p q)) :
        normOneFrobeniusGroup p q))

open scoped Classical in
/-- The non-kernel-character error term in the concrete `C_1 * C_1 -> C_2`
class-sum formula. -/
noncomputable def normOneFrobeniusNonKernelContribution [Fact p.Prime] : ℂ :=
  ∑ χ ∈ Finset.univ.filter
      (fun χ : IrreducibleCharacter (normOneFrobeniusGroup p q) =>
        ¬ normOneFrobeniusKernelCharacterPred p q χ),
    normOneFrobeniusClassSumConcreteTerm p q χ

end OddOrder.BG.AppC.NormSet


