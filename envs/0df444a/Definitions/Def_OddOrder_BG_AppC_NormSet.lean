-- Prove2me | Definitions.Def_OddOrder_BG_AppC_NormSet
-- name    : OddOrder_BG_AppC_NormSet
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:39.160541+00:00
-- url     : https://prove2.me/theorems/b6273892-aa9b-4740-9deb-1a97cd051a21
-- title:
--   Bender–Glauberman Appendix C: the finite-field norm-set argument
-- statement:
--   Develops the finite-field side of Bender–Glauberman Appendix C (pp. 145–152; the Carlip–Wheeler account of Peterfalvi's generators-and-relations argument) on the actual field $\mathbb{F}_{p^q}$ (`GaloisField p q`), rather than the propositional scaffold used elsewhere. Here $p,q$ are primes satisfying condition (A), $\gcd((p^q-1)/(p-1),p-1)=1$, and $N$ is the norm of $\mathbb{F}_{p^q}$ over $\mathbb{F}_p$.
--
--   Main definitions: `normOneUnitOfMemNormSetE` and `normOnePairOfMemNormSetE` (norm-one units and pairs attached to $a\in E$), `normSetETwistedNormOneStep` (Lemma C.3 Step 4, norm-one form), `dSeq` (the sequence $d_k=(k+1)-ka$ of Lemma C.1), `tauIter` (the Möbius iterate $a_{k+1}=(2-a_k)^{-1}$ of Lemma C.1) and `fCubic` (the cubic $f_c(X)=X(X-2)(X-c)+(X-1)$ of Lemma C.2, $q=3$).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_NormSet.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSet.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod

namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- `N(0) = 0` (the `i = 0` factor `0^{p^0} = 0` makes the product vanish). -/
lemma normN_zero [Fact p.Prime] (hq : 0 < q) :
    normN p q (0 : GaloisField p q) = 0 := by
  simp only [normN]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hq) (by simp)

/-- An element of `E` is nonzero (its norm is `1 ≠ 0`). -/
lemma ne_zero_of_mem_normSetE [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : a ≠ 0 := by
  intro h
  have := ha.1
  rw [h, normN_zero p q hq] at this
  exact zero_ne_one this

/-- Coerce an element of `E` to the corresponding norm-one unit. -/
noncomputable def normOneUnitOfMemNormSetE [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) : normOneUnits p q :=
  let u : (GaloisField p q)ˣ := Units.mk0 a (ne_zero_of_mem_normSetE p q hq ha)
  ⟨u, (mem_normOneUnits_iff_normN p q hq.ne' u).mpr ha.1⟩

@[simp] theorem normOneUnitOfMemNormSetE_coe [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) :
    (((normOneUnitOfMemNormSetE p q hq ha : normOneUnits p q) :
        (GaloisField p q)ˣ) : GaloisField p q) = a := by
  rfl

/-- The pair `(a, 2-a)` attached to `a ∈ E`, viewed as a pair of norm-one
units. -/
noncomputable def normOnePairOfMemNormSetE [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) :
    normOneUnits p q × normOneUnits p q :=
  (normOneUnitOfMemNormSetE p q hq ha,
    normOneUnitOfMemNormSetE p q hq (two_sub_mem_normSetE p q ha))

@[simp] theorem normOnePairOfMemNormSetE_fst_coe [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) :
    ((((normOnePairOfMemNormSetE p q hq ha).1 : normOneUnits p q) :
        (GaloisField p q)ˣ) : GaloisField p q) = a := by
  rfl

@[simp] theorem normOnePairOfMemNormSetE_snd_coe [Fact p.Prime] (hq : 0 < q)
    {a : GaloisField p q} (ha : a ∈ normSetE p q) :
    ((((normOnePairOfMemNormSetE p q hq ha).2 : normOneUnits p q) :
        (GaloisField p q)ˣ) : GaloisField p q) = (2 : GaloisField p q) - a := by
  rfl

/-- **BG Appendix C, Lemma C.3, Step 4 norm-one form**: the one-step output
only needs an automorphism of the norm-one unit group, since every element of
`E` has norm `1`. -/
def normSetETwistedNormOneStep [Fact p.Prime] (φ : MulAut (normOneUnits p q)) : Prop :=
  ∀ u : normOneUnits p q,
    (((u : normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q) ∈ normSetE p q →
      (((twistedInv φ u : normOneUnits p q) : (GaloisField p q)ˣ) :
          GaloisField p q) ∈ normSetE p q

/-- The sequence `d_k := (k+1) - k·a = (1-a)·k + 1` of BG Lemma C.1. -/
noncomputable def dSeq [Fact p.Prime] (a : GaloisField p q) (k : ℕ) : GaloisField p q :=
  (k : GaloisField p q) + 1 - (k : GaloisField p q) * a

@[simp] lemma dSeq_zero [Fact p.Prime] (a : GaloisField p q) : dSeq p q a 0 = 1 := by
  simp [dSeq]

/-- The Möbius iterate `a₀ = a`, `a_{k+1} = (2 - aₖ)⁻¹` of BG Lemma C.1. -/
noncomputable def tauIter [Fact p.Prime] (a : GaloisField p q) (k : ℕ) : GaloisField p q :=
  Nat.rec a (fun _ prev => (2 - prev)⁻¹) k

@[simp] lemma tauIter_zero [Fact p.Prime] (a : GaloisField p q) : tauIter p q a 0 = a := rfl

/-- The cubic `f_c(X) = X(X-2)(X-c) + (X-1)` of BG Lemma C.2 (`q = 3`). -/
noncomputable def fCubic (c : ZMod p) : (ZMod p)[X] :=
  X * (X - C 2) * (X - C c) + (X - C 1)

end OddOrder.BG.AppC.NormSet


