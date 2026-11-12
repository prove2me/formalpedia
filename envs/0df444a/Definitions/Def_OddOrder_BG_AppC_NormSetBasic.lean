-- Prove2me | Definitions.Def_OddOrder_BG_AppC_NormSetBasic
-- name    : OddOrder_BG_AppC_NormSetBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:30.075204+00:00
-- url     : https://prove2.me/theorems/a1ad2845-af63-440e-bd76-52cbd8ec24c6
-- title:
--   Bender–Glauberman Appendix C: the norm set, basics and the Frobenius product
-- statement:
--   The first part of the Bender–Glauberman Appendix C formalization: the norm and the norm set with their basic algebra, Remark (I) (condition (A) is equivalent to $q\nmid(p-1)$), finite-field helper lemmas, Frobenius stability of the norm set (Lemma C.3 Step 4), and the Frobenius semidirect product $P\rtimes U$ used for Lemmas C.2 and C.3.
--
--   Main definitions: `normN` (the norm $N(x)$ from $\mathbb{F}_{p^q}$ to $\mathbb{F}_p$), `normSetE` ($E=\{a: N(a)=N(2-a)=1\}$), `normOneUnits` (Remark (VII): the subgroup $U$ of units of norm $1$), `primeFieldUnits`, and the pair sets `normOnePairSet` and `normOnePairSetAt` for Lemma C.2.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_NormSetBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
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

/-- **BG App C norm** `N(x)`: the norm of `x ∈ 𝔽_{p^q}` over `𝔽_p`, written as the
product of its Frobenius conjugates `∏_{i<q} x^{p^i}` (this equals
`Algebra.norm (ZMod p) x`). -/
noncomputable def normN [Fact p.Prime] (x : GaloisField p q) : GaloisField p q :=
  ∏ i ∈ Finset.range q, x ^ (p ^ i)

/-- **BG App C norm set** `E = { a ∈ 𝔽_{p^q} | N(a) = N(2-a) = 1 }` (mmd L4853). -/
def normSetE [Fact p.Prime] : Set (GaloisField p q) :=
  {a | normN p q a = 1 ∧ normN p q (2 - a) = 1}

@[simp] lemma normN_one [Fact p.Prime] : normN p q (1 : GaloisField p q) = 1 := by
  simp [normN]

/-- The product definition `normN` agrees with the mathlib finite-field norm after
embedding `𝔽_p` into `𝔽_{p^q}`.  This is the bridge needed for the norm-one
subgroup `U` used in BG Appendix C, Remark (VII). -/
lemma normN_eq_algebraMap_norm [Fact p.Prime] (hq : q ≠ 0) (x : GaloisField p q) :
    normN p q x = algebraMap (ZMod p) (GaloisField p q) (Algebra.norm (ZMod p) x) := by
  simpa [normN, GaloisField.finrank p hq, Nat.card_zmod]
    using (FiniteField.algebraMap_norm_eq_prod_pow
      (ZMod p) (GaloisField p q) x).symm

/-- **BG Appendix C, Remark (VII)**: the subgroup
`U = {x ∈ 𝔽_{p^q}ˣ | N(x)=1}` of norm-one units. -/
noncomputable def normOneUnits [Fact p.Prime] : Subgroup (GaloisField p q)ˣ :=
  (Units.map (Algebra.norm (ZMod p) (S := GaloisField p q))).ker

/-- The subgroup of `𝔽_{p^q}ˣ` consisting of units coming from the prime field
`𝔽_pˣ`.  Under condition (A), BG Appendix C Remark (VII) uses this subgroup
together with `U` to decompose `𝔽_{p^q}ˣ`. -/
noncomputable def primeFieldUnits [Fact p.Prime] : Subgroup (GaloisField p q)ˣ :=
  (Units.map ((algebraMap (ZMod p) (GaloisField p q)).toMonoidHom)).range

lemma mem_normOneUnits_iff_normN [Fact p.Prime] (hq : q ≠ 0)
    (u : (GaloisField p q)ˣ) :
    u ∈ normOneUnits p q ↔ normN p q (u : GaloisField p q) = 1 := by
  constructor
  · intro hu
    have hbase : Algebra.norm (ZMod p) (u : GaloisField p q) = 1 :=
      congrArg Units.val hu
    rw [normN_eq_algebraMap_norm p q hq, hbase, map_one]
  · intro hu
    ext
    apply (algebraMap (ZMod p) (GaloisField p q)).injective
    change algebraMap (ZMod p) (GaloisField p q)
        (Algebra.norm (ZMod p) (u : GaloisField p q)) =
      algebraMap (ZMod p) (GaloisField p q) (1 : ZMod p)
    rw [← normN_eq_algebraMap_norm p q hq, hu, map_one]

/-- The pair set `{(u, v) ∈ U × U | u + v = 2}` whose cardinality is the
structure constant identified with `|E|` in BG Appendix C, Lemma C.2. -/
def normOnePairSet [Fact p.Prime] : Set (normOneUnits p q × normOneUnits p q) :=
  {uv | (((uv.1 : (GaloisField p q)ˣ) : GaloisField p q) +
      ((uv.2 : (GaloisField p q)ˣ) : GaloisField p q)) = 2}

/-- The BG Appendix C, Lemma C.2 pair set at a nonzero additive element `s`: pairs
`(u, v) ∈ U × U` satisfying `u * s + v * s = 2 * s`.  BG identifies the
cardinality of this set with the structure constant of a class-sum product in
the Frobenius group `H = P ⋊ U`. -/
def normOnePairSetAt [Fact p.Prime] (s : GaloisField p q) :
    Set (normOneUnits p q × normOneUnits p q) :=
  {uv | (((uv.1 : (GaloisField p q)ˣ) : GaloisField p q) * s +
      ((uv.2 : (GaloisField p q)ˣ) : GaloisField p q) * s) = 2 * s}

/-- `E` is symmetric under `a ↦ 2 - a` (the two norm conditions just swap). -/
lemma two_sub_mem_normSetE [Fact p.Prime] {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : (2 - a) ∈ normSetE p q := by
  refine ⟨ha.2, ?_⟩
  rw [show (2 : GaloisField p q) - (2 - a) = a by ring]
  exact ha.1

/-- **BG Appendix C, Lemma C.3, Step 4**: in characteristic `p`, Frobenius
turns a two-term sum into the sum of `p`-th powers. -/
lemma add_pow_p [Fact p.Prime] (a b : GaloisField p q) :
    a ^ p + b ^ p = (a + b) ^ p := by
  have h := map_add (frobenius (GaloisField p q) p) a b
  simpa [frobenius_def] using h.symm

/-- The twisted-inverse map attached to an automorphism `φ`: `x ↦ φ(x⁻¹)`.
This is the abstract form of the last induction in BG Appendix C, Lemma C.3. -/
def twistedInv {α : Type*} [Group α] (φ : MulAut α) (x : α) : α := φ x⁻¹

@[simp] lemma twistedInv_twistedInv {α : Type*} [Group α] (φ : MulAut α)
    (x : α) :
    twistedInv φ (twistedInv φ x) = (φ ^ 2) x := by
  simp [twistedInv, pow_two]

/-- The additive group of `𝔽_{p^q}`, written multiplicatively so it can be the
kernel factor in mathlib's `SemidirectProduct`. -/
abbrev additiveFieldGroup [Fact p.Prime] := Multiplicative (GaloisField p q)

/-- The action of the norm-one subgroup `U` on the additive group `P = 𝔽_{p^q}`:
`u` sends `s` to `u * s`.  This is the action used in the Frobenius group
`H = P ⋊ U` in BG Appendix C, Lemma C.2. -/
noncomputable def normOneMulAction [Fact p.Prime] :
    normOneUnits p q →* MulAut (additiveFieldGroup p q) :=
  (MulAutMultiplicative (GaloisField p q)).symm.toMonoidHom.comp
    ((AddAut.mulLeft :
        (GaloisField p q)ˣ →* Multiplicative (AddAut (GaloisField p q))).comp
      (normOneUnits p q).subtype)

/-- The concrete Frobenius group `H = P ⋊ U` from BG Appendix C, Lemma C.2, with
`P` the additive group of `𝔽_{p^q}` and `U` the norm-one subgroup. -/
abbrev normOneFrobeniusGroup [Fact p.Prime] :=
  additiveFieldGroup p q ⋊[normOneMulAction p q] normOneUnits p q

/-- The additive kernel `P` in the concrete Frobenius group `H = P ⋊ U`. -/
noncomputable def normOneFrobeniusKernel [Fact p.Prime] :
    Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q).range

/-- The norm-one complement `U` in the concrete Frobenius group `H = P ⋊ U`. -/
noncomputable def normOneFrobeniusComplement [Fact p.Prime] :
    Subgroup (normOneFrobeniusGroup p q) :=
  (SemidirectProduct.inr : normOneUnits p q →* normOneFrobeniusGroup p q).range

@[simp] theorem normOneMulAction_apply [Fact p.Prime] (u : normOneUnits p q)
    (s : GaloisField p q) :
    ((normOneMulAction p q u) (Multiplicative.ofAdd s)).toAdd =
      ((u : (GaloisField p q)ˣ) : GaloisField p q) * s := by
  rfl

/-- The additive subgroup `W ≤ P` inside the concrete Frobenius group `P ⋊ U`. -/
noncomputable def normOneFrobeniusSubspaceKernel [Fact p.Prime]
    (W : Submodule (ZMod p) (GaloisField p q)) :
    Subgroup (normOneFrobeniusGroup p q) :=
  W.toAddSubgroup.toSubgroup.map
    (SemidirectProduct.inl : additiveFieldGroup p q →* normOneFrobeniusGroup p q)

/-- Membership in the embedded additive subspace is exactly membership in `W`. -/
@[simp] theorem mem_normOneFrobeniusSubspaceKernel_inl [Fact p.Prime]
    (W : Submodule (ZMod p) (GaloisField p q)) (s : GaloisField p q) :
    (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈
      normOneFrobeniusSubspaceKernel p q W ↔ s ∈ W := by
  unfold normOneFrobeniusSubspaceKernel
  constructor
  · intro h
    rcases h with ⟨x, hxW, hx⟩
    have hx' : x = Multiplicative.ofAdd s := SemidirectProduct.inl_injective hx
    simpa [hx'] using hxW
  · intro hs
    exact ⟨Multiplicative.ofAdd s, by simpa using hs, rfl⟩

/-- Additive-kernel preimage of a subgroup `X ≤ P ⋊ U`. -/
noncomputable def normOneFrobeniusKernelPreimageAddSubgroup [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q)) : AddSubgroup (GaloisField p q) where
  carrier := {s | (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈ X}
  zero_mem' := by
    simp
  add_mem' := by
    intro a b ha hb
    have hmul := X.mul_mem ha hb
    simpa [← map_mul, ofAdd_add] using hmul
  neg_mem' := by
    intro a ha
    have hinv := X.inv_mem ha
    simpa using hinv

/-- The additive-kernel preimage of `X ≤ P ⋊ U`, viewed as an `𝔽_p`-subspace. -/
noncomputable def normOneFrobeniusKernelPreimageSubmodule [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q)) : Submodule (ZMod p) (GaloisField p q) :=
  AddSubgroup.toZModSubmodule (n := p) (normOneFrobeniusKernelPreimageAddSubgroup p q X)

/-- Membership in the kernel-preimage subspace is membership of the corresponding
embedded additive element in `X`. -/
@[simp] theorem mem_normOneFrobeniusKernelPreimageSubmodule [Fact p.Prime]
    (X : Subgroup (normOneFrobeniusGroup p q)) (s : GaloisField p q) :
    s ∈ normOneFrobeniusKernelPreimageSubmodule p q X ↔
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : normOneFrobeniusGroup p q) ∈ X := by
  rfl

end OddOrder.BG.AppC.NormSet


