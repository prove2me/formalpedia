-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumSections
-- name    : OddOrder_GroupTheory_RepresentationTheory_ClassSumSections
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:17.963206+00:00
-- url     : https://prove2.me/theorems/3a1315ab-42a6-41a4-9434-2b89078f7353
-- title:
--   Class sums: indexing, structure coefficients, and the pair action
-- statement:
--   Part of the class-sum congruence development: the indexing of class sums, the structure coefficients $a_{ijs}$ expressing a product of two class sums as an integer combination of class sums (Isaacs §3; Peterfalvi (6.7)), the structure coefficient at the identity, and the action on the pair set $\Omega=\{(u,v)\in C_i\times C_j : uv\in C_s\}$ of Peterfalvi (6.7.1).
--
--   Main definitions: `classSumCoeff` (the structure coefficient $a_{ijs}$, counting ordered pairs $(u,v)$ with product in a given class) and `IsClassPair` (the defining predicate of the pair set $\Omega$). Lemmas include the product formula `classSum_mul` and conjugation-invariance of the pair predicate.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ClassSumSections.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ClassSumSections.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumCore
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_Algebra_AlgInt
import Definitions.Def_OddOrder_GroupTheory_FreeActionOrbitCount
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_AbsolutelyIrreducible
import Definitions.Def_OddOrder_GroupTheory_ConjClassCardinality
import Definitions.Def_OddOrder_Mathlib_Sylow
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.RationalRoot

namespace OddOrder.RepresentationTheory

open scoped MonoidAlgebra

open OddOrder.GroupTheory.CenterClassSum

open Module (finrank)

open Representation

variable {G : Type*} [Group G]

section StructureCoeff

variable [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)]

/-- The **structure coefficient** `a_{ijs}`: the number of ordered pairs `(u, v)` with `u ∈ C_i`,
`v ∈ C_j`, and `u·v ∈ C_s`.  These are the natural numbers in Peterfalvi's `C_i · C_j = ∑_s a_{ijs}
· C_s` (note that the coefficient of the *class sum* `C_s` in that combination is `a_{ijs}/|C_s|`;
the unscaled `a_{ijs}` counts pairs over the whole class). -/
noncomputable def classSumCoeff (Ci Cj Cs : ConjClasses G) : ℕ :=
  (Finset.univ.filter (fun p : G × G =>
    ConjClasses.mk p.1 = Ci ∧ ConjClasses.mk p.2 = Cj ∧ ConjClasses.mk (p.1 * p.2) = Cs)).card

/-- **Coefficient of a product of class sums at a group element.** The coefficient of `w` in
`classSum Ci * classSum Cj` is the number of factorizations `w = u·v` with `u ∈ C_i` and `v ∈ C_j`.
(This per-element count is constant on each conjugacy class; summing it over a class `C_s` recovers
the structure coefficient `classSumCoeff Ci Cj Cs`.) -/
theorem classSum_mul_apply {k : Type*} [CommRing k] (Ci Cj : ConjClasses G) (w : G) :
    (classSum Ci * classSum Cj : k[G]).coeff w =
      (Finset.univ.filter (fun p : G × G =>
        ConjClasses.mk p.1 = Ci ∧ ConjClasses.mk p.2 = Cj ∧ p.1 * p.2 = w)).card := by
  classical
  -- Expand the product coefficient over all pairs `(u, v)` with `u * v = w`.
  have hexp := MonoidAlgebra.coeff_mul_antidiag (classSum (k := k) Ci) (classSum (k := k) Cj) w
    (Finset.univ.filter (fun p : G × G => p.1 * p.2 = w)) (by intro p; simp)
  rw [hexp]
  -- Each summand is the product of two `0/1` indicators; combine into a single indicator.
  have hbody : ∀ p : G × G,
      (classSum (k := k) Ci).coeff p.1 * (classSum (k := k) Cj).coeff p.2
        = if ConjClasses.mk p.1 = Ci ∧ ConjClasses.mk p.2 = Cj then (1 : k) else 0 := by
    intro p
    rw [coeff_classSum, coeff_classSum, ite_and]
    by_cases h1 : ConjClasses.mk p.1 = Ci <;> by_cases h2 : ConjClasses.mk p.2 = Cj <;>
      simp [h1, h2]
  rw [Finset.sum_congr rfl (fun p _ => hbody p)]
  -- Sum of a `0/1` indicator over the antidiagonal is the cardinality of the counted set.
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine congrArg Nat.cast (congrArg Finset.card (Finset.ext fun p => ?_))
  show p ∈ _ ↔ p ∈ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, hi, hj⟩; exact ⟨hi, hj, hw⟩
  · rintro ⟨hi, hj, hw⟩; exact ⟨hw, hi, hj⟩

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] in
/-- The conjugacy class of `h * g * h⁻¹` is the same as that of `g`. -/
private theorem mk_conj_eq (h g : G) : ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h⁻¹, by group⟩)

omit [DecidableEq G] in
/-- The per-element product coefficient `(classSum Ci * classSum Cj : ℂ[G]).coeff w` is a **class
function** of `w`: conjugating `w` by any group element leaves the number of factorizations
unchanged.  (The bijection `(u, v) ↦ (h u h⁻¹, h v h⁻¹)` preserves the class of each factor and
maps `u·v = w` to `(h u h⁻¹)·(h v h⁻¹) = h w h⁻¹`.) -/
theorem classSum_mul_apply_conj (Ci Cj : ConjClasses G) (h w : G) :
    (classSum Ci * classSum Cj : ℂ[G]).coeff (h * w * h⁻¹)
      = (classSum Ci * classSum Cj : ℂ[G]).coeff w := by
  classical
  rw [classSum_mul_apply, classSum_mul_apply]
  norm_cast
  -- `i` sends a factorization of `h·w·h⁻¹` to one of `w` by conjugating *down* by `h`.
  refine Finset.card_nbij' (fun p => (h⁻¹ * p.1 * h, h⁻¹ * p.2 * h))
    (fun p => (h * p.1 * h⁻¹, h * p.2 * h⁻¹)) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hi, hj, huv⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · rw [show h⁻¹ * u * h = h⁻¹ * u * h⁻¹⁻¹ by group, mk_conj_eq, hi]
    · rw [show h⁻¹ * v * h = h⁻¹ * v * h⁻¹⁻¹ by group, mk_conj_eq, hj]
    · rw [show h⁻¹ * u * h * (h⁻¹ * v * h) = h⁻¹ * (u * v) * h by group, huv]; group
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hi, hj, huv⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · rw [mk_conj_eq, hi]
    · rw [mk_conj_eq, hj]
    · rw [show h * u * h⁻¹ * (h * v * h⁻¹) = h * (u * v) * h⁻¹ by group, huv]
  · rintro ⟨u, v⟩ _; simp only [Prod.mk.injEq]; constructor <;> group
  · rintro ⟨u, v⟩ _; simp only [Prod.mk.injEq]; constructor <;> group

omit [DecidableEq G] in
set_option backward.isDefEq.respectTransparency false in
/-- The per-element product coefficient equals the count taken at the chosen class representative
`(ConjClasses.mk w).out`. -/
theorem classSum_mul_apply_out (Ci Cj : ConjClasses G) (w : G) :
    (classSum Ci * classSum Cj : ℂ[G]).coeff w
      = (classSum Ci * classSum Cj : ℂ[G]).coeff (ConjClasses.mk w).out := by
  classical
  -- `(mk w).out` is conjugate to `w`, so write it as `h * w * h⁻¹` and apply class-invariance.
  have hmk : ConjClasses.mk (ConjClasses.mk w).out = ConjClasses.mk w := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  have hconj : IsConj w (ConjClasses.mk w).out :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hmk.symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  rw [← hc, classSum_mul_apply_conj]

variable [Fintype (ConjClasses G)]

omit [DecidableEq G] in
/-- **Product of class sums as an integer combination of class sums** (Isaacs §3; Peterfalvi
(6.7.2)): `C_i · C_j = ∑_s a_{ijs}^∘ · C_s`, where the coefficient of `C_s` is the per-element
factorization count `(classSum Ci * classSum Cj : ℂ[G]).coeff (out C_s)` — a natural number that is
*constant* on the class (this is the coefficient that is actually consistent with
`classSum_mul_apply`, **not** the pair-count `classSumCoeff` divided by `|C_s|`). -/
theorem classSum_mul (Ci Cj : ConjClasses G) :
    (classSum Ci * classSum Cj : ℂ[G]) =
      ∑ Cs : ConjClasses G,
        ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) • classSum Cs := by
  classical
  -- Compare coefficients at an arbitrary group element `w`.
  ext w
  -- Push the coefficient evaluation `· w` through the finite sum.
  rw [MonoidAlgebra.coeff_finsetSum]
  -- RHS coefficient at `w`: only the `Cs = mk w` term survives, contributing `κ((mk w).out)`.
  have hterm : ∀ Cs : ConjClasses G,
      (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) • classSum Cs).coeff w
        = if Cs = ConjClasses.mk w then (classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out else 0 := by
    intro Cs
    rw [MonoidAlgebra.coeff_smul_apply, coeff_classSum, smul_eq_mul]
    by_cases hCs : ConjClasses.mk w = Cs
    · rw [if_pos hCs, if_pos hCs.symm, mul_one]
    · rw [if_neg hCs, if_neg (fun h => hCs h.symm), mul_zero]
  rw [Finset.sum_congr rfl (fun Cs _ => hterm Cs),
    Finset.sum_ite_eq' Finset.univ (ConjClasses.mk w)
      (fun Cs => (classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out)]
  rw [if_pos (Finset.mem_univ _)]
  exact classSum_mul_apply_out Ci Cj w

end StructureCoeff

section StructureCoeffAtIdentity

/-- `mk w = 1` (the identity conjugacy class) iff `w = 1`. -/
theorem mk_eq_one_iff_eq_one {w : G} : ConjClasses.mk w = 1 ↔ w = 1 := by
  rw [ConjClasses.one_eq_mk_one, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left]

variable [Fintype G] [DecidableEq (ConjClasses G)]

/-- **Peterfalvi (6.7.3), structure constant `a_{ij0} = 0`.** The coefficient of the *identity*
class in `classSumCoeff Ci Cj 1` counts ordered pairs `(u, v)` with `u ∈ C_i`, `v ∈ C_j` and
`u·v = 1`, i.e. `v = u⁻¹` with `mk u = C_i` and `mk u⁻¹ = C_j`.  If no element of `C_i` has its
inverse in `C_j` (`∀ u, mk u = C_i → mk u⁻¹ ≠ C_j`), the count is `0`.

This is Peterfalvi's `a_{110} = 0`: with `C_i = C_j = C₁ = ⟦z⟧` and `⟦z⁻¹⟧ ≠ ⟦z⟧` (no nontrivial
real class in odd order), an element `u ∈ C₁` has `u⁻¹ ∈ ⟦z⁻¹⟧ ≠ C₁`, so no pair multiplies to
`1`. -/
theorem classSumCoeff_one_eq_zero (Ci Cj : ConjClasses G)
    (h : ∀ u : G, ConjClasses.mk u = Ci → ConjClasses.mk u⁻¹ ≠ Cj) :
    classSumCoeff Ci Cj 1 = 0 := by
  rw [classSumCoeff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨u, v⟩ -
  rintro ⟨hi, hj, huv⟩
  -- `mk (u·v) = 1` forces `u·v = 1`, i.e. `u⁻¹ = v`; then `mk u⁻¹ = mk v = C_j` contradicts `h`.
  rw [mk_eq_one_iff_eq_one] at huv
  exact (h u hi) (by rw [inv_eq_of_mul_eq_one_right huv]; exact hj)

/-- **Peterfalvi (6.7.3), structure constant `a_{ij0} = |C_i|`.** When `C_j` is the *inverse* class
of `C_i` (every `u ∈ C_i` has `u⁻¹ ∈ C_j`), the coefficient of the identity class
`classSumCoeff Ci Cj 1` equals `|C_i|`: the pairs with product `1` are exactly `(u, u⁻¹)` for
`u ∈ C_i`, a bijection with `C_i`.

This is Peterfalvi's `a_{120} = |C₁|`: with `C_i = C₁ = ⟦z⟧` and `C_j = C₂ = ⟦z⁻¹⟧`, each `u ∈ C₁`
contributes the single pair `(u, u⁻¹)`.  The hypothesis `hinv` (that `mk u⁻¹ = C_j` for all
`u ∈ C_i`) holds for `C_j = ⟦z⁻¹⟧` because `mk u = ⟦z⟧ ⟹ mk u⁻¹ = ⟦z⁻¹⟧`. -/
theorem classSumCoeff_one_eq_card (Ci Cj : ConjClasses G)
    (hinv : ∀ u : G, ConjClasses.mk u = Ci → ConjClasses.mk u⁻¹ = Cj) :
    classSumCoeff Ci Cj 1 = Nat.card { x : G // ConjClasses.mk x = Ci } := by
  classical
  rw [classSumCoeff, Nat.card_eq_fintype_card,
    Fintype.card_subtype (p := fun x => ConjClasses.mk x = Ci)]
  -- The pair set `{(u,v) : mk u = Ci, mk v = Cj, mk (u·v) = 1}` is in bijection with
  -- `{u : mk u = Ci}` via `u ↦ (u, u⁻¹)`, inverse `(u,v) ↦ u`.
  refine Finset.card_nbij' (fun p => p.1) (fun u => (u, u⁻¹)) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  · intro u hu
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hu ⊢
    refine ⟨hu, hinv u hu, ?_⟩
    rw [mul_inv_cancel, mk_eq_one_iff_eq_one]
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hp
    obtain ⟨-, -, hs⟩ := hp
    -- `mk (u·v) = 1` ⟹ `u·v = 1` ⟹ `v = u⁻¹`, so `(u, u⁻¹) = (u, v)`.
    rw [mk_eq_one_iff_eq_one] at hs
    simp [inv_eq_of_mul_eq_one_right hs]
  · intro u _; rfl

/-- **Peterfalvi (6.7.3), `a_{110} = 0` keyed to `z`.** With `C_1 = ⟦z⟧`, the coefficient of the
identity class in `C_1 · C_1` is `0` provided `z⁻¹` is not `G`-conjugate to `z`
(`⟦z⁻¹⟧ ≠ ⟦z⟧`).  This is the direct instance of `classSumCoeff_one_eq_zero` consumed by (6.7.3):
the only hypothesis is the real-class atom `⟦z⁻¹⟧ ≠ ⟦z⟧` (from `|L|` odd). -/
theorem classSumCoeff_self_one_eq_zero (z : G)
    (hz : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z) :
    classSumCoeff (ConjClasses.mk z) (ConjClasses.mk z) 1 = 0 := by
  refine classSumCoeff_one_eq_zero _ _ fun u hu => ?_
  -- `mk u = ⟦z⟧ ⟹ mk u⁻¹ = ⟦z⁻¹⟧ ≠ ⟦z⟧`.
  rw [mk_inv_eq_of_mk_eq hu]
  exact hz

/-- **Peterfalvi (6.7.3), `a_{120} = |C_1|` keyed to `z`.** With `C_1 = ⟦z⟧` and `C_2 = ⟦z⁻¹⟧`
(the inverse class), the coefficient of the identity class in `C_1 · C_2` is `|C_1|`.  This is the
direct instance of `classSumCoeff_one_eq_card` consumed by (6.7.3); the inverse-class hypothesis
`∀ u, mk u = ⟦z⟧ → mk u⁻¹ = ⟦z⁻¹⟧` is *unconditional* (`mk_inv_eq_of_mk_eq`). -/
theorem classSumCoeff_self_inv_one_eq_card (z : G) :
    classSumCoeff (ConjClasses.mk z) (ConjClasses.mk z⁻¹) 1
      = Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z } :=
  classSumCoeff_one_eq_card _ _ fun _ hu => mk_inv_eq_of_mk_eq hu

end StructureCoeffAtIdentity

section PairAction

variable [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)]

/-- The defining predicate of the pair set `Ω = {(u,v) ∈ C_i × C_j ∣ u·v ∈ C_s}` of Peterfalvi
(6.7.1): an ordered pair `q = (u, v)` with `u ∈ C_i`, `v ∈ C_j` and `u·v ∈ C_s`. -/
def IsClassPair (Ci Cj Cs : ConjClasses G) (q : G × G) : Prop :=
  ConjClasses.mk q.1 = Ci ∧ ConjClasses.mk q.2 = Cj ∧ ConjClasses.mk (q.1 * q.2) = Cs

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] in
/-- Conjugation preserves the pair predicate: if `q` lies in `Ω` then so does `(x q.1 x⁻¹, x q.2
x⁻¹)`, because conjugation fixes every conjugacy class and is multiplicative. -/
theorem isClassPair_conj {Ci Cj Cs : ConjClasses G} {q : G × G}
    (hq : IsClassPair Ci Cj Cs q) (x : G) :
    IsClassPair Ci Cj Cs (x * q.1 * x⁻¹, x * q.2 * x⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := hq
  refine ⟨by rw [mk_conj_eq, h1], by rw [mk_conj_eq, h2], ?_⟩
  rw [show x * q.1 * x⁻¹ * (x * q.2 * x⁻¹) = x * (q.1 * q.2) * x⁻¹ by group, mk_conj_eq, h3]

/-- The pair set `Ω` of Peterfalvi (6.7.1), as a subtype of `G × G`. -/
abbrev ClassPair (Ci Cj Cs : ConjClasses G) : Type _ := { q : G × G // IsClassPair Ci Cj Cs q }

/-- The **conjugation action of a subgroup `P ≤ G` on the pair set `Ω`** of Peterfalvi (6.7.1):
`x • (u, v) = (x u x⁻¹, x v x⁻¹)`.  This is the action whose fixed-point-freeness (no `x ∈ P^#`
fixes a pair) yields `|P| ∣ a_{ijs}|C_s| = |Ω|`. -/
instance classPairSMul (P : Subgroup G) (Ci Cj Cs : ConjClasses G) :
    SMul P (ClassPair Ci Cj Cs) where
  smul x q := ⟨((x : G) * q.1.1 * (x : G)⁻¹, (x : G) * q.1.2 * (x : G)⁻¹),
    isClassPair_conj q.2 (x : G)⟩

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] in
@[simp] theorem classPairSMul_coe (P : Subgroup G) {Ci Cj Cs : ConjClasses G} (x : P)
    (q : ClassPair Ci Cj Cs) :
    ((x • q : ClassPair Ci Cj Cs) : G × G) = ((x : G) * q.1.1 * (x : G)⁻¹,
      (x : G) * q.1.2 * (x : G)⁻¹) := rfl

instance classPairMulAction (P : Subgroup G) (Ci Cj Cs : ConjClasses G) :
    MulAction P (ClassPair Ci Cj Cs) where
  one_smul q := by
    apply Subtype.ext
    rw [classPairSMul_coe]
    simp
  mul_smul x y q := by
    apply Subtype.ext
    rw [classPairSMul_coe, classPairSMul_coe, classPairSMul_coe]
    simp only [Subgroup.coe_mul, Prod.mk.injEq]
    constructor <;> group

omit [DecidableEq G] in
set_option backward.isDefEq.respectTransparency false in
/-- The cardinality of the pair set `Ω` equals the structure coefficient `a_{ijs}|C_s| =
`classSumCoeff Ci Cj Cs` (Peterfalvi's `a_{ijs}|{\cal C}_s|`). -/
theorem card_classPair (Ci Cj Cs : ConjClasses G) :
    Nat.card (ClassPair Ci Cj Cs) = classSumCoeff Ci Cj Cs := by
  classical
  rw [classSumCoeff, Nat.card_eq_fintype_card,
    Fintype.card_subtype (p := fun q => IsClassPair Ci Cj Cs q)]
  congr 1
  ext q
  simp only [Finset.mem_filter, IsClassPair]

omit [DecidableEq G] in
/-- **Peterfalvi (6.7.1)** (orbit-counting half).  Let `P ≤ G` be a finite subgroup acting on the
pair set `Ω = {(u,v) ∈ C_i × C_j ∣ u·v ∈ C_s}` by conjugation.  If `P` acts *fixed-point-freely* —
no `x ∈ P` with `x ≠ 1` fixes a pair of `Ω` — then `|P| ∣ a_{ijs}|C_s|`, i.e. `|P|` divides the
structure-coefficient count `classSumCoeff Ci Cj Cs`.

This packages the counting step of (6.7.1): the remaining content of (6.7.1) is precisely the
group-theoretic verification of the fixed-point-free hypothesis (`P^#` TI-subset ⟹ `C_G(x) ⊆ L`,
a `p`-element of `L` lies in `P`, conjugacy into `Z^#` with `Z ⊴ L` forces it into `Z`,
contradicting `C_s ∩ Z = ∅`). -/
theorem card_dvd_classSumCoeff_of_fixedPointFree (P : Subgroup G) [Finite P]
    (Ci Cj Cs : ConjClasses G)
    (hfree : ∀ x : P, (x : G) ≠ 1 → ∀ q : ClassPair Ci Cj Cs, x • q ≠ q) :
    Nat.card P ∣ classSumCoeff Ci Cj Cs := by
  rw [← card_classPair]
  refine card_dvd_of_no_nontrivial_fixed (Γ := P) (β := ClassPair Ci Cj Cs) ?_
  intro x hx q
  exact hfree x (by simpa using hx) q

end PairAction

end OddOrder.RepresentationTheory


