-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_TotallyPositive
-- name    : TauCeti_NumberTheory_NumberField_TotallyPositive
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:42:07.464168+00:00
-- url     : https://prove2.me/theorems/2ca12df1-f982-42be-81c5-19d1c98c4820
-- title:
--   Totally positive elements of a number field
-- statement:
--   For a number field $K$, an element $x$ is totally positive when
--
--   $$
--   \tau(x)>0\quad\text{for every real embedding }\tau:K\hookrightarrow\mathbb R.
--   $$
--
--   The totally positive nonzero elements form a subgroup of $K^\times$. This records the archimedean conditions in ray and narrow class groups.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/TotallyPositive.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/TotallyPositive.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_GroupTheory_Index_Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Totally positive elements of a number field

An element `x` of a number field `K` is **totally positive** when it is strictly positive under
every real embedding `K →+* ℝ` — equivalently, at every real infinite place. This is the archimedean
positivity condition underlying the *narrow* class group of the multiquadratic roadmap (Layer 3):
the narrow class group `Cl⁺(K)` is the quotient of the fractional ideals by the principal ideals
admitting a totally positive generator. It surjects onto the ordinary class group `Cl(K)`
(forgetting the positivity condition), and the `2`-rank of `Cl⁺(K)` is what the genus-theory
`t - 1` formula (with `t` the number of ramified primes) computes for a **real quadratic** field
in the multiquadratic roadmap.

This file introduces the predicate and its multiplicative structure. The totally positive elements
are closed under multiplication and inversion and contain every nonzero square, so the totally
positive units form a subgroup of `Kˣ`. That subgroup is the kernel of the sign (signature) map on
units; the signs *not* realized by units measure the difference between `Cl⁺(K)` and `Cl(K)`.

The file also records that `totallyPositiveUnits` has **finite index** — a finite intersection, over
the real places, of the finite-index preimages of the positive units of `ℝ` — which is what makes
the narrow class group finite (see `NarrowClassGroup.Finite`).

## Main definitions and results

* `NumberField.IsTotallyPositive`: strict positivity at every real place, with
  `isTotallyPositive_iff` its introduction/elimination form.
* `NumberField.isTotallyPositive_one`, `IsTotallyPositive.mul`, `IsTotallyPositive.inv`,
  `isTotallyPositive_sq`: the multiplicative structure, including that nonzero squares are totally
  positive.
* `NumberField.isTotallyPositive_ratCast`: a positive rational number is totally positive, with
  `NumberField.isTotallyPositive_intCast` its integer special case.
* `NumberField.totallyPositiveUnits`: the subgroup of totally positive units of `Kˣ` (the
  kernel of the unit signature map), with `sq_mem_totallyPositiveUnits`. For a totally complex field
  it is everything (`totallyPositiveUnits_eq_top`), since total positivity is then vacuous
  (`not_isReal_of_isTotallyComplex` makes `IsTotallyPositive` `simp` to `True`).
* `NumberField.totallyPositiveIntegerUnits`: the corresponding subgroup of the arithmetic
  units `(𝓞 K)ˣ`, the preimage of `totallyPositiveUnits` under `(𝓞 K)ˣ → Kˣ`, with
  `mem_totallyPositiveIntegerUnits` and `sq_mem_totallyPositiveIntegerUnits`.
* `NumberField.exists_isTotallyPositive_sub_mem`: every residue class modulo a nonzero ideal of
  `𝓞 K` contains a nonzero totally positive integer.
* `NumberField.norm_nonneg_of_isTotallyPositive`: the field norm of a totally positive element is
  nonnegative, and `NumberField.norm_pos_of_isTotallyPositive`: for a nonzero such element it is
  strictly positive.
* `NumberField.finiteIndex_totallyPositiveUnits`: `totallyPositiveUnits` has finite index
  (via `Units.instFiniteIndexPosSubgroup` and the general `Subgroup.instFiniteIndexComap`).
-/

 section

open NumberField InfinitePlace

namespace NumberField

variable {K : Type*} [Field K]

/-- An element of a number field is **totally positive** when it is strictly positive under every
real embedding `K →+* ℝ` (equivalently, at every real infinite place `w`). For a totally complex
field the condition is vacuous; the content is at the real places. -/
def IsTotallyPositive (x : K) : Prop :=
  ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < embedding_of_isReal hw x

/-- Introduction and elimination form of `IsTotallyPositive`: total positivity is exactly strict
positivity at every real infinite place. -/
@[simp, grind =] theorem isTotallyPositive_iff {x : K} :
    IsTotallyPositive x ↔ ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < embedding_of_isReal hw x :=
  Iff.rfl













/-- The subgroup of **totally positive units** of `Kˣ`: the intersection, over the real infinite
places `w`, of the preimages of the positive units of `ℝ` under the real embedding `w`. It is the
kernel of the sign (signature) map on units, and controls the comparison between the narrow class
group `Cl⁺(K)` and the ordinary class group `Cl(K)`. -/
noncomputable def totallyPositiveUnits : Subgroup Kˣ :=
  ⨅ (w : InfinitePlace K) (hw : w.IsReal),
    (Units.posSubgroup ℝ).comap (Units.map (embedding_of_isReal hw).toMonoidHom)

/-- A unit lies in `totallyPositiveUnits` exactly when its underlying field element is totally
positive. -/
@[simp]
theorem mem_totallyPositiveUnits {u : Kˣ} :
    u ∈ totallyPositiveUnits ↔ IsTotallyPositive (u : K) := by
  simp [totallyPositiveUnits, isTotallyPositive_iff]







variable [NumberField K]











/-- **The signed product formula at a totally positive element.** For a totally positive `x` the
product of `w x ^ mult w` over the infinite places is the norm itself, and not merely its absolute
value as in `InfinitePlace.prod_eq_abs_norm`: at a real place total positivity identifies `w x`
with the value of the corresponding real embedding, and a complex place contributes a conjugate
pair, whose product is a square. -/
 theorem norm_eq_prod_of_isTotallyPositive {x : K} (hpos : IsTotallyPositive x) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, w x ^ mult w := by
  classical
  -- Compare in `ℂ`, where the norm is the product over all the embeddings, then descend to `ℝ`.
  have key : ((Algebra.norm ℚ x : ℚ) : ℂ) =
      ((∏ w : InfinitePlace K, w x ^ mult w : ℝ) : ℂ) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ) (Algebra.norm ℚ x), Algebra.norm_eq_prod_embeddings ℚ ℂ x,
      ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
        (fun σ : K →ₐ[ℚ] ℂ => σ x) (fun φ => by simp [RingHom.equivRatAlgHom]),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x),
      Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    by_cases hw : IsReal w
    · -- A real place has a single embedding above it, namely `embedding w`.
      have hcard : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w).card = 1 := by
        rw [InfinitePlace.card_filter_mk_eq, hw.mult_eq_one]
      have hmem : embedding w ∈ Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mk_embedding]
      rw [Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hmem, fun y hy => Finset.card_le_one.mp hcard.le y hy _ hmem⟩,
        Finset.prod_singleton, hw.mult_eq_one, pow_one, ← embedding_of_isReal_apply hw]
      -- Total positivity identifies the real embedding with the place.
      have hval : w x = embedding_of_isReal hw x := by
        rw [← norm_embedding_of_isReal hw, Real.norm_eq_abs, abs_of_pos (hpos w hw)]
      rw [hval]
    · -- A complex place has the conjugate pair `embedding w`, `conj (embedding w)` above it.
      have hne : embedding w ≠ ComplexEmbedding.conjugate (embedding w) := fun h =>
        hw (isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
      have hsub : ({embedding w, ComplexEmbedding.conjugate (embedding w)} : Finset (K →+* ℂ)) ⊆
          Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w := by
        intro φ hφ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hφ with rfl | rfl
        · exact mk_embedding w
        · rw [mk_conjugate_eq]; exact mk_embedding w
      have hcard : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w).card = 2 := by
        rw [InfinitePlace.card_filter_mk_eq, (not_isReal_iff_isComplex.mp hw).mult_eq_two]
      rw [(Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_pair hne])).symm,
        Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, norm_embedding_eq,
        (not_isReal_iff_isComplex.mp hw).mult_eq_two]
  exact_mod_cast key

/-- **The norm of a totally positive element is nonnegative.**

Over a totally complex field the hypothesis is vacuous (`not_isReal_of_isTotallyComplex`), so the
conclusion holds for every `x` there, including `x = 0` whose norm is `0`. -/
theorem norm_nonneg_of_isTotallyPositive {x : K} (hpos : IsTotallyPositive x) :
    0 ≤ Algebra.norm ℚ x := by
  -- Against `prod_eq_abs_norm`, the signed product formula says the absolute value costs nothing.
  have hreal := norm_eq_prod_of_isTotallyPositive hpos
  rw [InfinitePlace.prod_eq_abs_norm] at hreal
  have habs : |Algebra.norm ℚ x| = Algebra.norm ℚ x := by exact_mod_cast hreal.symm
  exact abs_eq_self.mp habs

/-- **The norm of a nonzero totally positive element is positive.**

Over a totally complex field the hypothesis `IsTotallyPositive x` is vacuous
(`not_isReal_of_isTotallyComplex`), so this covers imaginary quadratic fields as a special case. -/
theorem norm_pos_of_isTotallyPositive {x : K} (hx : x ≠ 0) (hpos : IsTotallyPositive x) :
    0 < Algebra.norm ℚ x :=
  lt_of_le_of_ne (norm_nonneg_of_isTotallyPositive hpos)
    (Ne.symm ((Algebra.norm_ne_zero_iff_of_basis (Module.finBasis ℚ K)).mpr hx))

/-- `totallyPositiveUnits` has **finite index** in `Kˣ`: it is a finite intersection, over the real
infinite places, of the finite-index preimages of the positive units of `ℝ` (via the general
`Units.instFiniteIndexPosSubgroup` and `Subgroup.instFiniteIndexComap`). -/
instance finiteIndex_totallyPositiveUnits : (totallyPositiveUnits (K := K)).FiniteIndex := by
  rw [totallyPositiveUnits, iInf_subtype']
  exact Subgroup.finiteIndex_iInf fun _ => inferInstance

end NumberField

end
end


