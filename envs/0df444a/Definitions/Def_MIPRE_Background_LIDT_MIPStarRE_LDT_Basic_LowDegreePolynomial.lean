-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:36.980759+00:00
-- url     : https://prove2.me/theorems/a4ae5589-9885-4838-a259-e237327cc1fe
-- title:
--   Definitions of LowDegreePolynomial: Low-individual-degree polynomials for the low individual degree test Multivariate low-degree polynomial objects and…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LowDegreePolynomial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Low-individual-degree polynomials for the low individual degree test. Multivariate low-degree polynomial objects and their restrictions. Note: this module contributes declarations to the comparator statement closure of `mainFormal`, which must elaborate in the same environment as the Mathlib-only `Challenge.lean`. Keep the full `import Mathlib`; do not narrow it. See `docs/comparator.md`, "Environment alignment".
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (10): `MIPStarRE.LDT.Polynomial` (Global low-individual-degree polynomial outcomes.); `MIPStarRE.LDT.Polynomial.appendAtHeight` (Extend a global polynomial to the slice at height `x` by ignoring the new variable.); `MIPStarRE.LDT.Polynomial.axisCoordinatePolynomial` (Coordinate polynomial for restricting to an axis-parallel affine line.); `MIPStarRE.LDT.Polynomial.const` (The constant polynomial with value `a`.); `MIPStarRE.LDT.Polynomial.instCoeFunForallPointFq`; `MIPStarRE.LDT.Polynomial.instInhabited`; `MIPStarRE.LDT.Polynomial.restrictAtHeight` (Restrict a global polynomial in `m + 1` variables to the slice at height `x`.); `MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap` (Coordinate map for restricting a polynomial in `m+1` variables to the slice `X_m = x`.); `MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine` (Restrict a global polynomial to an axis-parallel line.); `MIPStarRE.LDT.Polynomial.toFun` (Evaluation of the stored multivariate polynomial on a coded point.).
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `const_apply`, `degreeOf_eval₂Hom_restrictAtHeightCoordinateMap_le`, `degreeOf_rename_embedCoord_le`, `natDegree_eval₂Hom_axisCoordinatePolynomial_le`, `degreeOf_rename_embedCoord_lastCoord`, `degreeOf_restrictAtHeightCoordinateMap_le`, `natDegree_axisCoordinatePolynomial_le`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LowDegreePolynomial` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LowDegreePolynomial.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 4 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LowDegreePolynomial.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/LowDegreePolynomial.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LowDegreePolynomial.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.RelClasses
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Theorems.Thm_MIPStarRE_LDT_embedCoord_injective
import Theorems.Thm_MIPStarRE_LDT_embedCoord_ne_lastCoord

set_option backward.isDefEq.respectTransparency false

/-!
# Low-individual-degree polynomials for the low individual degree test

Multivariate low-degree polynomial objects and their restrictions.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".
-/

namespace MIPStarRE.LDT

/-- Global low-individual-degree polynomial outcomes. -/
structure Polynomial (params : Parameters) [FieldModel params.q] where
  poly : PolynomialModel params
  lowIndividualDegree : ∀ i, MvPolynomial.degreeOf i poly ≤ params.d

/-- Renaming a polynomial along the old-coordinate inclusion does not introduce
the appended last coordinate. -/
theorem degreeOf_rename_embedCoord_lastCoord (params : Parameters) [FieldModel params.q]
    (p : PolynomialModel params) :
    MvPolynomial.degreeOf (lastCoord params)
      (MvPolynomial.rename (embedCoord params) p : PolynomialModel params.next) = 0 := by
  rw [MvPolynomial.degreeOf, MvPolynomial.degrees_rename_of_injective
    (embedCoord_injective params)]
  simp only [Multiset.count_eq_zero, Multiset.mem_map]
  rintro ⟨b, _, hb⟩
  exact embedCoord_ne_lastCoord params b hb

namespace Polynomial

/-- Evaluation of the stored multivariate polynomial on a coded point. -/
noncomputable def toFun {params : Parameters} [FieldModel params.q] (g : Polynomial params) :
    Point params → Fq params :=
  evalPolynomialModel params g.poly

noncomputable instance {params : Parameters} [FieldModel params.q] :
    CoeFun (Polynomial params) (fun _ => Point params → Fq params) :=
  ⟨Polynomial.toFun⟩

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The constant polynomial with value `a`. -/
noncomputable def const (params : Parameters) [FieldModel params.q] (a : Fq params) :
    Polynomial params where
  poly := MvPolynomial.C (decodeScalar a)
  lowIndividualDegree := fun i => (MvPolynomial.degreeOf_C _ i).trans_le (Nat.zero_le _)

noncomputable instance {params : Parameters} [FieldModel params.q] :
    Inhabited (Polynomial params) :=
  ⟨const params default⟩

/-- The constant polynomial evaluates to its prescribed value. -/
@[simp] theorem const_apply (params : Parameters) [FieldModel params.q]
    (a : Fq params) (u : Point params) :
    const params a u = a := by
  simp [const, Polynomial.toFun, evalPolynomialModel]

/-- Renaming a low-degree polynomial along the coordinate embedding preserves the
low-individual-degree bound in `m + 1` variables. -/
theorem degreeOf_rename_embedCoord_le (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (i : Fin params.next.m) :
    MvPolynomial.degreeOf i
      (MvPolynomial.rename (embedCoord params) g.poly : PolynomialModel params.next) ≤
      params.d := by
  have hinj : Function.Injective (embedCoord params) := embedCoord_injective params
  by_cases h : i.val < params.m
  · -- i is in the range of embedCoord: transfer the degree bound
    have hi : embedCoord params ⟨i.val, h⟩ = i := by
      ext; simp [embedCoord]
    rw [← hi, MvPolynomial.degreeOf_rename_of_injective hinj]
    exact g.lowIndividualDegree _
  · -- i is not in range: degreeOf = 0
    have hi_last : i = lastCoord params := by
      apply Fin.ext
      have hle : params.m ≤ i.val := Nat.le_of_not_gt h
      have hlt : i.val < params.m + 1 := by
        simpa [Parameters.next] using i.isLt
      exact le_antisymm (Nat.le_of_lt_succ hlt) hle
    rw [hi_last, degreeOf_rename_embedCoord_lastCoord]
    omega

/-- Extend a global polynomial to the slice at height `x` by ignoring the new variable. -/
noncomputable def appendAtHeight (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (_x : Fq params) : Polynomial params.next where
  poly := MvPolynomial.rename (embedCoord params) g.poly
  lowIndividualDegree := degreeOf_rename_embedCoord_le params g

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- Coordinate map for restricting a polynomial in `m+1` variables to the slice `X_m = x`. -/
noncomputable def restrictAtHeightCoordinateMap (params : Parameters) [FieldModel params.q]
    (x : Fq params) :
    Fin params.next.m → PolynomialModel params :=
  fun i =>
    if h : i.1 < params.m then
      MvPolynomial.X ⟨i.1, h⟩
    else
      MvPolynomial.C (decodeScalar x)

theorem degreeOf_restrictAtHeightCoordinateMap_le
    (params : Parameters) [FieldModel params.q] (x : Fq params)
    (i : Fin params.m) (j : Fin params.next.m) :
    MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j) ≤
      if j = embedCoord params i then 1 else 0 := by
  classical
  by_cases hji : j = embedCoord params i
  · subst hji
    rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
    · letI := hsub
      have hX : (MvPolynomial.X i : PolynomialModel params) = 0 := Subsingleton.elim _ _
      simp [restrictAtHeightCoordinateMap, embedCoord, hX]
    · letI := hnontriv
      simp [restrictAtHeightCoordinateMap, embedCoord]
  · by_cases hj : j.1 < params.m
    · have hne : (⟨j.1, hj⟩ : Fin params.m) ≠ i := by
        intro h
        apply hji
        ext
        simpa [embedCoord] using congrArg Fin.val h
      rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
      · letI := hsub
        have hX : (MvPolynomial.X ⟨j.1, hj⟩ : PolynomialModel params) = 0 := Subsingleton.elim _ _
        simp [restrictAtHeightCoordinateMap, hj, hji, hX]
      · letI := hnontriv
        have hne' : i ≠ ⟨j.1, hj⟩ := by
          simpa [eq_comm] using hne
        rw [restrictAtHeightCoordinateMap, dif_pos hj, MvPolynomial.degreeOf_X]
        simp [hne', hji]
    · simp [restrictAtHeightCoordinateMap, hj, MvPolynomial.degreeOf_C, hji]

/-- Restricting a polynomial to a coordinate slice via `eval₂Hom` preserves the
low-individual-degree bound: each variable's degree stays at most `d`. -/
theorem degreeOf_eval₂Hom_restrictAtHeightCoordinateMap_le
    (params : Parameters) [FieldModel params.q]
    (g : Polynomial params.next) (x : Fq params) (i : Fin params.m) :
    MvPolynomial.degreeOf i
      (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) g.poly) ≤
      params.d := by
    classical
    let p : MvPolynomial (Fin params.next.m) (Scalar params) := g.poly
    change MvPolynomial.degreeOf i
      (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) p) ≤ params.d
    rw [p.as_sum]
    rw [map_sum
      (g := MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x))
      (s := p.support)
      (f := fun n => (MvPolynomial.monomial n) (MvPolynomial.coeff n p))]
    calc
      MvPolynomial.degreeOf i
          (∑ n ∈ p.support,
            MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x)
              (MvPolynomial.monomial n (p.coeff n))) ≤
          p.support.sup fun n =>
            MvPolynomial.degreeOf i
              (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x)
                (MvPolynomial.monomial n (p.coeff n))) :=
        MvPolynomial.degreeOf_sum_le i _ _
      _ ≤ params.d := by
        apply Finset.sup_le
        intro n hn
        rw [MvPolynomial.eval₂Hom_monomial]
        calc
          MvPolynomial.degreeOf i
              ((MvPolynomial.C (p.coeff n) : PolynomialModel params) *
                ∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) ≤
              MvPolynomial.degreeOf i (MvPolynomial.C (p.coeff n)) +
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) :=
            MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ 0 +
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) := by
            gcongr
            exact (MvPolynomial.degreeOf_C (g.poly.coeff n) i).le
          _ =
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) := by
            simp
          _ ≤ ∑ j ∈ n.support,
                MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j ^ n j) :=
            MvPolynomial.degreeOf_prod_le i _ _
          _ ≤ ∑ j ∈ n.support, if j = embedCoord params i then n j else 0 := by
            apply Finset.sum_le_sum
            intro j hj
            calc
              MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j ^ n j) ≤
                  n j * MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j) :=
                MvPolynomial.degreeOf_pow_le i _ _
              _ ≤ n j * (if j = embedCoord params i then 1 else 0) := by
                exact Nat.mul_le_mul_left _ (degreeOf_restrictAtHeightCoordinateMap_le params x i j)
              _ = if j = embedCoord params i then n j else 0 := by
                split_ifs <;> simp
          _ = n (embedCoord params i) := by
            by_cases hmem : embedCoord params i ∈ n.support
            · rw [Finset.sum_eq_single (embedCoord params i)]
              · simp
              · intro j hj hne
                simp [hne]
              · intro hnot
                contradiction
            · rw [Finset.sum_eq_zero]
              · rw [Finsupp.notMem_support_iff.mp hmem]
              · intro j hj
                by_cases h : j = embedCoord params i
                · exact (hmem (h ▸ hj)).elim
                · simp [h]
          _ ≤ params.d := by
            exact
              (MvPolynomial.degreeOf_le_iff.mp
                (g.lowIndividualDegree (embedCoord params i))) n hn

/-- Restrict a global polynomial in `m + 1` variables to the slice at height `x`. -/
noncomputable def restrictAtHeight (params : Parameters) [FieldModel params.q]
    (g : Polynomial params.next) (x : Fq params) : Polynomial params where
  poly := MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) g.poly
  lowIndividualDegree := degreeOf_eval₂Hom_restrictAtHeightCoordinateMap_le params g x

/-- Coordinate polynomial for restricting to an axis-parallel affine line. -/
noncomputable def axisCoordinatePolynomial (params : Parameters) [FieldModel params.q]
    (ℓ : AxisParallelLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    if i = ℓ.direction then
      _root_.Polynomial.C (decodeScalar (ℓ.base i)) + _root_.Polynomial.X
    else
      _root_.Polynomial.C (decodeScalar (ℓ.base i))

theorem natDegree_axisCoordinatePolynomial_le (params : Parameters) [FieldModel params.q]
    (ℓ : AxisParallelLine params) (i : Fin params.m) :
    (axisCoordinatePolynomial params ℓ i).natDegree ≤ if i = ℓ.direction then 1 else 0 := by
  classical
  by_cases hi : i = ℓ.direction
  · subst hi
    rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
    · letI := hsub
      have hX : (_root_.Polynomial.X : LinePolynomialModel params) = 0 := Subsingleton.elim _ _
      simp [axisCoordinatePolynomial, hX]
    · letI := hnontriv
      simp [axisCoordinatePolynomial, add_comm]
  · simp [axisCoordinatePolynomial, hi, Polynomial.natDegree_C]

/-- Restricting a low-degree polynomial to an axis-parallel line via `eval₂Hom` yields a
univariate polynomial whose natural degree is at most `d`. -/
theorem natDegree_eval₂Hom_axisCoordinatePolynomial_le
    (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) :
    (MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ)
      g.poly).natDegree ≤ params.d := by
    classical
    rw [g.poly.as_sum, map_sum]
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := g.poly.support)
      (f := fun n =>
        MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ)
          (MvPolynomial.monomial n (g.poly.coeff n)))
      (n := params.d) ?_
    intro n hn
    rw [MvPolynomial.eval₂Hom_monomial]
    calc
      ((_root_.Polynomial.C (g.poly.coeff n) : LinePolynomialModel params) *
          ∏ j ∈ n.support, axisCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
          (∏ j ∈ n.support, axisCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ ∑ j ∈ n.support, (axisCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ j ∈ n.support, if j = ℓ.direction then n j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (axisCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
              n j * (axisCoordinatePolynomial params ℓ j).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ n j * (if j = ℓ.direction then 1 else 0) := by
            exact Nat.mul_le_mul_left _ (natDegree_axisCoordinatePolynomial_le params ℓ j)
          _ = if j = ℓ.direction then n j else 0 := by
            split_ifs <;> simp
      _ = n ℓ.direction := by
        by_cases hmem : ℓ.direction ∈ n.support
        · rw [Finset.sum_eq_single ℓ.direction]
          · simp
          · intro j hj hne
            simp [hne]
          · intro hnot
            contradiction
        · rw [Finset.sum_eq_zero]
          · rw [Finsupp.notMem_support_iff.mp hmem]
          · intro j hj
            by_cases h : j = ℓ.direction
            · exact (hmem (h ▸ hj)).elim
            · simp [h]
      _ ≤ params.d := by
        exact (MvPolynomial.degreeOf_le_iff.mp (g.lowIndividualDegree ℓ.direction)) n hn

/-- Restrict a global polynomial to an axis-parallel line. -/
noncomputable def restrictToAxisParallelLine (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) : AxisLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ) g.poly
  degreeBounded := natDegree_eval₂Hom_axisCoordinatePolynomial_le params g ℓ

end Polynomial

end MIPStarRE.LDT


