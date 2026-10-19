-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:37.435545+00:00
-- url     : https://prove2.me/theorems/447da7d1-3f46-4119-8976-8a0a64bff946
-- title:
--   Definitions of LinePolynomialEmbedding: Axis-line to global polynomial lifts Utility lemmas for substituting a univariate axis-line polynomial into a chosen…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LinePolynomialEmbedding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Axis-line to global polynomial lifts. Utility lemmas for substituting a univariate axis-line polynomial into a chosen ambient coordinate.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (1): `MIPStarRE.LDT.axisLinePolynomialToPolynomial` (Extend an axis-line answer to a global polynomial by substituting the ambient coordinate `X i` for the formal line parameter.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `degreeOf_eval₂_C_X_le_natDegree`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LinePolynomialEmbedding` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LinePolynomialEmbedding.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 5 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LinePolynomialEmbedding.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/LinePolynomialEmbedding.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LinePolynomialEmbedding.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial

set_option backward.isDefEq.respectTransparency false

/-!
# Axis-line to global polynomial lifts

Utility lemmas for substituting a univariate axis-line polynomial into a chosen
ambient coordinate.
-/

namespace MIPStarRE.LDT

/-- Substituting a univariate polynomial into one multivariate variable preserves its
degree bound in that variable and gives degree zero in all other variables. -/
theorem degreeOf_eval₂_C_X_le_natDegree {K σ : Type*} [Field K] [DecidableEq σ]
    (p : _root_.Polynomial K) (i j : σ) :
    MvPolynomial.degreeOf i
      (p.eval₂ MvPolynomial.C (MvPolynomial.X j) : MvPolynomial σ K) ≤
        if i = j then p.natDegree else 0 := by
  rw [_root_.Polynomial.eval₂_eq_sum_range]
  refine (MvPolynomial.degreeOf_sum_le i (Finset.range (p.natDegree + 1)) _).trans ?_
  refine Finset.sup_le fun n hn => ?_
  calc
    MvPolynomial.degreeOf i
        (MvPolynomial.C (p.coeff n) * MvPolynomial.X j ^ n : MvPolynomial σ K)
        ≤ MvPolynomial.degreeOf i (MvPolynomial.X j ^ n : MvPolynomial σ K) := by
          exact MvPolynomial.degreeOf_C_mul_le _ _ _
    _ ≤ n * MvPolynomial.degreeOf i (MvPolynomial.X j : MvPolynomial σ K) := by
          exact MvPolynomial.degreeOf_pow_le _ _ _
    _ ≤ if i = j then p.natDegree else 0 := by
          by_cases hij : i = j
          · have hn_le : n ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
            simp [hij, hn_le]
          · simp [hij, MvPolynomial.degreeOf_X]

/-- Extend an axis-line answer to a global polynomial by substituting the ambient
coordinate `X i` for the formal line parameter. Away from direction `i`, the result
is constant, so in the `m = 1` base case this identifies the unique axis-parallel
line polynomial with an ambient low-degree polynomial. -/
noncomputable def axisLinePolynomialToPolynomial
    (params : Parameters) [FieldModel params.q]
    (i : Fin params.m) (f : AxisLinePolynomial params) : Polynomial params where
  poly := f.poly.eval₂ MvPolynomial.C (MvPolynomial.X i)
  lowIndividualDegree := fun j =>
    (degreeOf_eval₂_C_X_le_natDegree f.poly j i).trans <| by
      by_cases hji : j = i
      · simp [hji, f.degreeBounded]
      · simp [hji]

end MIPStarRE.LDT


