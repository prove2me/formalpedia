-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:33.265317+00:00
-- url     : https://prove2.me/theorems/538747fd-a57b-412e-9fb1-4a8981e1d583
-- title:
--   Definitions of ParametersFiniteAnswers: Finite answer spaces for the low individual degree test Finite-type instances for the bounded polynomial answer spaces…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.ParametersFiniteAnswers` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Finite answer spaces for the low individual degree test. Finite-type instances for the bounded polynomial answer spaces defined in `MIPStarRE.LDT.Basic.LowDegreePolynomial`.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (5): `MIPStarRE.LDT.instDecidableEqAxisLinePolynomial` (The axis-line polynomial answer type uses classical equality on the bundled polynomial witness.); `MIPStarRE.LDT.instDecidableEqPolynomial` (The finite low-individual-degree polynomial answer type uses classical equality on the bundled polynomial witness.); `MIPStarRE.LDT.instFintypeAxisLinePolynomial` (Axis-line polynomial answers form a finite type via their bounded coefficient vectors.); `MIPStarRE.LDT.instFintypeDiagonalLinePolynomial` (Diagonal-line polynomial answers form a finite type via their bounded coefficient vectors.); `MIPStarRE.LDT.instFintypePolynomial` (Global low-individual-degree polynomial answers form a finite type, by injecting into the finite space of degree-restricted multivariate…).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `linePolynomial_coeff_fin_injective`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.ParametersFiniteAnswers` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 5 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean (definition bundle: declarations the uploaded statements rest on);
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
# Finite answer spaces for the low individual degree test

Finite-type instances for the bounded polynomial answer spaces defined in
`MIPStarRE.LDT.Basic.LowDegreePolynomial`.
-/

namespace MIPStarRE.LDT

open scoped BigOperators

/-! ### Finite answer spaces -/

/-- The axis-line polynomial answer type uses classical equality on the bundled
polynomial witness. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    DecidableEq (AxisLinePolynomial params) :=
  Classical.decEq _

/-- The finite low-individual-degree polynomial answer type uses classical
equality on the bundled polynomial witness. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    DecidableEq (Polynomial params) :=
  Classical.decEq _

/-- A univariate polynomial of `natDegree ≤ n` is determined by its first
`n + 1` coefficients.  Shared injectivity fact behind the finite-answer-space
instances below. -/
theorem linePolynomial_coeff_fin_injective (params : Parameters) [FieldModel params.q]
    {n : ℕ} {p q : LinePolynomialModel params}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ i : Fin (n + 1), p.coeff i = q.coeff i) : p = q := by
  ext k
  by_cases hk : k < n + 1
  · exact h ⟨k, hk⟩
  · rw [p.coeff_eq_zero_of_natDegree_lt (hp.trans_lt (by omega)),
      q.coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega))]

/-- Axis-line polynomial answers form a finite type via their bounded coefficient vectors. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (AxisLinePolynomial params) := by
  classical
  exact Fintype.ofInjective
    (fun f : AxisLinePolynomial params => fun i : Fin (params.d + 1) => f.poly.coeff i)
    fun f g h => AxisLinePolynomial.ext
      (linePolynomial_coeff_fin_injective params f.degreeBounded g.degreeBounded
        fun i => congrFun h i)

/-- Diagonal-line polynomial answers form a finite type via their bounded coefficient vectors. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (DiagonalLinePolynomial params) := by
  classical
  exact Fintype.ofInjective
    (fun f : DiagonalLinePolynomial params =>
      fun i : Fin (params.m * params.d + 1) => f.poly.coeff i)
    fun f g h => DiagonalLinePolynomial.ext
      (linePolynomial_coeff_fin_injective params f.degreeBounded g.degreeBounded
        fun i => congrFun h i)

/-- Global low-individual-degree polynomial answers form a finite type, by
injecting into the finite space of degree-restricted multivariate polynomials. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (Polynomial params) := by
  classical
  letI : Finite (MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d) :=
    Module.finite_of_finite (Scalar params)
  letI : Fintype (MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d) :=
    Fintype.ofFinite _
  exact Fintype.ofInjective
    (fun g : Polynomial params =>
      (⟨g.poly, by
          rw [MvPolynomial.mem_restrictDegree_iff_sup]
          simpa [MvPolynomial.degreeOf_def] using g.lowIndividualDegree⟩ :
        MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d))
    fun g g' h => by
      cases g; cases g'
      simpa using congrArg Subtype.val h

end MIPStarRE.LDT


