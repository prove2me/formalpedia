-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:20.909033+00:00
-- url     : https://prove2.me/theorems/210c8df6-06f4-4de5-9070-b537249d4548
-- title:
--   Definitions of Definitions: Error cascade — core definitions This module defines the central error quantities `mainFormalError`,…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.Definitions` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Error cascade — core definitions. This module defines the central error quantities `mainFormalError`, `mainFormalEnvelope`, the cascade variables `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄`, and the `CascadeHypotheses` numeric regime used throughout the error-cascade bookkeeping for Step 8 of `mainFormal`. Note: this module contributes declarations to the comparator statement closure of `mainFormal`, which must elaborate in the same environment as the Mathlib-only `Challenge.lean`. Keep the full `import Mathlib`; do not narrow it. See `docs/comparator.md`, "Environment alignment".
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (10): `MIPStarRE.LDT.Test.CascadeHypotheses` (Paper origin: `references/ldt-paper/inductive_step.tex:130-211` (`\label{eq:G-self-consistency}` through…); `MIPStarRE.LDT.Test.cascadeLine169RepairError` (Repaired line-169 error obtained by the checked local pre-completion route.); `MIPStarRE.LDT.Test.cascadeSigma` (Paper quantity `σ` (see `inductive_step.tex:189`), built from an incoming induction-step error `ν` and the main-induction exponential decay…); `MIPStarRE.LDT.Test.cascadeZeta1` (Paper quantity `ζ₁ = 2σ + 2·√(3ε + 2σ) + m·d/q` (see `inductive_step.tex:133`).); `MIPStarRE.LDT.Test.cascadeZeta2` (Formal Step 6 quantity `ζ₂ = 200·ζ₁^(1/4) + 42·ζ₁^(1/8)`.); `MIPStarRE.LDT.Test.cascadeZeta3` (Paper quantity `ζ₃ = 6·ζ₁ + 6·ζ₂` (see `inductive_step.tex:158`).); `MIPStarRE.LDT.Test.cascadeZeta4` (Paper quantity `ζ₄ = 2σ + 2·√(ζ₁ + ζ₃/2)` (see `inductive_step.tex:181`).); `MIPStarRE.LDT.Test.cascadeZeta4Repaired` (Repaired final point-consistency scalar obtained by substituting the checked line-169 repair error into the last Step 8 transport triangle.); `MIPStarRE.LDT.Test.mainFormalEnvelope` (The polynomial-exponent envelope common to all cascade bounds, `ε^(1/40000) + (d/q)^(1/40000) + exp(-k/(2560000 m²))`.); `MIPStarRE.LDT.Test.mainFormalError` (The formal final error envelope for `thm:main-formal`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.Definitions` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase

set_option backward.isDefEq.respectTransparency false

/-!
# Error cascade — core definitions

This module defines the central error quantities `mainFormalError`,
`mainFormalEnvelope`, the cascade variables `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄`,
and the `CascadeHypotheses` numeric regime used throughout the error-cascade
bookkeeping for Step 8 of `mainFormal`.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

/-- The formal final error envelope for `thm:main-formal`.

The sharper pre-completion line-169 repair keeps the point-transport scale at
the original `1/40000` exponent used by the surrounding Step 8 cascade. -/
noncomputable def mainFormalError (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
    (Real.rpow eps (1 / (40000 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (40000 : Error)) +
      Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))))

/-- The polynomial-exponent envelope common to all cascade bounds,
`ε^(1/40000) + (d/q)^(1/40000) + exp(-k/(2560000 m²))`. See
`mainFormalError_eq_envelope` for the identification
`mainFormalError = 100000 · k² · m⁴ · mainFormalEnvelope`. -/
noncomputable def mainFormalEnvelope (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  Real.rpow eps (1 / (40000 : Error)) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (40000 : Error)) +
    Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ)))))

/-- Paper quantity `σ` (see `inductive_step.tex:189`), built from an incoming
induction-step error `ν` and the main-induction exponential decay factor. -/
noncomputable def cascadeSigma (params : Parameters) (k : ℕ) (ν : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (ν + Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))

/-- Paper quantity `ζ₁ = 2σ + 2·√(3ε + 2σ) + m·d/q` (see `inductive_step.tex:133`). -/
noncomputable def cascadeZeta1 (params : Parameters) (eps σ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
    (params.m : Error) * (params.d : Error) / (params.q : Error)

/-- Formal Step 6 quantity
`ζ₂ = 200·ζ₁^(1/4) + 42·ζ₁^(1/8)`.

The paper prints coefficient `40` in `inductive_step.tex:149`; the extra `2`
absorbs the residual `+ 2ζ₁` term from completing an orthonormalized
submeasurement when `0 ≤ ζ₁ ≤ 1`. -/
noncomputable def cascadeZeta2 (ζ₁ : Error) : Error :=
  200 * Real.rpow ζ₁ (1 / (4 : Error)) + 42 * Real.rpow ζ₁ (1 / (8 : Error))

/-- Paper quantity `ζ₃ = 6·ζ₁ + 6·ζ₂` (see `inductive_step.tex:158`). -/
noncomputable def cascadeZeta3 (ζ₁ ζ₂ : Error) : Error :=
  6 * ζ₁ + 6 * ζ₂

/-- Paper quantity `ζ₄ = 2σ + 2·√(ζ₁ + ζ₃/2)` (see `inductive_step.tex:181`). -/
noncomputable def cascadeZeta4 (σ ζ₁ ζ₃ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (ζ₁ + ζ₃ / 2)

/-- Repaired line-169 error obtained by the checked local pre-completion route.

**Source:** This is source-faithful scalar bookkeeping for the repaired
line-169 route documented in `docs/paper-gaps/issue-1099-sharper-local-fix.tex`
and used in `references/ldt-paper/inductive_step.tex:167-173`.

Paper line 169 is printed with the exact error `ζ₁`; the checked local repair
instead yields `ζ₁ + 10·ζ₁^(1/8)`.  The additional term comes from
`sqrt (orthonormalizationError ζ₁) = sqrt (100·ζ₁^(1/4)) = 10·ζ₁^(1/8)` in
`ProjectivizationLine169Repair.leftConsistency_with_orthonormalization_loss`
and its Bob-side mirror.

This is an internal repaired-route scalar for the Step 6 transport.  It is not
the paper's printed line-169 parameter, and it is later absorbed into
`mainFormalError`. -/
noncomputable def cascadeLine169RepairError (ζ₁ : Error) : Error :=
  ζ₁ + 10 * Real.rpow ζ₁ (1 / (8 : Error))

/-- Repaired final point-consistency scalar obtained by substituting the checked
line-169 repair error into the last Step 8 transport triangle.

**Source:** This is source-faithful scalar bookkeeping for the repaired
line-169 route documented in `docs/paper-gaps/issue-1099-sharper-local-fix.tex`
and absorbed by the error cascade from
`references/ldt-paper/inductive_step.tex:186-234`.

The paper's `ζ₄` at `references/ldt-paper/inductive_step.tex:181` is
`2σ + 2·√(ζ₁ + ζ₃/2)`.  This repaired variant replaces `ζ₁` by the internal
checked line-169 repair error above, so it is likewise an internal scalar that
is subsequently absorbed into `mainFormalError` rather than a new paper-facing
theorem parameter. -/
noncomputable def cascadeZeta4Repaired (σ ζ₁ ζ₃ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (cascadeLine169RepairError ζ₁ + ζ₃ / 2)

/-- Paper origin: `references/ldt-paper/inductive_step.tex:130-211`
(`\label{eq:G-self-consistency}` through
`\label{eq:final-right-point-consistency}`, error cascade ζ₁–ζ₄); blueprint
`\label{def:main-formal-error-cascade}`.

**Source:** This is a faithful encoding of the standing scalar regime used in
the paper's error cascade, with the corrected large-\(k\) and nonzero-sampling
boundaries documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex`
and `docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`.

Standing numeric regime used throughout the cascade bounds: parameters
satisfy the unit scale, and `ε, d/q ∈ [0, 1]`. -/
structure CascadeHypotheses (params : Parameters) (k : ℕ) (eps : Error) : Prop where
  hk : 1 ≤ (k : Error)
  hm : 1 ≤ (params.m : Error)
  hepsNN : 0 ≤ eps
  hepsOne : eps ≤ 1
  hdq : (params.d : Error) ≤ (params.q : Error)
  hqPos : 0 < (params.q : Error)

namespace CascadeHypotheses

variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)

include h

end CascadeHypotheses

end Test

end MIPStarRE.LDT


