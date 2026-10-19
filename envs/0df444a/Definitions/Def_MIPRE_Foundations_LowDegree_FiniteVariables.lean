-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
-- name    : MIPRE_Foundations_LowDegree_FiniteVariables
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:23.403079+00:00
-- url     : https://prove2.me/theorems/b803de75-3926-436c-933e-f6fdbfa97708
-- title:
--   Definitions of FiniteVariables: Restricting polynomials to an embedded set of variables Setting all other variables to zero preserves every…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.FiniteVariables` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Restricting polynomials to an embedded set of variables. Setting all other variables to zero preserves every individual-degree bound. This lets circuit polynomials be written with natural-number input and gate indices, then restricted to the exact finite variable count used by the PCP.
--
--   **Definitions** (1): `MIPRE.LowDegree.extendZero` (Extend values by zero outside an embedded set of coordinates.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `extendZero_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.FiniteVariables` (`MIPRE/Foundations/LowDegree/FiniteVariables.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/FiniteVariables.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/FiniteVariables.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

/-!
# Restricting polynomials to an embedded set of variables

Setting all other variables to zero preserves every individual-degree bound.
This lets circuit polynomials be written with natural-number input and gate
indices, then restricted to the exact finite variable count used by the PCP.
-/

noncomputable section

namespace MIPRE.LowDegree

open MvPolynomial
open scoped Classical

variable {σ τ F : Type*} [CommRing F] {f : σ → τ} (hf : Function.Injective f)

/-- Extend values by zero outside an embedded set of coordinates. -/
def extendZero (x : σ → F) (j : τ) : F :=
  if h : j ∈ Set.range f then x ((Equiv.ofInjective f hf).symm ⟨j, h⟩) else 0

@[simp] theorem extendZero_apply (x : σ → F) (i : σ) : extendZero hf x (f i) = x i := by
  simp [extendZero, Equiv.ofInjective_symm_apply]

end MIPRE.LowDegree

end


