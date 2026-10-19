-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:16.042971+00:00
-- url     : https://prove2.me/theorems/09f18e57-8bbd-44be-9ade-8d0e2ae1a5ae
-- title:
--   Definitions of Polynomials: Polynomial preliminaries Packages the paper's low-individual-degree polynomial class together with Schwartz-Zippel…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Polynomials` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Polynomial preliminaries. Packages the paper's low-individual-degree polynomial class together with Schwartz-Zippel bounds as thin wrappers around Mathlib's existing multivariate polynomial theorems.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (2): `MIPStarRE.LDT.Preliminaries.polyFunc` (`\polyfunc{m}{q}{d}` from the paper's definition of low-individual-degree polynomials.); `MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability` (The uniform agreement probability of two polynomials on `K^m`, written as a finite cardinality ratio over `K^m`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Polynomials` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/Polynomials.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Polynomials.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Polynomial preliminaries

Packages the paper's low-individual-degree polynomial class together
with Schwartz-Zippel bounds as thin wrappers around Mathlib's existing
multivariate polynomial theorems.

## References

* `references/ldt-paper/preliminaries.tex`, Section 3 (Preliminaries)
-/

open Finset Fintype

open scoped BigOperators

namespace MIPStarRE.LDT.Preliminaries

open MvPolynomial

/-- `\polyfunc{m}{q}{d}` from the paper's definition of low-individual-degree
polynomials. This is Mathlib's `MvPolynomial.restrictDegree` submodule. -/
noncomputable abbrev polyFunc (m : ℕ) (K : Type*) [CommSemiring K] (d : ℕ) :
    Submodule K (MvPolynomial (Fin m) K) :=
  MvPolynomial.restrictDegree (Fin m) K d

/-- The uniform agreement probability of two polynomials on `K^m`, written as a
finite cardinality ratio over `K^m`. -/
noncomputable def polynomialAgreementProbability (m : ℕ) (K : Type*) [Field K] [Fintype K]
    [DecidableEq K] (g h : MvPolynomial (Fin m) K) : ℚ≥0 :=
  #{x ∈ (Finset.univ : Finset (Fin m → K)) |
      MvPolynomial.eval x g = MvPolynomial.eval x h} /
    (Fintype.card K ^ m : ℚ≥0)

end MIPStarRE.LDT.Preliminaries


