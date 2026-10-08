-- Prove2me | Definitions.Def_OAICatalanChebyshevData
-- name    : OAICatalanChebyshevData
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-07T22:00:16.621483+00:00
-- url     : https://prove2.me/theorems/f82b20af-c3fa-437d-9a05-0a1991560d85
-- title:
--   OpenAI's Catalan Chebyshev data — explicit integer forms of T₂₃, T₂₄, U₂₂, U₂₃
-- statement:
--   Four explicit integer polynomials from OpenAI's Lean development `lean/OAI/NumberTheory/Catalan` (github.com/openai/math, Apache License 2.0), carved out without change: `fixedChebyshevTData_23`, `fixedChebyshevTData_24`, `fixedChebyshevUData_22`, `fixedChebyshevUData_23`, each a sum of monomials $c_jx^j$ in $\mathbb Z[x]$ with the integer coefficients written out.
--
--   They are OpenAI's typed data for the Chebyshev polynomials $T_{23}$, $T_{24}$ (first kind) and $U_{22}$, $U_{23}$ (second kind), which the per-row certificate of the paper's §4.4 uses to build the row polynomials $P_r=(1-t)^2t^{62}T_u(1/t)$ and $D_r=\operatorname{sgn}(r-4)(1-t)^2t^{62}U_{u-1}(1/t)$, $u=|r-4|$. That they equal the Chebyshev polynomials is not part of this bundle; it is stated by the published lemmas `OAI.InternalCatalan.fixed_chebyshevT_typed_23` and its three siblings.
--
--   **Source and credit.** OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math), [paper](https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf), §4.4, p. 23; Lean in `lean/OAI/NumberTheory/Catalan`, Apache License 2.0. The code of this bundle is OpenAI's, with comments removed.
--
--   **Formalization note.** The definitions live in OpenAI's namespace `OAI.InternalCatalan` under their own names; the bundle imports only Mathlib.
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), §4.4 p. 23 (integer Chebyshev polynomials used for the fixed rows); the definitions are OpenAI's Lean definitions, carved from the development

import Mathlib.Algebra.Polynomial.Coeff

/-!
# Catalan's constant is irrational: four Chebyshev polynomials

OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026,
https://github.com/openai/math (paper:
`preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf`).

The definitions below are taken from OpenAI's Lean development `lean/OAI/NumberTheory/Catalan`
in that repository (Apache License, Version 2.0), with comments removed and line-level edits for
this Lean and Mathlib version. They are the declarations needed to state the published lemmas
of the proof.
-/

section

namespace OAI

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedChebyshevTData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-23 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (2024 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-52624 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (631488 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-4209920 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (17145856 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-44843008 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (76873728 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-85917696 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (60293120 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-24117248 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (4194304 : ℤ)

def fixedChebyshevTData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-288 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (13728 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-256256 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (2471040 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-14057472 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (50692096 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-120324096 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (190513152 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-199229440 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (132120576 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-50331648 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (8388608 : ℤ)

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedChebyshevUData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (264 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-11440 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (192192 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-1647360 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (8200192 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (50135040 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-63504384 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (49807360 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-22020096 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (4194304 : ℤ)

def fixedChebyshevUData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-24 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (2288 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-64064 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (823680 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-5857280 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-70189056 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (127008768 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-149422080 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (110100480 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-46137344 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (8388608 : ℤ)

end InternalCatalan

end

end OAI

end


