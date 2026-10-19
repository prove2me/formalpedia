-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
-- name    : MIPRE_Foundations_LowDegree_Anticomm
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:16.544693+00:00
-- url     : https://prove2.me/theorems/c1af2c23-6fc9-4273-9327-c0b4b47f0628
-- title:
--   Definitions of Anticomm: When is a Pauli-test question tuple anticommuting?
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.Anticomm` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). When is a Pauli-test question tuple anticommuting?. The Pauli basis test samples `ω = (u_X, u_Z, r_X, r_Z)` and the two Pauli operators it asks about commute or anticommute according to whether `γ(ω) = tr_{q → 2} \bigl( (r_X · ind_m(u_X)) · (r_Z · ind_m(u_Z)) \bigr)` vanishes. The paper's `fact:omega-anticomm-prob` says each case has probability at least `(1 - 3md/q)/2`; this file is that fact. `ind_m(x) ∈ 𝔽_q^{2^m}` is the vector of the subcube indicator polynomials of `MIPRE/Foundations/LowDegree/Encoding.lean` evaluated at an *arbitrary* point `x`, and the dot product of two of them is one…
--
--   **Definitions** (3): `MIPRE.LowDegree.acGamma` (`γ(ω)`, the quantity of the Pauli basis test whose vanishing says that the two Pauli operators of the tuple `ω = (u_X, u_Z, r_X, r_Z)`…); `MIPRE.LowDegree.indPair` (The dot product `ind_m(x) · ind_m(z)`, which is the `γ` of the Pauli basis test up to the scalars `r_X r_Z` and the trace.); `MIPRE.LowDegree.indVec` (`ind_m(x)`, the vector of the subcube indicator polynomials evaluated at `x`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.Anticomm` (`MIPRE/Foundations/LowDegree/Anticomm.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/Anticomm.lean; blueprint fact:omega-anticomm-prob

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/Anticomm.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel

/-!
# When is a Pauli-test question tuple anticommuting?

The Pauli basis test samples `ω = (u_X, u_Z, r_X, r_Z)` and the two Pauli operators it asks
about commute or anticommute according to whether

`γ(ω) = tr_{q → 2} \bigl( (r_X · ind_m(u_X)) · (r_Z · ind_m(u_Z)) \bigr)`

vanishes. The paper's `fact:omega-anticomm-prob` says each case has probability at least
`(1 - 3md/q)/2`; this file is that fact.

`ind_m(x) ∈ 𝔽_q^{2^m}` is the vector of the subcube indicator polynomials of
`MIPRE/Foundations/LowDegree/Encoding.lean` evaluated at an *arbitrary* point `x`, and the
dot product of two of them is one low-degree encoding evaluated at the other point
(`indPair_eq_eval`). So the fact is Schwartz--Zippel --- the encoding is a nonzero polynomial,
because `ind_m(x)` is never the zero vector (`sum_indVec`, whose value is `1`) --- together with
the count of `r` in the kernel of a nonzero `𝔽`-linear functional (`card_filter_ker_mul`).

Two departures from the paper, both recorded in the blueprint's comments on the fact:

* **the wasteful factor is dropped.** The paper states
  `(1 - q^{-m})(1 - q^{-1})(1 - md/q)/2`, whose first factor came from a case distinction on
  `u_X = 0` that its own `\cnote` then removes as vacuous. The bound proved here is
  `(1 - (m+1)/q)/2`, which is sharper than the paper's final `(1 - 3md/q)/2` and needs no such
  factor.
* **individual degree, not total degree.** The low-degree encoding is multilinear, so the
  Schwartz--Zippel step costs `m/q` rather than the `md/q` the paper spends. The paper's form is
  recovered in `prob_anticommuting_ge` for `1 ≤ d`.
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset MvPolynomial

/-! ## The indicator vector at an arbitrary point -/

section IndVec

variable {K : Type*} [CommRing K] {m : ℕ}

/-- `ind_m(x)`, the vector of the subcube indicator polynomials evaluated at `x`. For a subcube
point this is the standard basis vector at that point (`eval_ind`); the definition is what the
Pauli basis test uses at a general `x ∈ 𝔽_q^m`. -/
def indVec (x : Fin m → K) : (Fin m → Bool) → K := fun y => eval x (ind y)

/-- The dot product `ind_m(x) · ind_m(z)`, which is the `γ` of the Pauli basis test up to the
scalars `r_X r_Z` and the trace. -/
def indPair (x z : Fin m → K) : K := ∑ y, indVec x y * indVec z y

end IndVec

/-! ## The kernel of a nonzero linear functional -/

section Ker

/-! The kernel-index count is about a finite `𝔽`-vector space, not about a field extension: the
proof uses only the module structure and a vector off the kernel. It is stated that way because
the Weyl operators of `MIPRE/Foundations/Weyl.lean` need it on `n → 𝔽`, where the phase
`(-1)^{tr(a · b)}` is summed over a whole register rather than over a single field element. The
field-extension form below is the instance `V = K`. -/

section Module

variable {F V : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V] [Module F V]
  [Fintype V] [DecidableEq V]

end Module

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Fintype K]
  [DecidableEq K] [Algebra F K]

variable [FiniteDimensional F K] [Algebra.IsSeparable F K]

end Ker

/-! ## The fact -/

section Fact

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Fintype K]
  [DecidableEq K] [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K] {m d : ℕ}

/-- `γ(ω)`, the quantity of the Pauli basis test whose vanishing says that the two Pauli
operators of the tuple `ω = (u_X, u_Z, r_X, r_Z)` commute: the trace of the dot product of
`r_X · ind_m(u_X)` with `r_Z · ind_m(u_Z)`. -/
def acGamma (F : Type*) [Field F] [Algebra F K] (uX uZ : Fin m → K) (rX rZ : K) : F :=
  Algebra.trace F K (rX * rZ * indPair uX uZ)

/-! ### The Schwartz--Zippel step -/

/-! ### The two counts -/

/-! ### The fact -/

end Fact

end MIPRE.LowDegree

end


