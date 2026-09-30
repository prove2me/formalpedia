-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_MainTerm
-- name    : TauCeti_NumberTheory_NumberField_Global_RayClass_MainTerm
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:02:19.938763+00:00
-- url     : https://prove2.me/theorems/f5ee59df-6409-459c-a1a4-5f9ac6592b31
-- title:
--   The main term of the ray class ideal count
-- statement:
--   For a modulus $\mathfrak m$ of a number field $K$, let $h_{\mathfrak m}$ be its ray class number and $\rho_K$ the residue of the Dedekind zeta function at one. Define the ray-class main-term coefficient by
--
--   $$
--   c_{\mathfrak m}=\frac{\rho_K}{h_{\mathfrak m}}\prod_{P\mid\mathfrak m_0}\left(1-\frac1{\mathrm N P}\right).
--   $$
--
--   This is the coefficient of the linear main term in each ray-class ideal count.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/MainTerm.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/MainTerm.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The main term of the ray class ideal count

This file defines the main term of the ray class ideal count and proves it positive: the number
of integral ideals of a fixed ray class with absolute norm at most `x` is this coefficient times
`x`, up to a power-saving error; this is
`TauCeti.GlobalNumberFields.isBigO_rayClassIdealCountingFunction_sub`.

The coefficient is the Dedekind-zeta residue divided by the order of the ray class group, times
one correction factor `1 - (N 𝔭)⁻¹` for each prime `𝔭` in the support of the modulus.  The Euler
factor of `ζ_K` at `𝔭` is `(1 - N 𝔭 ^ (-s))⁻¹`, so deleting `𝔭` from the Euler product multiplies
`ζ_K s` by its reciprocal `1 - N 𝔭 ^ (-s)`; the factor above is that reciprocal at `s = 1`.  The
intended count runs over the ideals prime to the finite part of the modulus, which is what makes
those corrections the right ones.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm`: the coefficient.

## Main results

* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_eq`: the coefficient written out.
* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_one`: at the trivial modulus it is the
  Dedekind-zeta residue over the class number.
* `TauCeti.GlobalNumberFields.rayClassIdealMainTerm_pos`: it is positive.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VIII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

 section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The coefficient intended as the main term of the ray class ideal count: the Dedekind-zeta
residue of `K`, divided by the order of the ray class group of `𝔪`, times one correction factor
`1 - (N 𝔭)⁻¹` — the reciprocal Euler factor at `s = 1` — for each prime `𝔭` in the support of
`𝔪`. -/
noncomputable def rayClassIdealMainTerm (𝔪 : Modulus K) : ℝ :=
  dedekindZeta_residue K / (Nat.card (RayClassGroup 𝔪) : ℝ) *
    ∏ v ∈ 𝔪.support, (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)







end TauCeti.GlobalNumberFields

end
end


