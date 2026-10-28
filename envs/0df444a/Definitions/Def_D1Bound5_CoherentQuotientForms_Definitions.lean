-- Prove2me | Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
-- name    : D1Bound5_CoherentQuotientForms_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:31:26.427949+00:00
-- url     : https://prove2.me/theorems/91416e2b-2576-428a-a2dc-a36042d4b9b8
-- title:
--   Coherent Quotient Forms
-- statement:
--   The actual quotient-weighted coherent form in the manuscript. The named objects in this bundle include `coherentQuotientForm`.
-- source:
--   D1Bound5/CoherentQuotientForms.lean, lines 10-16, SHA-256 392bcc4a54c87594a3594b5daa5b4ef8fcad70a5934eefb672cd5a7b190f86a4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The actual quotient-weighted coherent form in the manuscript. -/
noncomputable def coherentQuotientForm {m : ℕ} (a : Fin m → ℂ)
    (Delta p q eta : ℂ) : ℂ :=
  -Delta * coherentTerminalRoot p q eta +
    ∑ i, (Delta * (a i) ^ (m - 2) /
      (∏ j ∈ Finset.univ.erase i, (a i - a j))) *
        coherentAnchorRoot (a i) p q eta









end D1Bound5
end


