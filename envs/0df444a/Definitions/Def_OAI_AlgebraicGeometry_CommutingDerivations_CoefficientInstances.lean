-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_CoefficientInstances
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_CoefficientInstances
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:26:52.398575+00:00
-- url     : https://prove2.me/theorems/72c7ab63-cfcc-4c37-97e2-83a85ba7b05a
-- title:
--   The Laurent polynomial ring $\mathbb{C}[t,t^{-1}]$ is an integral domain of characteristic zero
-- statement:
--   Let $\Lambda$ be the ring of complex Laurent polynomials, realized as the localization of $\mathbb{C}[t]$ at the powers of $t$:
--   $$\Lambda=\mathbb{C}[t]\bigl[t^{-1}\bigr]=\mathbb{C}[t,t^{-1}] .$$
--   The file records two structural facts about $\Lambda$.
--
--   1. $\Lambda$ is an integral domain, because it is the localization of the domain $\mathbb{C}[t]$ at the nonzero element $t$.
--   2. $\Lambda$ has characteristic zero, because the structure map $\mathbb{C}\to\Lambda$ is injective.
--
--   These are exactly the hypotheses under which, in a polynomial ring $\Lambda[Z_1,\dots,Z_m]$, an element annihilated by every partial derivative must be a constant in $\Lambda$. That fact identifies the common kernel of the localized coordinate derivations with the Laurent coefficient ring, which is ultimately how the common kernel $\mathbb{C}[F]$ is computed.
--
--   **Formalization Note** The two facts are the type-class instances `laurentCoefficients_isDomain` and `laurentCoefficients_charZero` on `LaurentCoefficients`. They are declared as instances so that later lemmas requiring `IsDomain` and `CharZero` apply automatically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/CoefficientInstances.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/CoefficientInstances.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CommutingDerivations mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBezout
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationSetup

namespace OAI

/-! The concrete Laurent coefficient ring is a characteristic-zero domain.
These instances are consequences of its actual localization construction. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

instance laurentCoefficients_isDomain : IsDomain LaurentCoefficients :=
  Localization.Away.isDomain (Polynomial.X_ne_zero : (Polynomial.X : Polynomial ℂ) ≠ 0)

instance laurentCoefficients_charZero : CharZero LaurentCoefficients :=
  charZero_of_injective_algebraMap (algebraMap ℂ LaurentCoefficients).injective

end AbhyankarSathaye.CommutingDerivations

end

end OAI


