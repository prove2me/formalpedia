-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_OrdinaryExtraMain
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_OrdinaryExtraMain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:42:30.242916+00:00
-- url     : https://prove2.me/theorems/fb49b58e-d6ce-4b43-bdcc-fce1e149717b
-- title:
--   Derivation families whose extra members are the ordinary coordinate partials, with matching clearing exponents
-- statement:
--   Fix $n\ge 4$ and let $A_n=\mathbb{C}[X_0,\dots,X_{n-1}]$. The $n-1$ slots $k=0,1,\dots,n-2$ of a family of derivations are split into three *core* slots $k\in\{0,1,2\}$ and $n-4$ *extra* slots $k=3+i$ with $0\le i<n-4$. In the same way the variables split into the four core variables $X_0,\dots,X_3$, which carry the polynomial $F_n=F(X_0,X_1,X_2,X_3)$ of the main construction, and the $n-4$ extra variables $X_{4+i}$. The file defines two objects.
--
--   1. **Family with ordinary extras.** Given any family $d=(d_0,\dots,d_{n-2})$ of $\mathbb{C}$-linear derivations of $A_n$, the family $d^{\mathrm{ord}}=(d^{\mathrm{ord}}_0,\dots,d^{\mathrm{ord}}_{n-2})$ keeps the core members of $d$ and replaces each extra member by the ordinary partial derivative in the corresponding extra variable:
--
--      $$d^{\mathrm{ord}}_k=d_k\quad(0\le k\le 2),\qquad d^{\mathrm{ord}}_{3+i}=\frac{\partial}{\partial X_{4+i}}\quad(0\le i<n-4).$$
--
--   2. **Clearing exponent.** Given $N\in\mathbb{N}$, the exponent attached to slot $k$ is
--
--      $$e_N(k)=N\quad(0\le k\le 2),\qquad e_N(3+i)=0\quad(0\le i<n-4).$$
--
--   In the construction of the commuting family, the partial derivatives $D_0,\dots,D_{n-2}$ in Laurent coordinates on the localization $A_n[(F_n+1)^{-1}]$, with localization map $\lambda$, are multiplied by a common power $(F_n+1)^N$ so that they restrict to derivations $d_k$ of $A_n$ with $\lambda(d_k(a))=\lambda(F_n+1)^N D_k(\lambda(a))$. In the extra directions the localized derivative $D_{3+i}$ already restricts to $\partial/\partial X_{4+i}$, so no denominator has to be cleared there. The pair $(d^{\mathrm{ord}},e_N)$ records this: for every slot $k$ and every $a\in A_n$ one has $\lambda(d^{\mathrm{ord}}_k(a))=\lambda(F_n+1)^{e_N(k)}D_k(\lambda(a))$, and the final family contains the ordinary coordinate partials $\partial/\partial X_{4+i}$ verbatim as its members with index $3+i$.
--
--   **Formalization Note** The Lean names are `withOrdinaryExtras hn d` and `extraClearingExponent hn N`, where `hn : 4 ≤ n`. Slots and variables are split with the equivalences `blocksToOutput hn : Fin (n-4) ⊕ Fin 3 ≃ Fin (n-1)`, which sends the extra index $i$ to $3+i$ and the core index $j$ to $j$, and `blocksToAmbient hn : Fin (n-4) ⊕ Fin 4 ≃ Fin n`, which sends $i$ to $4+i$ and $j$ to $j$. The members of $d$ in the extra slots are discarded. The displayed relation with the localized derivatives is not part of the definitions; it is proved where they are used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/OrdinaryExtraMain.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/OrdinaryExtraMain.lean by skeleton subtraction
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
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_CoefficientInstances
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBridge
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationEquivalence
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedLocalization
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ConcreteKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_DerivationOperations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizedPartials

namespace OAI

/-! The all-dimensional family may be chosen with the additional n-4
directions literally equal to the ordinary ambient coordinate partials. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

def withOrdinaryExtras {n : ℕ} (hn : 4 ≤ n)
    (d : Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ)) :
    Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) :=
  fun k => match (blocksToOutput hn).symm k with
    | Sum.inl i => pderiv (blocksToAmbient hn (Sum.inl i))
    | Sum.inr _ => d k

def extraClearingExponent {n : ℕ} (hn : 4 ≤ n) (N : ℕ) (k : Fin (n-1)) : ℕ :=
  match (blocksToOutput hn).symm k with
  | Sum.inl _ => 0
  | Sum.inr _ => N

end AbhyankarSathaye.CommutingDerivations

end

end OAI


