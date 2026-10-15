-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization__CommutingDerivations
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization__CommutingDerivations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:35:14.583978+00:00
-- url     : https://prove2.me/theorems/76427261-dfc9-41a9-8b74-47135bb42268
-- title:
--   Splitting $\mathbb{C}[X_0,\dots,X_{n-1}]$ over $\mathbb{C}[h,u,v,w]$ and the extended critical point
-- statement:
--   Fix an integer $n\ge4$ and let $R=\mathbb{C}[h,u,v,w]$. Identify $h,u,v,w$ with the first four variables $X_0,X_1,X_2,X_3$ of $\mathbb{C}[X_0,\dots,X_{n-1}]$, and let $F_n$ be the image of the polynomial $F\in R$ of the construction under this inclusion. The variables are indexed by the disjoint union $\{0,\dots,n-5\}\sqcup\{0,1,2,3\}$ through the bijection that sends $i$ in the second block to $i$ and $j$ in the first block to $4+j$. The file contains the following.
--
--   1. **Block bookkeeping.** Lemmas stating that this bijection restricts to the inclusion $\{0,1,2,3\}\hookrightarrow\{0,\dots,n-1\}$ on the second block, and dually that its inverse sends each $i\in\{0,1,2,3\}$ back to the second block.
--
--   2. **Splitting isomorphism.** The $\mathbb{C}$-algebra isomorphism
--
--      $$\Sigma_n:\mathbb{C}[X_0,\dots,X_{n-1}]\xrightarrow{\ \sim\ }R[Z_0,\dots,Z_{n-5}],\qquad (X_0,X_1,X_2,X_3)\mapsto(h,u,v,w),\quad X_{4+j}\mapsto Z_j,$$
--
--      which treats the first four variables as coefficients and the last $n-4$ as new variables (for $n=4$ there are none). Its restriction to the copy of $R$ in the first four variables is the constant embedding $R\to R[Z_0,\dots,Z_{n-5}]$; in particular $\Sigma_n(F_n)=F$, a constant polynomial.
--
--   3. **Extended critical point.** The point $\mathbf{c}^{(n)}=(2,0,-\tfrac12,\tfrac12,0,\dots,0)\in\mathbb{C}^n$, i.e. the critical point $(2,0,-\tfrac12,\tfrac12)$ of $F$ followed by $n-4$ zeros.
--
--   These objects stabilize the four-dimensional construction to every dimension $n\ge4$. Through $\Sigma_n$, the quotient of $\mathbb{C}[X_0,\dots,X_{n-1}]$ by $F_n$ becomes $(R/(F))[Z_0,\dots,Z_{n-5}]$, a polynomial algebra in $n-1$ variables because $R/(F)$ is one in three variables; and since $F_n$ does not involve $X_4,\dots,X_{n-1}$, the point $\mathbf{c}^{(n)}$ is still a critical point of $F_n$ with value $-1$, so $F_n$ is not a coordinate.
--
--   **Formalization Note** The bijection is `blocksToAmbient` from the base file, built from `Equiv.sumComm`, `finSumFinEquiv` and a cast from `Fin (4 + (n - 4))` to `Fin n`; the lemmas of item 1 are `blocksToAmbient_original` and `blocksToAmbient_symm_original`. The isomorphism `splitAmbient` is a renaming followed by Mathlib's `sumAlgEquiv`, and `splitAmbient_comp_original` and `splitAmbient_F` are the statements of item 2. `extendedPoint` takes the hypothesis $4\le n$ as an unused argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Stabilization.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Stabilization.lean by skeleton subtraction
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

namespace OAI

/-!
# Adjoining unused variables

For every `n ≥ 4`, renaming `F` into the first four variables gives a quotient
isomorphic to a polynomial algebra in `n - 1` variables. The extended critical
point still has value `-1` and zero gradient, so the polynomial is not a coordinate.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial

theorem blocksToAmbient_original {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    blocksToAmbient hn (Sum.inr i) = fourInclusion hn i := by
  apply Fin.ext
  rfl

theorem blocksToAmbient_symm_original {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    (blocksToAmbient hn).symm (fourInclusion hn i) = Sum.inr i := by
  rw [← blocksToAmbient_original hn i, Equiv.symm_apply_apply]

def splitAmbient {n : ℕ} (hn : 4 ≤ n) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin (n-4)) R :=
  (renameEquiv ℂ (blocksToAmbient hn).symm).trans
    (sumAlgEquiv ℂ (Fin (n-4)) (Fin 4))

theorem splitAmbient_comp_original {n : ℕ} (hn : 4 ≤ n) :
    (splitAmbient hn).toAlgHom.comp (rename (fourInclusion hn)) =
      IsScalarTower.toAlgHom ℂ R (MvPolynomial (Fin (n-4)) R) := by
  apply MvPolynomial.algHom_ext
  intro i
  change sumAlgEquiv ℂ (Fin (n-4)) (Fin 4)
    (rename (blocksToAmbient hn).symm (rename (fourInclusion hn) (X i))) = C (X i)
  rw [rename_X, rename_X, blocksToAmbient_symm_original]
  exact sumAlgEquiv_X_inr ℂ (Fin (n-4)) (Fin 4) i

theorem splitAmbient_F {n : ℕ} (hn : 4 ≤ n) : splitAmbient hn (extendedF hn) = C F :=
  AlgHom.congr_fun (splitAmbient_comp_original hn) F

def extendedPoint {n : ℕ} (_hn : 4 ≤ n) (i : Fin n) : ℂ :=
  if hi : i.val < 4 then criticalPoint ⟨i.val, hi⟩ else 0

end AbhyankarSathaye

end

end OAI


