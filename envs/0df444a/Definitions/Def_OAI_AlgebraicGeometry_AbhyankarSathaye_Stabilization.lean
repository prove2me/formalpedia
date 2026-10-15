-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization
-- name    : OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:32:11.258154+00:00
-- url     : https://prove2.me/theorems/a670161c-0bef-4233-8451-6ce778d39413
-- title:
--   Adjoining unused variables: the polynomial $F$ in $n\ge 4$ variables and its polynomial quotient
-- statement:
--   Fix a natural number $n\ge 4$ and write $\mathbb{C}[x_0,\dots,x_{n-1}]$ for the polynomial ring in $n$ variables. Let $R=\mathbb{C}[h,u,v,w]$ and let $F=h-P(x,y,s)-1\in R$ be the explicit polynomial (with $x=u^3+hv$, $y=-u^2+hw$, $s=S(h,u,v,w)$), whose quotient $R/(F)$ is isomorphic to $\mathbb{C}[X_0,X_1,X_2]$ via the fiber isomorphism.
--
--   1. **Inclusion of the first four indices.** $\iota:\{0,1,2,3\}\to\{0,\dots,n-1\}$, $\iota(i)=i$.
--   2. **The extended polynomial.** $F_n\in\mathbb{C}[x_0,\dots,x_{n-1}]$ is obtained from $F$ by renaming $h,u,v,w$ to $x_0,x_1,x_2,x_3$:
--   $$F_n=F(x_0,x_1,x_2,x_3).$$
--   3. **Splitting the ambient ring.** Separating the first four variables from the remaining $n-4$ gives a $\mathbb{C}$-algebra isomorphism
--   $$\mathbb{C}[x_0,\dots,x_{n-1}]\cong R[z_0,\dots,z_{n-5}],\qquad x_0,x_1,x_2,x_3\mapsto h,u,v,w,\quad x_{4+j}\mapsto z_j,$$
--   onto the polynomial ring over $R$ in $n-4$ variables (none when $n=4$), under which $F_n$ corresponds to the constant polynomial $F$.
--   4. **The stabilized isomorphism.** A $\mathbb{C}$-algebra isomorphism
--   $$\mathbb{C}[x_0,\dots,x_{n-1}]/(F_n)\ \cong\ \mathbb{C}[y_0,\dots,y_{n-2}],$$
--   obtained by composing item 3 on quotients, the identification $R[z]/(F)\cong(R/(F))[z]$, the fiber isomorphism applied to coefficients, and a regrouping of variables in which the three fiber coordinates become $y_0,y_1,y_2$ and $z_j$ becomes $y_{3+j}$.
--   5. **The extended point.** $p_n\in\mathbb{C}^n$ has coordinates $2,0,-\tfrac12,\tfrac12$ in positions $0,1,2,3$ and $0$ in every position $i\ge 4$.
--
--   Adjoining variables on which the polynomial does not depend preserves both features of the four-variable example. Item 4 shows that the hypersurface $F_n=0$ still has the coordinate ring of affine $(n-1)$-space, and $p_n$ is a point where $F_n=-1$ and all partial derivatives of $F_n$ vanish, which prevents $F_n$ from being a coordinate. This yields the example in every dimension $n\ge 4$.
--
--   **Formalization Note** The hypothesis $n\ge 4$ is the argument `hn : 4 ≤ n` of every definition; under it the natural-number subtractions $n-4$ and $n-1$ are exact. The items are `fourInclusion`, `extendedF`, `splitAmbient` (via `blocksToAmbient : Fin (n-4) ⊕ Fin 4 ≃ Fin n`, with lemmas `blocksToAmbient_original`, `blocksToAmbient_symm_original`, `splitAmbient_comp_original` and `splitAmbient_F`), `extendedFiberEquiv` (via `blocksToOutput : Fin (n-4) ⊕ Fin 3 ≃ Fin (n-1)`) and `extendedPoint`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Stabilization.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/AbhyankarSathaye/Stabilization.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AbhyankarSathaye mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_FiberFormulas
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LinearPresentation
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint

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

def fourInclusion {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt hn⟩

def extendedF {n : ℕ} (hn : 4 ≤ n) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.rename (fourInclusion hn) F

def blocksToAmbient {n : ℕ} (hn : 4 ≤ n) : Fin (n-4) ⊕ Fin 4 ≃ Fin n :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))

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

def blocksToOutput {n : ℕ} (hn : 4 ≤ n) : Fin (n-4) ⊕ Fin 3 ≃ Fin (n-1) :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))

def extendedFiberEquiv {n : ℕ} (hn : 4 ≤ n) :
    (MvPolynomial (Fin n) ℂ ⧸ Ideal.span {extendedF hn}) ≃ₐ[ℂ]
      MvPolynomial (Fin (n-1)) ℂ := by
  let J : Ideal (MvPolynomial (Fin (n-4)) R) := (Ideal.span {F}).map C
  have hi : J = (Ideal.span {extendedF hn}).map (splitAmbient hn : _ →+* _) := by
    simp [J, Ideal.map_span, splitAmbient_F]
  exact (Ideal.quotientEquivAlg (Ideal.span {extendedF hn}) J (splitAmbient hn) hi).trans
    (((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin (n-4))
      (Ideal.span {F})).restrictScalars ℂ).symm.trans
      ((MvPolynomial.mapAlgEquiv (Fin (n-4)) fiberEquiv).trans
        ((sumAlgEquiv ℂ (Fin (n-4)) (Fin 3)).symm.trans
          (renameEquiv ℂ (blocksToOutput hn)))))

def extendedPoint {n : ℕ} (_hn : 4 ≤ n) (i : Fin n) : ℂ :=
  if hi : i.val < 4 then criticalPoint ⟨i.val, hi⟩ else 0

end AbhyankarSathaye

end

end OAI


