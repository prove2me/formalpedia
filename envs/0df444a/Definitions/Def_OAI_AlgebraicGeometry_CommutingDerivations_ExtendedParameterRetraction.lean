-- Prove2me | Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedParameterRetraction
-- name    : OAI_AlgebraicGeometry_CommutingDerivations_ExtendedParameterRetraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:38:20.108836+00:00
-- url     : https://prove2.me/theorems/e0d4f3cd-43f4-45c4-adda-10796cc64ab2
-- title:
--   The parameter $F_n+1$ and its retraction onto the first coordinate axis
-- statement:
--   Fix an integer $n\ge4$ and let $F_n\in\mathbb{C}[X_0,\dots,X_{n-1}]$ be the polynomial $F$ of the construction written in the first four variables $X_0,X_1,X_2,X_3$ in place of $h,u,v,w$. Let $\pi:\mathbb{C}[h,u,v,w]\to\mathbb{C}[t]$ be the four-variable slice retraction, $h\mapsto t$ and $u,v,w\mapsto0$. The file defines the following objects.
--
--   1. **The parameter.** The element $F_n+1\in\mathbb{C}[X_0,\dots,X_{n-1}]$.
--
--   2. **The slice retraction.** The $\mathbb{C}$-algebra homomorphism $\pi_n:\mathbb{C}[X_0,\dots,X_{n-1}]\to\mathbb{C}[t]$ with $\pi_n(X_0)=t$ and $\pi_n(X_i)=0$ for $1\le i\le n-1$, i.e. restriction to the line $(t,0,\dots,0)$.
--
--   It records the following identities: $\pi_n\bigl(q(X_0,X_1,X_2,X_3)\bigr)=\pi(q)$ for every $q\in\mathbb{C}[h,u,v,w]$, so $\pi_n$ extends $\pi$; $\pi_n(F_n+1)=t$; and
--
--   $$
--   \pi_n\bigl(q(F_n+1)\bigr)=q(t)\qquad\text{for every }q\in\mathbb{C}[t].
--   $$
--
--   As in four variables, $\pi_n$ is a left inverse of the substitution $q\mapsto q(F_n+1)$, so $\mathbb{C}[F_n+1]$ is a retract of $\mathbb{C}[X_0,\dots,X_{n-1}]$. This is used to show, in every dimension $n\ge4$, that an element of the polynomial ring whose image in the localization away from $F_n+1$ is a Laurent polynomial in $F_n+1$ is already an ordinary polynomial in $F_n$, which identifies the common kernel of the derivations with $\mathbb{C}[F_n]$.
--
--   **Formalization Note** Lean names: `extendedAmbientParameter` (defined as `extendedF hn + 1`), `extendedParameterSlice` ($\pi_n$; its hypothesis $4\le n$ is unused), and the lemmas `extendedParameterSlice_rename`, `extendedParameterSlice_parameter`, `extendedParameterSlice_aeval` and `extendedParameterSlice_aeval_apply`. The file also contains a private copy of the core lemma `if_neg` under the name `ite_eq_right`, used only inside a proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedParameterRetraction.lean

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedParameterRetraction.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! The explicit intersection proof retains every dimension n >= 4 and
identifies its ordinary polynomial side with the standard subalgebra C[F_n]. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

def extendedAmbientParameter {n : ℕ} (hn : 4 ≤ n) : MvPolynomial (Fin n) ℂ :=
  extendedF hn + 1

def extendedParameterSlice {n : ℕ} (_hn : 4 ≤ n) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i : Fin n => if i.val = 0 then Polynomial.X else 0)

theorem extendedParameterSlice_rename {n : ℕ} (hn : 4 ≤ n) (q : R) :
    extendedParameterSlice hn (MvPolynomial.rename (fourInclusion hn) q) = parameterSlice q := by
  unfold extendedParameterSlice parameterSlice
  rw [MvPolynomial.aeval_rename]
  have he : (fun i : Fin n => if i.val = 0 then (Polynomial.X : Polynomial ℂ) else 0) ∘
      fourInclusion hn = (fun i : Fin 4 => if i = 0 then Polynomial.X else 0) := by
    funext i
    change (if i.val = 0 then (Polynomial.X : Polynomial ℂ) else 0) =
      (if i = 0 then Polynomial.X else 0)
    by_cases hi : i = 0
    · subst i
      rfl
    · have hv : i.val ≠ 0 := fun hh => hi (Fin.ext hh)
      rw [ite_eq_right hv, ite_eq_right hi]
  rw [he]

@[simp] theorem extendedParameterSlice_parameter {n : ℕ} (hn : 4 ≤ n) :
    extendedParameterSlice hn (extendedAmbientParameter hn) = Polynomial.X := by
  have he : extendedAmbientParameter hn = MvPolynomial.rename (fourInclusion hn) ambientParameter := by
    simp [extendedAmbientParameter, extendedF, ambientParameter]
  rw [he, extendedParameterSlice_rename, parameterSlice_parameter]

theorem extendedParameterSlice_aeval {n : ℕ} (hn : 4 ≤ n) :
    (extendedParameterSlice hn).comp (Polynomial.aeval (extendedAmbientParameter hn)) =
      AlgHom.id ℂ (Polynomial ℂ) := by
  apply Polynomial.algHom_ext
  simp

@[simp] theorem extendedParameterSlice_aeval_apply {n : ℕ} (hn : 4 ≤ n) (q : Polynomial ℂ) :
    extendedParameterSlice hn (Polynomial.aeval (extendedAmbientParameter hn) q) = q :=
  AlgHom.congr_fun (extendedParameterSlice_aeval hn) q

end AbhyankarSathaye.CommutingDerivations

end

end OAI


