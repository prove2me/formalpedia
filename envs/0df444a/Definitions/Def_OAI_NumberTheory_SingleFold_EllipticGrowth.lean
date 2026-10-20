-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
-- name    : OAI_NumberTheory_SingleFold_EllipticGrowth
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:23:19.221079+00:00
-- url     : https://prove2.me/theorems/93d51302-024b-4a96-b86d-2d5443b49f8b
-- title:
--   Height sequences along a rank-one elliptic curve
-- statement:
--   Let $E$ be the elliptic curve $y^2=x^3-25x$ over $\mathbb{Q}$, with point at infinity $O$. Fix an isomorphism $f:E(\mathbb{Q})\cong\mathbb{Z}\times T$ with $T$ finite, and let $P=f^{-1}(1,0)$.
--
--   1. $H_x(O)=1$ and $H_x(x,y)=\max(|\mathrm{num}(x)|,\mathrm{den}(x))$. For $m\in\mathbb{N}$ let $W_m(Q)=H_x(mQ)$ and $s_m(j)=W_m(jP)$. The index of $Q$ is its $\mathbb{Z}$-coordinate.
--   2. **Representative.** $Q$ is a representative for $m$ if $Q\ne O$, $y(Q)\ge0$, $W_m(Q)>1$, and for every torsion point $t$ the point $Q+t$ is nonzero with $x(Q+t)\le x(Q)$.
--   3. **Bracket.** $Q$ brackets $u$ if
--   $$
--   W_m(Q)\le u+W_m(P)<\max\bigl(W_m(Q+P),W_m(Q-P)\bigr) .
--   $$
--   4. **Window.** $(Q,R)$ is a $\kappa$-window if $W_m(2Q)W_m(R)W_m(P)$ and $W_m(Q)^2\max(W_m(R\pm P))$ are within a factor $\kappa$ of each other. A growth pair is a bracketing representative together with a representative forming a window with it.
--
--   These relations encode, by polynomial conditions on point codes, the index of a point. They yield a single-fold representation of a function of super-polynomial but controlled growth.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticGrowth.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticGrowth.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.EllipticModel
open WeierstrassCurve.Affine.Point
abbrev E := CurveHeight.E

def Hx : E.Point → ℕ
  | zero => 1
  | WeierstrassCurve.Affine.Point.some x _ _ => max x.num.natAbs x.den
variable {T : Type} [AddCommGroup T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
noncomputable def point (n : ℤ) (t : T) : E.Point := f.symm (fun _ => n,t)
noncomputable def P : E.Point := point f 1 0
noncomputable def index (Q : E.Point) : ℤ := (f Q).1 0
noncomputable def W (m : ℕ) (Q : E.Point) : ℕ := Hx (m • Q)
noncomputable def sequence (m : ℕ) (j : ℕ) : ℕ := W m (j • P f)
noncomputable def xcoord : E.Point → ℚ
  | .zero => 0
  | .some x _ _ => x
noncomputable def ycoord : E.Point → ℚ
  | .zero => 0
  | .some _ y _ => y
def Representative (m : ℕ) (Q : E.Point) : Prop :=
  Q≠0 ∧ 0≤ycoord Q ∧ 1<W m Q ∧
  ∀ t : T, Q+point f 0 t≠0 ∧ xcoord (Q+point f 0 t)≤xcoord Q
def Bracket (m u : ℕ) (Q : E.Point) : Prop :=
  W m Q ≤ u+W m (P f) ∧ u+W m (P f) < max (W m (Q+P f)) (W m (Q-P f))
def Window (m κ : ℕ) (Q R : E.Point) : Prop :=
  W m (2 • Q)*W m R*W m (P f) ≤ κ*(W m Q^2*max (W m (R+P f)) (W m (R-P f))) ∧
  W m Q^2*max (W m (R+P f)) (W m (R-P f)) ≤ κ*(W m (2 • Q)*W m R*W m (P f))
def GrowthPair (m κ u : ℕ) (A : E.Point × E.Point) : Prop :=
  Representative f m A.1 ∧ Bracket f m u A.1 ∧ Representative f m A.2 ∧ Window f m κ A.1 A.2

end SingleFold.EllipticModel

namespace SingleFold.GrowthCompilation
open Compiler PointCompiler
abbrev E := EllipticModel.E
section
variable {T α : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
variable {Q R : (α → ℕ) → E.Point}
end

section
variable {T : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
end

end SingleFold.GrowthCompilation

end OAI


