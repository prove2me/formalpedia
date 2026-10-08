-- Prove2me | Definitions.Def_FenchelRobust_Counterpart_Model
-- name    : FenchelRobust_Counterpart_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:08:41.971257+00:00
-- url     : https://prove2.me/theorems/b42317a3-8613-4364-906d-eef4e7180958
-- title:
--   Affine uncertainty set, regularity, robust constraint, and Fenchel counterpart
-- statement:
--   Let $a^0\in\mathbb R^m$, $A\in\mathbb R^{m\times L}$, and $Z\subseteq\mathbb R^L$. The **uncertainty set** is
--   $$U=\{a^0+A\zeta:\zeta\in Z\}.$$
--   For each decision $x\in\mathbb R^n$, let $D(x)$ be the effective domain of $f(\cdot,x)$. The nominal vector is **regular** when $a^0\in\operatorname{ri}D(x)$ for every $x$. The **robust constraint** requires $f(a,x)\le0$ for every $a\in U\cap D(x)$; outside $D(x)$ the paper assigns $f(a,x)=-\infty$.
--
--   The worst-case value is $F(x)=\sup_{a\in U\cap D(x)}f(a,x)$. The **Fenchel robust counterpart** at $(x,v)$ is
--   $$ (a^0)^Tv+\delta^*(A^Tv\mid Z)-f_*(v,x)\le0, $$
--   where $f_*(v,x)=\inf_{a\in D(x)}(a^Tv-f(a,x))$. These definitions share one domain map, so no value of the real representative of $f$ is used outside its effective domain.
--
--   **Formalization Note.** Both extrema and the counterpart value are extended real. The paper's nominal-vector regularity quantifies over every decision $x$.
-- source:
--   Ben-Tal, den Hertog, Vial, Deriving robust counterparts of nonlinear uncertain inequalities, CentER Discussion Paper 2012-053 (July 2, 2012), pp. 3–4, Eqs. (5), (6), (8), (12), Definition 1

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_ConvexDuality

namespace FenchelRobust.Counterpart

/-- The affine uncertainty set of Section 2. -/
def uncertaintySet {m L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ)) : Set (Fin m → ℝ) :=
  {a | ∃ ζ ∈ Z, a = a0 + Matrix.mulVec A ζ}

/-- Definition 1: the nominal vector is regular for every decision. -/
def Regular {m n : ℕ} (a0 : Fin m → ℝ)
    (D : (Fin n → ℝ) → Set (Fin m → ℝ)) : Prop :=
  ∀ x, a0 ∈ intrinsicInterior ℝ (D x)

/-- The robust constraint (6), with values outside the effective domain interpreted as `-∞`. -/
def RobustFeasible {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ a ∈ uncertaintySet a0 A Z, a ∈ D x → f a x ≤ 0

/-- The extended-real worst-case value in (8) and (13). -/
noncomputable def worstCase {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : EReal :=
  ⨆ a ∈ uncertaintySet a0 A Z ∩ D x, (f a x : EReal)

/-- The extended-real left side of the Fenchel robust counterpart (12). -/
noncomputable def frcValue {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (v : Fin m → ℝ) : EReal :=
  ((a0 ⬝ᵥ v : ℝ) : EReal) + supportFun Z (Matrix.mulVec A.transpose v) -
    concaveConj (D x) (fun a => f a x) v

end FenchelRobust.Counterpart


