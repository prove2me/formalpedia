-- Prove2me | Definitions.Def_DouglasRachfordPPA_GenDR_Operators
-- name    : DouglasRachfordPPA_GenDR_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:03:43.471903+00:00
-- url     : https://prove2.me/theorems/749b8a0e-9b96-4555-b457-ce662ddc290c
-- title:
--   Operators as graphs: identity, scaling, sum, inverse, image, resolvent, (firmly) nonexpansive
-- statement:
--   Let $\mathcal H$ be a real inner product space. Following Eckstein and Bertsekas, an **operator** on $\mathcal H$ is any subset $T$ of $\mathcal H\times\mathcal H$ (its graph), with $Tx=\{y \mid (x,y)\in T\}$; it may be multivalued and need not be defined everywhere. This file fixes the operations on operators used in §2 of the paper.
--
--   1. The **identity** $I=\{(x,x)\mid x\in\mathcal H\}$.
--   2. For $c\in\mathbb R$, the **scaled operator** $cT=\{(x,cy)\mid (x,y)\in T\}$.
--   3. The **sum** $A+B=\{(x,y+z)\mid (x,y)\in A,\ (x,z)\in B\}$; its domain is $\operatorname{dom}A\cap\operatorname{dom}B$.
--   4. The **inverse** $T^{-1}=\{(y,x)\mid (x,y)\in T\}$.
--   5. The **image** $\operatorname{im}T=\{y\mid \exists x,\ (x,y)\in T\}$.
--   6. The **resolvent** $J_{cT}=(I+cT)^{-1}$, built from items 1–4; it equals $\{(x+cy,\,x)\mid (x,y)\in T\}$.
--   7. $T$ is **single-valued** if $Tx$ has at most one element for every $x$.
--   8. $C$ is **nonexpansive** if
--   $$\|y'-y\|\le\|x'-x\|\qquad\forall (x,y),(x',y')\in C.$$
--   9. $J$ is **firmly nonexpansive** if
--   $$\|y'-y\|^2\le\langle x'-x,\ y'-y\rangle\qquad\forall (x,y),(x',y')\in J.$$
--
--   These are graph notions: a (firmly) nonexpansive operator need not have full domain. Combined operators such as $2J-I$, $I-J$, $\tfrac12(C+I)$ and $K^{-1}-I$ are written with the sum, scaling, identity and inverse above, exactly as the paper writes them. Monotonicity, maximal monotonicity, $\operatorname{dom}$ and $\operatorname{zer}$ are the published definitions `ThreeOpSplitting_Convergence_MonotoneOperators`.
--
--   **Formalization Note** An operator is a map `H → Set H`; its graph is $\{(x,y)\mid y\in Tx\}$. Lean's `λ` is a keyword, so later files call the paper's $\lambda$ `lam`.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), pp. 3–5, §2 (operators, dom, im, inverse, cT, A+B, I, resolvent J_{cT}, nonexpansive, firmly nonexpansive)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

open InnerProductSpace

namespace DouglasRachfordPPA.GenDR

/-! Operators on `H` are subsets of `H × H`, encoded as `T : H → Set H` with graph
`{(x, y) | y ∈ T x}` (Eckstein–Bertsekas, pp. 3–5). Monotonicity, maximality, `dom` and `zer`
are the published `ThreeOpSplitting.Convergence` notions. -/

/-- The identity operator `I = {(x, x) | x ∈ H}`. -/
def opId {H : Type*} : H → Set H := fun x => {x}

/-- The scaled operator `cT = {(x, c y) | (x, y) ∈ T}`. -/
def opSmul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (T : H → Set H) : H → Set H :=
  fun x => {w | ∃ y ∈ T x, w = c • y}

/-- The sum `A + B = {(x, y + z) | (x, y) ∈ A, (x, z) ∈ B}`; its domain is `dom A ∩ dom B`. -/
def opAdd {H : Type*} [Add H] (A B : H → Set H) : H → Set H :=
  fun x => {w | ∃ y ∈ A x, ∃ z ∈ B x, w = y + z}

/-- The inverse `T⁻¹ = {(y, x) | (x, y) ∈ T}`. -/
def opInv {H : Type*} (T : H → Set H) : H → Set H := fun y => {x | y ∈ T x}

/-- The image (range) `im T = {y | ∃ x, (x, y) ∈ T}`. -/
def imOp {H : Type*} (T : H → Set H) : Set H := {y | ∃ x, y ∈ T x}

/-- The resolvent `J_{cT} = (I + cT)⁻¹`, as an operator (a graph, possibly multivalued and
not everywhere defined). -/
def opResolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) (T : H → Set H) : H → Set H :=
  opInv (opAdd opId (opSmul c T))

/-- An operator `T` is single-valued if `T x` has at most one element for every `x`. -/
def IsSingleValuedOp {H : Type*} (T : H → Set H) : Prop :=
  ∀ x y y' : H, y ∈ T x → y' ∈ T x → y = y'

/-- An operator `C` is nonexpansive if `‖y' - y‖ ≤ ‖x' - x‖` for all `(x, y), (x', y') ∈ C`. -/
def IsNonexpansiveOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : H → Set H) : Prop :=
  ∀ x x' y y' : H, y ∈ C x → y' ∈ C x' → ‖y' - y‖ ≤ ‖x' - x‖

/-- An operator `J` is firmly nonexpansive if `‖y' - y‖² ≤ ⟪x' - x, y' - y⟫` for all
`(x, y), (x', y') ∈ J`. -/
def IsFirmlyNonexpansiveOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : H → Set H) : Prop :=
  ∀ x x' y y' : H, y ∈ J x → y' ∈ J x' → ‖y' - y‖ ^ 2 ≤ ⟪x' - x, y' - y⟫_ℝ

end DouglasRachfordPPA.GenDR


