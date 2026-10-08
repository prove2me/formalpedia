-- Prove2me | Definitions.Def_BertsekasShreve_AnalyticSelection_LowerSemianalytic
-- name    : BertsekasShreve_AnalyticSelection_LowerSemianalytic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:35.352025+00:00
-- url     : https://prove2.me/theorems/7091fb27-65e8-4153-a8c0-acf71f518e32
-- title:
--   Lower semianalytic functions (Definition 7.21), the partial infimum $f^*(x)=\inf_{y\in D_x}f(x,y)$, and the attainment set $I$
-- statement:
--   Let $X$ be a Borel space, $D\subseteq X$, and $f:D\to R^*$, where $R^*=[-\infty,\infty]$.
--
--   1. (**Definition 7.21**) $f$ is **lower semianalytic** if $D$ is analytic and the set
--   $$\{x\in D\mid f(x)<c\}$$
--   is analytic for every real number $c$.
--   2. (**Eqs. (103) and (114) of Chapter 7**) Let $Y$ be a second Borel space, $D\subseteq X\times Y$, and $f:D\to R^*$. For $x\in X$ write $D_x=\{y\in Y\mid (x,y)\in D\}$ and $\mathrm{proj}_X(D)=\{x\mid D_x\neq\emptyset\}$. The **partial infimum** $f^*:\mathrm{proj}_X(D)\to R^*$ is
--   $$f^*(x)=\inf_{y\in D_x}f(x,y).$$
--   3. (**Proposition 7.50(b)**) The **attainment set** is
--   $$I=\{x\in\mathrm{proj}_X(D)\mid f(x,y_x)=f^*(x)\text{ for some }y_x\in D_x\}.$$
--
--   Lower semianalytic functions are the class of cost functions closed under partial minimization, which is why they are the value functions of the Borel-space dynamic programming models of Chapters 8–9.
--
--   **Formalization Note** $R^*$ is Mathlib's `EReal`; the infimum is the complete-lattice infimum of `EReal`, which agrees with the book's convention $\inf\emptyset=+\infty$ (never invoked here, since $D_x\neq\emptyset$ on $\mathrm{proj}_X(D)$). No sum of infinities of opposite sign occurs in these definitions. Functions on $D$ and on $\mathrm{proj}_X(D)$ are functions on subtypes.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 177, Definition 7.21; p. 180, Eq. (103) of Chapter 7; pp. 184–185, Eq. (114) of Chapter 7 and Proposition 7.50(b)

import Mathlib

namespace BertsekasShreve.AnalyticSelection

open MeasureTheory

/-- **Definition 7.21** (p. 177). Let `D ⊆ X` and `f : D → R*`. `f` is *lower semianalytic* if
`D` is analytic and `{x ∈ D | f(x) < c}` is analytic for every real `c`. -/
def IsLowerSemianalytic {X : Type*} [TopologicalSpace X] (D : Set X) (f : D → EReal) : Prop :=
  AnalyticSet D ∧ ∀ c : ℝ, AnalyticSet (Subtype.val '' {x : D | f x < (c : EReal)})

/-- Eq. (103) / (114) of Chapter 7 (pp. 180, 184). For `D ⊆ X × Y` and `f : D → R*`, the
partial infimum `f* : proj_X(D) → R*`, `f*(x) = inf_{y ∈ D_x} f(x, y)`, where
`D_x = {y | (x, y) ∈ D}`. -/
noncomputable def partialInf {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) :
    (Prod.fst '' D) → EReal :=
  fun x => ⨅ (y : Y) (h : ((x : X), y) ∈ D), f ⟨((x : X), y), h⟩

/-- The set `I` of Proposition 7.50(b) (p. 185): the points `x ∈ proj_X(D)` at which the
infimum `f*(x)` is attained, i.e. `f(x, y_x) = f*(x)` for some `y_x ∈ D_x`. -/
def attainSet {X Y : Type*} (D : Set (X × Y)) (f : D → EReal) : Set X :=
  {x | ∃ hx : x ∈ Prod.fst '' D, ∃ (y : Y) (h : (x, y) ∈ D),
    f ⟨(x, y), h⟩ = partialInf D f ⟨x, hx⟩}

end BertsekasShreve.AnalyticSelection


