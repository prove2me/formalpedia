-- Prove2me | Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
-- name    : BertsekasShreve_AnalyticSelection_Measurability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:30.239728+00:00
-- url     : https://prove2.me/theorems/b6e3ea7b-9376-47bc-902c-c6a45d35feb1
-- title:
--   Universal σ-algebra $\mathscr U_X$, analytic σ-algebra $\mathscr A_X$, and analytically / universally measurable functions (Definitions 7.18–7.20)
-- statement:
--   Let $X$ be a Borel space with Borel σ-algebra $\mathscr B_X$, and let $P(X)$ be the set of probability measures on $(X,\mathscr B_X)$. For $p\in P(X)$, $\mathscr B_X(p)$ denotes the completion of $\mathscr B_X$ with respect to $p$.
--
--   1. (**Definition 7.18**) The **universal σ-algebra** is
--   $$\mathscr U_X=\bigcap_{p\in P(X)}\mathscr B_X(p).$$
--   A set $E\in\mathscr U_X$ is called **universally measurable**.
--   2. (**Definition 7.19**) The **analytic σ-algebra** $\mathscr A_X$ is the smallest σ-algebra containing the analytic subsets of $X$. A set $E\in\mathscr A_X$ is called **analytically measurable**.
--   3. (**Definition 7.20**) Let $Y$ be a Borel space and $f$ a function from a set $D\subseteq X$ into $Y$. If $D\in\mathscr A_X$ and $f^{-1}(B)\in\mathscr A_X$ for every $B\in\mathscr B_Y$, then $f$ is **analytically measurable**. If $D\in\mathscr U_X$ and $f^{-1}(B)\in\mathscr U_X$ for every $B\in\mathscr B_Y$, then $f$ is **universally measurable**.
--
--   Here a set $A\subseteq X$ is **analytic** if it is empty or the image of the Baire space $\mathscr N=\mathbb N^{\mathbb N}$ under a continuous map; by Proposition 7.41 of the book this agrees with the book's Definition 7.16 ($A$ is obtained from closed sets by the Suslin operation). For every Borel space $\mathscr B_X\subseteq\mathscr A_X\subseteq\mathscr U_X$; these are the three σ-algebras with respect to which policies are measurable in the stochastic optimal control models of the book.
--
--   **Formalization Note** "Analytic" is Mathlib's `MeasureTheory.AnalyticSet`, whose definition is the book's characterization (c) of Proposition 7.41. Membership in $\mathscr B_X(p)$ is Mathlib's `NullMeasurableSet E p` (the set differs from a Borel set by a subset of a $p$-null Borel set). A function on $D\subseteq X$ is a function on the subtype `D`, so no value outside $D$ is ever used, and $f^{-1}(B)$ is read as a subset of $X$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 167, Definition 7.18; p. 171, Definitions 7.19 and 7.20; p. 166, Proposition 7.41(c)

import Mathlib

namespace BertsekasShreve.AnalyticSelection

open MeasureTheory

/-- **Definition 7.18** (p. 167). A set `E ⊆ X` is *universally measurable* if it belongs to the
completion `𝓑_X(p)` of the Borel σ-algebra with respect to every probability measure `p` on `X`,
i.e. it is `p`-null-measurable for every probability measure `p`. -/
def IsUniversallyMeasurable {X : Type*} [MeasurableSpace X] (E : Set X) : Prop :=
  ∀ p : Measure X, IsProbabilityMeasure p → NullMeasurableSet E p

set_option warn.classDefReducibility false in
/-- **Definition 7.19** (p. 171). The *analytic σ-algebra* `𝒜_X`: the smallest σ-algebra
containing the analytic subsets of `X` (analytic sets in the sense of Mathlib's `AnalyticSet`:
empty or a continuous image of the Baire space `ℕ → ℕ`, the book's Proposition 7.41(c)). -/
def analyticSigmaAlgebra (X : Type*) [TopologicalSpace X] : MeasurableSpace X :=
  MeasurableSpace.generateFrom {A : Set X | AnalyticSet A}

/-- **Definition 7.19** (p. 171). `E` is *analytically measurable* if `E ∈ 𝒜_X`. -/
def IsAnalyticallyMeasurable {X : Type*} [TopologicalSpace X] (E : Set X) : Prop :=
  MeasurableSet[analyticSigmaAlgebra X] E

/-- **Definition 7.20** (p. 171). A function `f : D → Y` defined on a subset `D ⊆ X` is
*analytically measurable* if `D ∈ 𝒜_X` and `f⁻¹(B) ∈ 𝒜_X` for every Borel set `B ⊆ Y`. -/
def IsAnalyticallyMeasurableFun {X Y : Type*} [TopologicalSpace X] [MeasurableSpace Y]
    (D : Set X) (f : D → Y) : Prop :=
  IsAnalyticallyMeasurable D ∧
    ∀ B : Set Y, MeasurableSet B → IsAnalyticallyMeasurable (Subtype.val '' (f ⁻¹' B))

/-- **Definition 7.20** (p. 171). A function `f : D → Y` defined on a subset `D ⊆ X` is
*universally measurable* if `D ∈ 𝒰_X` and `f⁻¹(B) ∈ 𝒰_X` for every Borel set `B ⊆ Y`. -/
def IsUniversallyMeasurableFun {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Set X) (f : D → Y) : Prop :=
  IsUniversallyMeasurable D ∧
    ∀ B : Set Y, MeasurableSet B → IsUniversallyMeasurable (Subtype.val '' (f ⁻¹' B))

end BertsekasShreve.AnalyticSelection


