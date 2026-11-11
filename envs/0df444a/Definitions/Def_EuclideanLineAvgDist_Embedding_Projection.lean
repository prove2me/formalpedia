-- Prove2me | Definitions.Def_EuclideanLineAvgDist_Embedding_Projection
-- name    : EuclideanLineAvgDist_Embedding_Projection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:12.958447+00:00
-- url     : https://prove2.me/theorems/82db4261-e837-4926-8cee-fb5c5421e063
-- title:
--   Extreme sets of a random projection and their expected matching weight
-- statement:
--   The random-projection matching of Corollary 2.2.
--
--   Let $X\subset\mathbb R^k$ be a set of $n$ points, and fix an injective labelling $\tau:X\to\mathbb N$ used only to break ties. For $g\in\mathbb R^k$ order $X$ by $x\mapsto\langle x,g\rangle$, ties broken by $\tau$: $x$ precedes $y$ if $\langle x,g\rangle<\langle y,g\rangle$, or $\langle x,g\rangle=\langle y,g\rangle$ and $\tau(x)<\tau(y)$. The rank of $x$ is the number of points preceding it, a number in $\{0,\dots,n-1\}$. Let $m=\lceil n/64\rceil$.
--
--   1. $X_g^-$ is the set of the $m$ smallest points (rank $<m$), and $X_g^+$ the set of the $m$ largest points (rank $\ge n-m$).
--   2. $|A_g|$ is the minimum total Euclidean weight $\sum\|x-y\|_2$ of a perfect matching between $X_g^-$ and $X_g^+$.
--   3. The expected matching weight is
--   $$\mathbb E_{\gamma\sim N(0,I_k)}|A_\gamma|=\int |A_g|\,dN(0,I_k)(g)\in[0,\infty].$$
--
--   For distinct projections (all $g$ outside finitely many hyperplanes, a Gaussian-null set when $k\ge 1$) the sets do not depend on $\tau$ and are exactly the source's $X_g^\pm$.
--
--   **Formalization Note** The sets are defined for every $g$, including $g=0$ and directions with ties, through the labelling $\tau$. The expectation is a lower Lebesgue integral of a nonnegative function with values in $[0,\infty]$, so it needs no integrability side condition.
-- source:
--   Jack Spalding-Jamieson, STOC 2027 submission #1643 (October 2026), p. 5, Corollary 2.2 (X_g^-, X_g^+, A_g, |A_g|), p. 12, proof of Corollary 2.2 (measure-zero coincidences)

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Embedding

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k : ℕ}

/-- The order on the points of `X ⊂ ℝᵏ` given by `x ↦ ⟨x, g⟩`, with ties broken by a fixed injective
labelling `tie : X → ℕ`: `x` precedes `y` iff `⟨x,g⟩ < ⟨y,g⟩`, or `⟨x,g⟩ = ⟨y,g⟩` and
`tie x < tie y`. For injective `tie` this is a strict total order on `X`. -/
def Precedes (X : Finset (Eucl k)) (tie : X → ℕ) (g : Eucl k) (x y : X) : Prop :=
  inner ℝ (x : Eucl k) g < inner ℝ (y : Eucl k) g ∨
    (inner ℝ (x : Eucl k) g = inner ℝ (y : Eucl k) g ∧ tie x < tie y)

/-- The position (`0, …, n-1`) of `x` in that order: the number of points preceding it. -/
def projRank (X : Finset (Eucl k)) (tie : X → ℕ) (g : Eucl k) (x : X) : ℕ :=
  (Finset.univ.filter (fun y : X => Precedes X tie g y x)).card

/-- `m = ⌈n/64⌉`. -/
def extremeCount (n : ℕ) : ℕ := ⌈(n : ℝ) / 64⌉₊

/-- `X_g⁻`: the `⌈n/64⌉` smallest points of `X` in the order given by `x ↦ ⟨x, g⟩`. -/
def lowSet (X : Finset (Eucl k)) (tie : X → ℕ) (g : Eucl k) : Finset X :=
  Finset.univ.filter (fun x => projRank X tie g x < extremeCount X.card)

/-- `X_g⁺`: the `⌈n/64⌉` largest points of `X` in the order given by `x ↦ ⟨x, g⟩`. -/
def highSet (X : Finset (Eucl k)) (tie : X → ℕ) (g : Eucl k) : Finset X :=
  Finset.univ.filter (fun x => X.card - extremeCount X.card ≤ projRank X tie g x)

/-- `E_{γ ∼ N(0,I_k)} |A_γ|`, where `|A_g|` is the minimum total Euclidean weight of a perfect
matching between `X_g⁻` and `X_g⁺`; an extended nonnegative (lower Lebesgue) integral. -/
def expectedExtremeMatching (X : Finset (Eucl k)) (tie : X → ℕ) : ℝ≥0∞ :=
  ∫⁻ g, ENNReal.ofReal (minMatchingCost (lowSet X tie g) (highSet X tie g)) ∂(stdGaussian (Eucl k))

end

end EuclideanLineAvgDist.Embedding


