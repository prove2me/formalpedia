-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
-- name    : OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:50:06.314221+00:00
-- url     : https://prove2.me/theorems/11fb99c3-7e73-4f3b-8c7a-a3fa3ef43ae5
-- title:
--   Discrete convexity, greatest convex minorants and normalized tail terms of sequences
-- statement:
--   This file introduces discrete convexity for real sequences indexed by $\mathbb{N}=\{0,1,2,\dots\}$, the greatest convex minorant of a sequence relative to a set of constraint indices, and an exponential tail term attached to a sequence.
--
--   1. **Discrete convexity.** A sequence $F:\mathbb{N}\to\mathbb{R}$ is *discretely convex* if its forward differences $\Delta F(n)=F(n+1)-F(n)$ form a non-decreasing sequence, $\Delta F(m)\le\Delta F(n)$ whenever $m\le n$. Equivalently, all second differences are nonnegative:
--   $$F(n+2)-2F(n+1)+F(n)\ge 0\qquad(n\in\mathbb{N}).$$
--   2. **Convex minorants.** For a set $I\subseteq\mathbb{N}$ and a sequence $f:\mathbb{N}\to\mathbb{R}$, the convex minorants of $f$ on $I$ are
--   $$\mathcal{M}(I,f)=\bigl\{F:\mathbb{N}\to\mathbb{R}\ :\ F(0)=0,\ F\text{ discretely convex},\ F(n)\le f(n)\text{ for all }n\in I\bigr\}.$$
--   Only the values of $f$ on $I$ constrain the minorants.
--   3. **Convex envelope.** The convex envelope of $f$ on $I$ is the pointwise supremum of these minorants,
--   $$\widehat f_I(n)=\sup\bigl\{F(n)\ :\ F\in\mathcal{M}(I,f)\bigr\}\qquad(n\in\mathbb{N}).$$
--   4. **Normalized tail term.** For $F:\mathbb{N}\to\mathbb{R}$ and $q,k\in\mathbb{N}$,
--   $$\tau_F(q,k)=\exp\bigl(F(k+1)+F(q)-F(q+k+1)\bigr).$$
--
--   When $I$ is unbounded and $\mathcal{M}(I,f)$ is nonempty, the envelope is the greatest element of $\mathcal{M}(I,f)$: it vanishes at $0$, lies below $f$ on $I$, is itself discretely convex, and at every corner it touches $f$, namely $\widehat f_I(n+2)-2\widehat f_I(n+1)+\widehat f_I(n)>0$ implies $n+1\in I$ and $\widehat f_I(n+1)=f(n+1)$. The tail term compares the growth of $F$ on $[q,q+k+1]$ with its growth on $[0,k+1]$; for a discretely convex $F$ whose slopes $\Delta F(n)$ tend to $+\infty$, $\tau_F(q,k)\to0$ as $q\to\infty$ for each fixed $k$. These are the one-dimensional convexity tools used to control two-sided sequences with vanishing correlations, in the construction of a nonzero operator $T$ on a separable infinite-dimensional Hilbert space with $\|T^n\|^{1/n}\to0$ whose commutant is transitive.
--
--   **Formalization Note** `DiscreteConvex F` is `Monotone (fun n => F (n + 1) - F n)`; the minorant set is `convexMinorants I f`, the envelope is `convexEnvelope I f n`, and the tail term is `normalizedTailTerm F q k`. The envelope is defined with `sSup` on the real numbers, which returns $0$ for an empty or unbounded-above set, so it has its intended meaning only under the unboundedness and nonemptiness hypotheses carried by the theorems about it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

def DiscreteConvex (F : ℕ → ℝ) : Prop :=
  Monotone (fun n => F (n + 1) - F n)

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

def convexMinorants (I : Set ℕ) (f : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {F | F 0 = 0 ∧ DiscreteConvex F ∧ ∀ n ∈ I, F n ≤ f n}

def convexEnvelope (I : Set ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup ((fun F : ℕ → ℝ => F n) '' convexMinorants I f)

namespace ConvexEnvelope

variable {I : Set ℕ} {f : ℕ → ℝ}
variable (hunbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ I)
variable (hne : (convexMinorants I f).Nonempty)

end ConvexEnvelope

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

def normalizedTailTerm (F : ℕ → ℝ) (q k : ℕ) : ℝ :=
  Real.exp (F (k+1) + F q - F (q+k+1))

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

end
end BackwardIntertwiners

end OAI


