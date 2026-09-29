-- Prove2me | Definitions.Def_BrinSquier
-- name    : BrinSquier
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-12T21:59:00.125334+00:00
-- url     : https://prove2.me/theorems/9a0532db-58ed-448b-a78e-7dede35421dc
-- title:
--   Supports, piecewise-linear homeomorphisms of the line, and slopes at the ends
-- statement:
--   The objects the mission is about.
--
--   $\operatorname{supp} f = \{\,t : f(t)\neq t\,\}$ is the **support** of an orientation-preserving homeomorphism $f$ of $\mathbb{R}$ — the set of points it moves. It is always open, and it is $f$-invariant.
--
--   $f$ is **piecewise linear with finitely many breakpoints** when there is a finite set $B$ such that $f$ is affine on a neighbourhood of every point *outside* $B$. Nothing is required at the points of $B$, which is what allows a genuine corner: the two affine pieces meeting at a breakpoint need not agree in slope. $B$ is only an upper bound for the corners — it need not be minimal, and $B=\varnothing$ is allowed, in which case local affineness on the connected line forces $f$ to be globally affine.
--
--   $f$ **has slope $a$ near $-\infty$** when it coincides with a single affine map $y\mapsto ay+b$ on some ray $(-\infty,M)$, and similarly near $+\infty$. Both the slope and the intercept are determined by $f$, since two affine maps agreeing on a ray agree everywhere; only the slope is named in the predicate, the intercept being existentially quantified.
--
--   **Why `IsPLFSlopeOne`, and not compact support.** The definition's docstring warns that slope $1$ at an end is a translation, not the identity. It is nonetheless the right object: Brin and Squier show the commutator subgroup $\mathrm{PLF}'(\mathbb{R})$ consists precisely of the elements with slope $1$ at both ends, the abelianization being (slope at $-\infty$, slope at $+\infty$). The compactness used later in the proof comes from a *commutator*, never from a single element.
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, pp. 486-488: the support of a homeomorphism (Section 1) and the definitions of PL(R) and PLF(R) (Section 2).

import Mathlib

namespace BrinSquier

/-- The **support** of an orientation-preserving homeomorphism of the line: the set of points it
moves.  It is an open subset of `ℝ`. -/
def supp (f : ℝ ≃o ℝ) : Set ℝ := {t | f t ≠ t}

/-- `f` is **piecewise linear with finitely many breaks**.

Following Brin–Squier: there is a finite set `B` of *breakpoints* such that `f` is affine on a
neighbourhood of every point outside `B`.  This is equivalent to `f`
being affine on each connected component of `ℝ \ B`, which is how the source phrases it (`f` is
differentiable off `B` with locally constant derivative).

The group of orientation-preserving such maps is Brin–Squier's `PLF(ℝ)`. -/
def IsPLF (f : ℝ ≃o ℝ) : Prop :=
  ∃ B : Finset ℝ, ∀ x ∉ (B : Set ℝ), ∃ ε > 0, ∃ a b : ℝ,
    ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b

/-- `f` has slope `a` near `-∞`: it agrees with a single affine map on some ray `(-∞, M)`. -/
def SlopeAtBot (f : ℝ ≃o ℝ) (a : ℝ) : Prop := ∃ b M : ℝ, ∀ y < M, f y = a * y + b

/-- `f` has slope `a` near `+∞`: it agrees with a single affine map on some ray `(M, ∞)`. -/
def SlopeAtTop (f : ℝ ≃o ℝ) (a : ℝ) : Prop := ∃ b M : ℝ, ∀ y > M, f y = a * y + b

/-- Piecewise linear with finitely many breakpoints, and slope `1` at both ends.

Beware: slope `1` at an end means `f` is a *translation* there, **not** that it is the identity
there — the translation constant is unconstrained, and the constants at the two ends are
independent.  So this is **not** a compact-support condition: every translation satisfies it.

Brin–Squier show this set is exactly the commutator subgroup `PLF'(ℝ)`, the abelianization of
`PLF(ℝ)` being (slope at `-∞`, slope at `+∞`). -/
def IsPLFSlopeOne (f : ℝ ≃o ℝ) : Prop := IsPLF f ∧ SlopeAtBot f 1 ∧ SlopeAtTop f 1

end BrinSquier


