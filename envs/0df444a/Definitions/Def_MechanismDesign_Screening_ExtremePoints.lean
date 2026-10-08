-- Prove2me | Definitions.Def_MechanismDesign_Screening_ExtremePoints
-- name    : MechanismDesign_Screening_ExtremePoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T22:19:29.520547+00:00
-- url     : https://prove2.me/theorems/19ff7b37-0745-4206-b2fe-be5285780b39
-- title:
--   Extreme points (Definition 2.4) and the set $M$ of increasing $[0,1]$-valued functions in $L^1$
-- statement:
--   **Extreme points (Definition 2.4).** If $C$ is a convex subset of a real vector space $X$, a point $x\in C$ is an **extreme point** of $C$ if for every $y\in X$ with $y\neq 0$, at least one of $x+y$ and $x-y$ lies outside $C$.
--
--   **The set $M$.** Let $\mu$ be Lebesgue measure on the type interval $[\underline\theta,\bar\theta]$ and let $\mathcal F$ be the space of integrable functions on $[\underline\theta,\bar\theta]$ with the $L^1$ norm
--   $$\|g\| = \int_{\underline\theta}^{\bar\theta} |g|\,d\mu .$$
--   The set $M\subset\mathcal F$ consists of the (weakly) increasing functions $q$ with $q(x)\in[0,1]$ for all $x\in[\underline\theta,\bar\theta]$. It is the seller's choice set for allocation rules once incentive compatibility and individual rationality are imposed.
--
--   **Formalization Note** The book gives the space of bounded functions the $L^1$ "norm", which vanishes on every function that is zero almost everywhere. To obtain a genuine normed space, $\mathcal F$ is the Lebesgue space $L^1([\underline\theta,\bar\theta])$ of almost-everywhere classes, and $M$ is the set of classes having a representative that is increasing on $[\underline\theta,\bar\theta]$ with values in $[0,1]$. This is the reading the book adopts itself in notes 4–6 to Lemma 2.7 (conditions hold on sets of positive measure or almost everywhere). Every class in $M$ is bounded, so replacing bounded functions by all integrable functions as the ambient space changes neither $M$, its topology, nor its extreme points.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.15–16, eqs. (2.16)–(2.17), set M, Definition 2.4; p.235, notes 4–6 to Chapter 2

import Mathlib

/-!
# Extreme points and the set `M` of increasing allocation rules (Börgers, Ch. 2, pp.15–16)

* Definition 2.4 (p.16): extreme points of a convex subset of a vector space.
* The space `F` of bounded functions `[θ̲, θ̄] → ℝ` with the `L¹` norm `∫ |f| dμ` (pp.15–16),
  and the subset `M` of increasing functions with values in `[0, 1]`.

The `L¹` "norm" vanishes on every function that is zero almost everywhere, so it is a norm only
on almost-everywhere equivalence classes. `F` is therefore modelled as the Lebesgue space
`L¹([θ̲, θ̄])` (`MeasureTheory.Lp ℝ 1` for Lebesgue measure restricted to `[θ̲, θ̄]`), a genuine
normed space, and `M` as the set of classes having an increasing representative with values in
`[0, 1]`. This is the reading the book itself adopts in notes 4–6 (p.235) to Lemma 2.7.
-/

namespace MechanismDesign.Screening

open MeasureTheory

/-- **Extreme point** (Definition 2.4, p.16): if `C` is a (convex) subset of a vector space `X`,
then `x ∈ C` is an extreme point of `C` if for every `y ∈ X` with `y ≠ 0`, either `x + y ∉ C` or
`x − y ∉ C` (or both). -/
def IsExtremePoint {X : Type*} [AddCommGroup X] (C : Set X) (x : X) : Prop :=
  x ∈ C ∧ ∀ y : X, y ≠ 0 → x + y ∉ C ∨ x - y ∉ C

/-- Lebesgue measure `μ` restricted to the type interval `[θ̲, θ̄]`. -/
noncomputable abbrev typeMeasure (θlo θhi : ℝ) : Measure ℝ :=
  volume.restrict (Set.Icc θlo θhi)

/-- The space `F` of p.15–16, as the normed space `L¹([θ̲, θ̄], μ)`: the norm of `f` is
`∫_{θ̲}^{θ̄} |f| dμ`. -/
abbrev L1Space (θlo θhi : ℝ) : Type :=
  Lp ℝ 1 (typeMeasure θlo θhi)

/-- The set `M ⊂ F` (p.16) of increasing functions with values in `[0, 1]`: the classes in
`L¹([θ̲, θ̄])` that have a representative `q` which is (weakly) increasing on `[θ̲, θ̄]` and
satisfies `q(x) ∈ [0, 1]` for all `x ∈ [θ̲, θ̄]`. -/
def monotoneAllocations (θlo θhi : ℝ) : Set (L1Space θlo θhi) :=
  {g | ∃ q : ℝ → ℝ, MonotoneOn q (Set.Icc θlo θhi) ∧
    (∀ x ∈ Set.Icc θlo θhi, q x ∈ Set.Icc (0 : ℝ) 1) ∧
    (g : ℝ → ℝ) =ᵐ[typeMeasure θlo θhi] q}

end MechanismDesign.Screening


