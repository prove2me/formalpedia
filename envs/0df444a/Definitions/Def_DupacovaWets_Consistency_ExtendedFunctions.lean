-- Prove2me | Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
-- name    : DupacovaWets_Consistency_ExtendedFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:28:17.722968+00:00
-- url     : https://prove2.me/theorems/fc746453-ee77-472a-b27d-921c86b9dea1
-- title:
--   Effective domain, proper function, epigraph, argmin and epi-convergence for $h:\mathbb R^n\to[-\infty,\infty]$
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}=[-\infty,\infty]$.
--
--   1. The **effective domain** is $\operatorname{dom} h=\{x : h(x)<\infty\}$.
--   2. $h$ is **proper** if $h(x)>-\infty$ for every $x$ and $h$ is not identically $+\infty$.
--   3. The **epigraph** is $\operatorname{epi} h=\{(x,\alpha)\in\mathbb R^n\times\mathbb R : h(x)\le\alpha\}$.
--   4. The **set of minimizers** is $\operatorname{argmin} h=\{x : h(x)=\inf h\}$, where $\inf h=\inf_{y\in\mathbb R^n}h(y)\in[-\infty,\infty]$.
--   5. A sequence $g^\nu:\mathbb R^n\to\overline{\mathbb R}$ **epi-converges** to $g$ if for every $x\in\mathbb R^n$
--
--   $$
--   \liminf_{\nu\to\infty} g^\nu(x^\nu)\ge g(x)\ \text{ for all } x^\nu\to x, \qquad \limsup_{\nu\to\infty} g^\nu(x^\nu)\le g(x)\ \text{ for some } x^\nu\to x,
--   $$
--
--   which are conditions (3.7) and (3.8) of Dupačová and Wets.
--
--   These are the variational notions in which the consistency results of §3 are phrased: epi-convergence of the estimated objectives is the mechanism that carries minimizers and optimal values to the limit.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and values are in `EReal`; infima, $\liminf$ and $\limsup$ are taken in the complete lattice `EReal`, so they have no junk values. $\operatorname{argmin} h$ is taken literally: it is all of $\mathbb R^n$ when $h\equiv+\infty$. In the epi-convergence definition the Lean index $k=0,1,\dots$ stands for $\nu=k+1$.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 10 (dom), pp. 10–11 (proper), p. 11 (epi), p. 12 (argmin, in Prop. 3.2), p. 13 (3.7)–(3.8)

import Mathlib
open Filter Topology

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 10: the effective domain `dom h = {x | h(x) < ∞}`. -/
def effDom {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | h x < ⊤}

/-- Pp. 10–11: `h : ℝⁿ → [-∞, ∞]` is *proper* if `h > -∞` and `h` is not identically `+∞`. -/
def IsProperFn {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  (∀ x, ⊥ < h x) ∧ ∃ x, h x ≠ ⊤

/-- P. 11: the epigraph `epi h = {(x, α) ∈ ℝⁿ × ℝ | h(x) ≤ α}`. -/
def epigraph {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) :
    Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  {p | h p.1 ≤ (p.2 : EReal)}

/-- P. 12: `argmin h = {x | h(x) = inf h}`, the infimum taken over all of `ℝⁿ` in `[-∞, ∞]`. -/
noncomputable def argminSet {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | h x = ⨅ y, h y}

/-- P. 13, (3.7)–(3.8): the sequence `g^ν` (Lean index `k` = paper's `ν = k + 1`)
*epi-converges* to `g₀`: for every `x`, `liminf g^ν(x^ν) ≥ g₀(x)` along every sequence
`x^ν → x`, and `limsup g^ν(x^ν) ≤ g₀(x)` along some sequence `x^ν → x`. -/
def EpiConverges {n : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin n) → EReal)
    (g₀ : EuclideanSpace ℝ (Fin n) → EReal) : Prop :=
  ∀ x, (∀ u : ℕ → EuclideanSpace ℝ (Fin n), Tendsto u atTop (𝓝 x) →
      g₀ x ≤ liminf (fun k => g k (u k)) atTop) ∧
    ∃ u : ℕ → EuclideanSpace ℝ (Fin n), Tendsto u atTop (𝓝 x) ∧
      limsup (fun k => g k (u k)) atTop ≤ g₀ x

end DupacovaWets.Consistency


