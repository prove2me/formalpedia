-- Prove2me | Definitions.Def_FracPSG_Subseq_Basic
-- name    : FracPSG_Subseq_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:38.61933+00:00
-- url     : https://prove2.me/theorems/c4009acb-1b34-47f6-bb6d-9e95cee8e357
-- title:
--   Indicator sums, regularity, weak convexity on a set, and lifted stationary points (pp. 4–5, Definition 3.1(ii))
-- statement:
--   Let $H$ be a finite-dimensional real Hilbert space. This file fixes four notions used throughout the analysis of the fractional program
--   $$\min_{x\in S}\ \frac{f(x)}{g(x)}.\qquad (P)$$
--
--   1. **Indicator sum.** For $h: H\to(-\infty,+\infty]$ and $S\subseteq H$, the function $h+\iota_S$ equals $h(x)$ on $S$ and $+\infty$ off $S$, where $\iota_S$ is the indicator function of $S$.
--   2. **Regularity.** A function $h$ that is finite at $x$ is *regular at $x$* when its Fréchet subdifferential $\widehat\partial h(x)$ and its limiting subdifferential $\partial_L h(x)$ coincide.
--   3. **Weak convexity on a set.** A real function $h$ is *weakly convex on $C$ with modulus $\rho$* when $\rho\ge0$ and $h+\iota_C+\frac\rho2\|\cdot\|^2$ is convex; for real-valued $h$ this says that $C$ is convex and $h+\frac\rho2\|\cdot\|^2$ is convex on $C$.
--   4. **Lifted stationary point.** For $f: H\to(-\infty,+\infty]$ and $g: H\to\mathbb R$, a point $\bar x\in S$ is a (limiting) *lifted stationary point* of (P) when
--   $$0\in g(\bar x)\,\partial_L(f+\iota_S)(\bar x)-f(\bar x)\,\partial_L g(\bar x),$$
--   that is, there are $u\in\partial_L(f+\iota_S)(\bar x)$ and $v\in\partial_L g(\bar x)$ with $g(\bar x)\,u-f(\bar x)\,v=0$.
--
--   The lifted stationarity condition is the first-order condition that the extrapolated proximal subgradient algorithm certifies at its cluster points; regularity and weak convexity are the two forms of the standing hypothesis on the denominator $g$.
--
--   **Formalization Note** $H$ is `EuclideanSpace ℝ (Fin N)` in the rest of the mission; these definitions are stated for any real inner-product space. $\widehat\partial$ and $\partial_L$ are the published `NonconvexSplitting.Shared.IsRegularSubgrad` and `LimitingSubdiff`, which are empty where the function is $+\infty$. "Modulus" is read as "a valid constant", not the smallest one, since every result only uses that $h+\frac\rho2\|\cdot\|^2$ is convex. In the lifted-stationarity condition $f(\bar x)$ enters through `EReal.toReal`; this is faithful because $u\in\partial_L(f+\iota_S)(\bar x)$ forces $f(\bar x)<+\infty$, and $f$ never takes $-\infty$ in the mission.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 4 (indicator (4), regularity), p. 5 (weak convexity), p. 7, Definition 3.1(ii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Subseq

open NonconvexSplitting.Shared

open Classical in
/-- The sum `h + ι_S` of an extended-real-valued function and the indicator function (4) of a set
`S` (Boţ–Dao–Li, p. 4): it equals `h x` on `S` and `+∞` off `S`. -/
noncomputable def addInd {X : Type*} (h : X → EReal) (S : Set X) : X → EReal :=
  fun x => if x ∈ S then h x else ⊤

/-- Regularity (Boţ–Dao–Li, p. 4): a function `h` finite at `x` is regular at `x` when its
Fréchet subdifferential and its limiting subdifferential at `x` coincide. -/
def IsRegularAt {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (h : X → EReal) (x : X) : Prop :=
  h x ≠ ⊤ ∧ h x ≠ ⊥ ∧ {v | IsRegularSubgrad h x v} = LimitingSubdiff h x

/-- Weak convexity on a set (Boţ–Dao–Li, p. 5), for a real-valued function: `h` is weakly convex
on `C` with modulus `ρ` when `ρ ≥ 0` and `h + ι_C + (ρ/2)‖·‖²` is convex, i.e. `C` is convex and
`h + (ρ/2)‖·‖²` is convex on `C`. "Modulus" is read as "a valid constant", not the smallest one. -/
def IsWeaklyConvexOn {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (C : Set X) (h : X → ℝ) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ ConvexOn ℝ C (fun x => h x + ρ / 2 * ‖x‖ ^ 2)

/-- Definition 3.1(ii) (Boţ–Dao–Li, p. 7): `xbar ∈ S` is a (limiting) lifted stationary point of
`min_{x ∈ S} f(x)/g(x)` when `0 ∈ g(xbar) ∂_L(f + ι_S)(xbar) − f(xbar) ∂_L g(xbar)`, written out
as: there are `u ∈ ∂_L(f + ι_S)(xbar)` and `v ∈ ∂_L g(xbar)` with `g(xbar) u − f(xbar) v = 0`.
Membership `u ∈ ∂_L(f + ι_S)(xbar)` forces `f xbar < +∞`, so `(f xbar).toReal` is `f(xbar)`. -/
def IsLiftedStationary {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (g : X → ℝ) (S : Set X) (xbar : X) : Prop :=
  xbar ∈ S ∧ ∃ u ∈ LimitingSubdiff (addInd f S) xbar,
    ∃ v ∈ LimitingSubdiff (fun y => (g y : EReal)) xbar,
      g xbar • u - (f xbar).toReal • v = 0

end FracPSG.Subseq


