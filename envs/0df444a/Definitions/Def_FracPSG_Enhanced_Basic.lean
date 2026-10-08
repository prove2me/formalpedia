-- Prove2me | Definitions.Def_FracPSG_Enhanced_Basic
-- name    : FracPSG_Enhanced_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:53.176319+00:00
-- url     : https://prove2.me/theorems/265ae7af-94ce-4840-a96c-83bf38fd88eb
-- title:
--   Indicator sums, weak convexity on a set, max-type functions, ε-active sets, and strong lifted stationary points
-- statement:
--   Let $H$ be a finite-dimensional real Hilbert space. This file fixes the notions used in the analysis of the fractional program
--   $$\min_{x\in S}\ \frac{f(x)}{g(x)}\qquad (P)$$
--   when the denominator is a maximum of finitely many smooth functions.
--
--   1. **Indicator sum.** For $h: H\to(-\infty,+\infty]$ and $S\subseteq H$, the function $h+\iota_S$ equals $h(x)$ on $S$ and $+\infty$ off $S$, where $\iota_S$ is the indicator function of $S$.
--   2. **Weak convexity on a set, real-valued case.** A function $h: H\to\mathbb R$ is *weakly convex on $C$ with modulus $\rho$* when $\rho\ge0$ and $h+\iota_C+\frac\rho2\|\cdot\|^2$ is convex; equivalently, $C$ is convex and $h+\frac\rho2\|\cdot\|^2$ is convex on $C$.
--   3. **Weak convexity on a set, extended-real case.** A function $h: H\to(-\infty,+\infty]$ is weakly convex on $S$ with modulus $\rho$ when $\rho\ge0$ and $h+\iota_S+\frac\rho2\|\cdot\|^2$ is convex, i.e. its epigraph
--   $$\{(x,t)\in H\times\mathbb R:\ x\in S,\ h(x)+\tfrac\rho2\|x\|^2\le t\}$$
--   is a convex set.
--   4. **Max-type function.** For finitely many functions $g_1,\dots,g_p: H\to\mathbb R$ ($p\ge1$), $g(x)=\max\{g_i(x): 1\le i\le p\}$.
--   5. **$\varepsilon$-active set.** For $\varepsilon\ge0$,
--   $$I_\varepsilon(x)=\{i\in\{1,\dots,p\}:\ g_i(x)\ge g(x)-\varepsilon\};$$
--   for $\varepsilon=0$ this is the active set $I_0(x)=\{i: g_i(x)=g(x)\}$.
--   6. **Strong lifted stationary point.** For $f: H\to(-\infty,+\infty]$ and $g: H\to\mathbb R$, a point $\bar x\in S$ is a (limiting) *strong lifted stationary point* of (P) when
--   $$f(\bar x)\,\partial_L g(\bar x)\subseteq g(\bar x)\,\partial_L(f+\iota_S)(\bar x),$$
--   that is, for every $v\in\partial_L g(\bar x)$ there is $u\in\partial_L(f+\iota_S)(\bar x)$ with $f(\bar x)\,v=g(\bar x)\,u$.
--
--   Strong lifted stationarity is stronger than lifted stationarity whenever $\partial_L g(\bar x)$ has more than one element; it is the stationarity notion certified by the enhanced extrapolated proximal subgradient algorithm.
--
--   **Formalization Note** The definitions are stated for any real inner-product space; the rest of the mission uses `EuclideanSpace ℝ (Fin N)`. The limiting subdifferential $\partial_L$ is the published `NonconvexSplitting.Shared.LimitingSubdiff`, which is empty where the function is $+\infty$. "Modulus" is read as "a valid constant", not the smallest one. The max is `Finset.sup'` over a nonempty finite index type, and indices run over `Fin p` (that is $0,\dots,p-1$ instead of $1,\dots,p$). In the strong lifted condition $f(\bar x)$ enters through `EReal.toReal`; the notion is meant for $f(\bar x)<+\infty$, which every theorem of the mission concludes separately.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 4 (indicator (4)), p. 5 (weak convexity), p. 7 (Definition 3.1(iii)), p. 21 (Assumption 2′, ε-active set)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracPSG_Subseq_Basic

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Enhanced

open NonconvexSplitting.Shared

open Classical in

/-- Weak convexity on a set (Boţ–Dao–Li, p. 5), for an extended-real-valued function
`h : X → (−∞, +∞]`: `h` is weakly convex on `S` with modulus `ρ` when `ρ ≥ 0` and
`h + ι_S + (ρ/2)‖·‖²` is a convex function, i.e. its epigraph
`{(x, t) : x ∈ S, h(x) + (ρ/2)‖x‖² ≤ t}` is a convex subset of `X × ℝ`. -/
def IsWeaklyConvexOnE {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : Set X) (h : X → EReal) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ Convex ℝ {q : X × ℝ | q.1 ∈ S ∧ h q.1 + ((ρ / 2 * ‖q.1‖ ^ 2 : ℝ) : EReal) ≤ (q.2 : EReal)}

/-- The pointwise maximum `g(x) = max{gᵢ(x) : i ∈ ι}` of finitely many real functions
(Assumption 2′, p. 21), over a nonempty finite index type. -/
noncomputable def maxFn {ι X : Type*} [Fintype ι] [Nonempty ι] (gi : ι → X → ℝ) (x : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => gi i x)

/-- The `ε`-active set (p. 21) of `g = max{gᵢ}` at `x`:
`I_ε(x) = {i : gᵢ(x) ≥ g(x) − ε}`. For `ε = 0` it is the active set `I₀(x) = {i : gᵢ(x) = g(x)}`. -/
noncomputable def activeSet {ι X : Type*} [Fintype ι] [Nonempty ι] (ε : ℝ) (gi : ι → X → ℝ)
    (x : X) : Finset ι :=
  Finset.univ.filter (fun i => maxFn gi x - ε ≤ gi i x)

/-- Definition 3.1(iii) (Boţ–Dao–Li, p. 7): `xbar ∈ S` is a (limiting) strong lifted stationary
point of `min_{x ∈ S} f(x)/g(x)` when `f(xbar) ∂_L g(xbar) ⊆ g(xbar) ∂_L(f + ι_S)(xbar)`, written
out as: for every `v ∈ ∂_L g(xbar)` there is `u ∈ ∂_L(f + ι_S)(xbar)` with
`f(xbar) v = g(xbar) u`. Here `f(xbar)` enters as `(f xbar).toReal`; the notion is meant for
`f(xbar) < +∞`, which is stated separately wherever it is concluded. -/
def IsStrongLiftedStationary {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (g : X → ℝ) (S : Set X) (xbar : X) : Prop :=
  xbar ∈ S ∧ ∀ v ∈ LimitingSubdiff (fun y => (g y : EReal)) xbar,
    ∃ u ∈ LimitingSubdiff (FracPSG.Subseq.addInd f S) xbar, (f xbar).toReal • v = g xbar • u

end FracPSG.Enhanced


