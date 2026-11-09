-- Prove2me | Definitions.Def_HopRamsey_IsStochRamseyEmbedding
-- name    : HopRamsey_IsStochRamseyEmbedding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:53.683012+00:00
-- url     : https://prove2.me/theorems/45215b10-9c37-4381-9fda-dd4901be5583
-- title:
--   Stochastic hop-constrained Ramsey-type embeddings into HSTs (Definition 2)
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph and $h$ a hop parameter. A **stochastic hop-constrained Ramsey-type embedding into HSTs** is a probability distribution $\mathcal D$ over pairs $(U,M)$, where $U$ is an HST whose leaves are (images of) the vertices, with tree distance $d_U$, and $M\subseteq V$ is a **saved set**. For parameters $\beta\in\mathbb N$ and $k,p,t\ge 0$:
--
--   1. $\mathcal D$ has **hop-stretch** $\beta$ if for every $(U,M)$ in the support and all $u,v\in V$: $d^{(\beta h)}_G(u,v)\le d_U(v,u)$.
--   2. $\mathcal D$ has **distortion** $k$ if for every $(U,M)$ in the support, every $u\in M$ and every $v\in V$: $d_U(v,u)\le k\cdot d^{(h)}_G(u,v)$.
--   3. $\mathcal D$ has **exclusion probability** $p$ if $\Pr_{(U,M)\sim\mathcal D}[v\notin M]\le p$ for every $v\in V$.
--   4. $\mathcal D$ has **expected distortion** $t$ if for all $u,v\in V$:
--
--   $$
--   \mathbb E_{(U,M)\sim\mathcal D}\big[d_{U,M}(u,v)\big]\le t\cdot d^{(h)}_G(u,v),\qquad d_{U,M}(u,v)=\begin{cases}d_U(u,v)& u,v\in M,\\ 0&\text{otherwise (even if } d_U(u,v)=\infty).\end{cases}
--   $$
--
--   Hop-stretch and distortion are worst-case guarantees over the whole support; exclusion and expected distortion are averages. Theorem 1 asks for all four at once.
--
--   **Formalization Note** An HST is recorded by its leaf ultrametric $\rho$ with values in $[0,\infty]$ (the published `ARTreeCover.HST`); the distribution is a `PMF` on pairs (HST, finite saved set); probabilities are outer-measure values of the PMF and the expectation is the $[0,\infty]$-valued sum of point masses, with the indicator inside the sum. Statements using this definition require every HST in the support to have leaf set $V$.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Definition 2, pp.13–14 (PDF pp.15–16); Definition 1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_HopRamsey_hopDist

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

/-- Hop-stretch `β` (Definition 2, first bullet, p.13, PDF p.15): every tree in the support
dominates the `(β·h)`-hop distance, `d^{(β·h)}_G(u, v) ≤ d_X(f(v), f(u))` for all `u, v ∈ V`.

**Formalization Note.** A distribution `D` over pairs (embedding into an HST, saved set) is a `PMF`
on `ARTreeCover.HST V × Finset V`; the HST distance `d_X(f(u), f(v))` is the HST's function `ρ`
read at `(u, v)` (the pulled-back ultrametric). -/
def HasHopStretch {V : Type} (G : WGraph V) (h : ℕ) (D : PMF (HST V × Finset V)) (β : ℕ) : Prop :=
  ∀ x ∈ D.support, ∀ u v : V, hopDist G (β * h) u v ≤ x.1.ρ v u

/-- Distortion `k` (Definition 2, second bullet, p.13): for every pair in the support, every saved
`u ∈ M` and every `v ∈ V`, `d_X(f(v), f(u)) ≤ k · d^{(h)}_G(u, v)` (products in `[0, ∞]`). -/
def HasDistortion {V : Type} (G : WGraph V) (h : ℕ) (D : PMF (HST V × Finset V)) (k : ℝ) : Prop :=
  ∀ x ∈ D.support, ∀ u ∈ x.2, ∀ v : V, x.1.ρ v u ≤ ENNReal.ofReal k * hopDist G h u v

/-- Exclusion probability `p` (Definition 2, third bullet, p.14, PDF p.16):
`Pr_{(f,M)∼D}[v ∉ M] ≤ p` for every `v ∈ V`. -/
def HasExclusion {V : Type} (D : PMF (HST V × Finset V)) (p : ℝ) : Prop :=
  ∀ v : V, D.toOuterMeasure {x | v ∉ x.2} ≤ ENNReal.ofReal p

/-- Expected distortion `t` (Definition 2, fourth bullet, p.14): for all `u, v ∈ V`,
`E[d_{X,M}(f(u), f(v))] ≤ t · d^{(h)}_G(u, v)`, where `d_{X,M}(f(u), f(v)) = d_X(f(u), f(v))` if
`u, v ∈ M` and `0` otherwise "(even if d_X(f(u),f(v)) = ∞)".

**Formalization Note.** The expectation is the `[0, ∞]`-valued sum over the PMF, with the indicator
written as an `if` inside the sum, so an infinite distance outside `M × M`, or on a null pair,
contributes `0`. -/
def HasExpectedDistortion {V : Type} [DecidableEq V] (G : WGraph V) (h : ℕ) (D : PMF (HST V × Finset V))
    (t : ℝ) : Prop :=
  ∀ u v : V, (∑' x, D x * (if u ∈ x.2 ∧ v ∈ x.2 then x.1.ρ u v else 0))
    ≤ ENNReal.ofReal t * hopDist G h u v

/-- A stochastic hop-constrained Ramsey-type embedding into HSTs with hop parameter `h`,
hop-stretch `β`, distortion `k`, exclusion probability `p` and expected distortion `t`.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), Definition 2,
pp.13–14 (PDF pp.15–16): "A stochastic hop-constrained Ramsey-type embedding with hop parameter h
from a weighted graph G = (V,E,w) to a metric family F is a distribution D over pairs (f,M), where
f is a mapping from G to a metric (X,d_X) ∈ F, and M ⊆ V is a saved set."

**Formalization Note.**
1. The target family is HSTs (Definition 1, p.12). A pair `(f, M)` is recorded as
   `(U, M)` with `U : ARTreeCover.HST V`, whose function `ρ u v` is `d_X(f(u), f(v))`. Every
   property of Definition 2 reads only these values, and the leaf ultrametrics of HSTs (labels in
   `[0, ∞]`) are exactly the ultrametrics with values in `[0, ∞]` (p.12). Statements that use this
   definition require `U.leaves = Set.univ` on the support, so that `ρ` is the ultrametric on all
   of `V`.
2. The distribution is a `PMF`; probabilities are `PMF.toOuterMeasure` values and expectations are
   sums of point masses. -/
def IsStochRamseyEmbedding {V : Type} [DecidableEq V] (G : WGraph V) (h : ℕ) (D : PMF (HST V × Finset V))
    (β : ℕ) (k p t : ℝ) : Prop :=
  HasHopStretch G h D β ∧ HasDistortion G h D k ∧ HasExclusion D p ∧
    HasExpectedDistortion G h D t

end HopRamsey


