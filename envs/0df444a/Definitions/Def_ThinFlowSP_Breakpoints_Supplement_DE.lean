-- Prove2me | Definitions.Def_ThinFlowSP_Breakpoints_Supplement_DE
-- name    : ThinFlowSP_Breakpoints_Supplement_DE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:42:44.318796+00:00
-- url     : https://prove2.me/theorems/8a17406c-a785-40b3-83d9-6796fa07d605
-- title:
--   pp. 4, 11–12, (DE) — the graphs G′_ϑ, the extended label function ϱ^{G′}, and the differential equation (DE)
-- statement:
--   The differential equation (DE) of Kaiser, §5.
--
--   1. **The graphs $G'_\vartheta$ (p. 4).** For a vector $\ell(\vartheta)\in\mathbb R^V$, $A'_\vartheta=\{a=(v,w):\ell_w(\vartheta)\ge\ell_v(\vartheta)+\tau_a\}$, $A^*_\vartheta=\{a=(v,w):\ell_w(\vartheta)>\ell_v(\vartheta)+\tau_a\}$ and $G'_\vartheta=(V,A'_\vartheta,A^*_\vartheta)$ with the capacities $\nu$ restricted to $A'_\vartheta$.
--   2. **The label function (pp. 11–12).** For a triple $G'=(V,A',A^*)$ and $\nu'_0\ge0$: if $G'$ is a shortest path graph with resetting, $\varrho^{G'}(\nu'_0)$ are the corresponding labels, with label $1$ at $s$, of a normalized thin $s$–$t$-flow with resetting of value $\nu'_0$; otherwise, with $U=\{v:\exists\ s\text{–}v\text{-path in }A'\}$, $\varrho^{G'}_v\equiv0$ for $v\in U$ and $\varrho^{G'}_v\equiv1$ for $v\notin U$.
--   3. **(DE) (p. 12).** $\ell:\mathbb R\to\mathbb R^V$ solves (DE) if it is locally absolutely continuous and
--   $$\ell(\vartheta)=(\vartheta+\ell^0_v)_{v\in V}\ \text{for all }\vartheta\le0\qquad\text{and}\qquad \frac{d\ell}{d\vartheta}(\vartheta)=\varrho^{G'_\vartheta}\bigl(\nu_0(\vartheta)\bigr)\ \text{for a.e. }\vartheta\ge0 .$$
--   It solves (DE) on $(-\infty,\vartheta]$ if this holds with local absolute continuity on $(-\infty,\vartheta]$ and the derivative condition for almost every point of $[0,\vartheta]$.
--
--   These are the objects of Theorems 19 and 21.
--
--   **Formalization Note** `IsRhoExt H A* ν ν′₀ r` states that $r=\varrho^{G'}(\nu'_0)$ as a property: in the shortest-path-graph case it asks for some normalized thin flow with resetting with labels $r$ and $r_s=1$ (the base definitions `IsStaticFlow`, `IsThinFlowLabels`); by Theorem 13 and Corollary 15 there is exactly one such $r$ for $\nu'_0\ge0$. `DEDeriv` asks that $\ell$ have a derivative at $\vartheta$ with this property for $G'_\vartheta$ computed from $\ell(\vartheta)$. In `SolvesDEUpTo N ν0 ϑ ℓ`, $\ell$ is a function on $\mathbb R$ of which only the values on $(-\infty,\vartheta]$ are constrained. The labels are real vectors, not non-negative ones, because $\ell_s(\vartheta)=\vartheta$ is negative for $\vartheta<0$.
--
--   The paper defines the extension only for acyclic arc sets. `IsRhoExt` also assigns the same 0/1 vector to cyclic non-shortest-path graphs; those additional inputs never occur in (DE), because `QNet.Standing` makes every graph `Gprime N (ℓ ϑ)` acyclic.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 4 (A′_ϑ, A*_ϑ, G′_ϑ), p. 11 (definition of ϱ^{G′} in the proof of Proposition 17), p. 12 (extension of ϱ^{G′}, (DE)), p. 15 ((DE) on (−∞, ϑ], Theorem 21)

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_FluidModel

open MeasureTheory

noncomputable section

namespace ThinFlowSP.Breakpoints.Supplement

open ThinFlowSP.Breakpoints

/-- `A′_ϑ = {a = (v, w) : ℓ_w(ϑ) ≥ ℓ_v(ϑ) + τ_a}` (p. 4), computed from a label vector `L = ℓ(ϑ)`. -/
def primeArcs (N : QNet) (L : N.G.V → ℝ) : Finset N.G.A :=
  Finset.univ.filter fun a => L (N.G.tail a) + N.τ a ≤ L (N.G.head a)

/-- The graph `(V, A′_ϑ)` of `G′_ϑ`. -/
abbrev Gprime (N : QNet) (L : N.G.V → ℝ) : Net := subNet N.G (primeArcs N L)

/-- `A*_ϑ = {a = (v, w) : ℓ_w(ϑ) > ℓ_v(ϑ) + τ_a}` (p. 4), as a set of arcs of `(V, A′_ϑ)`. -/
def starArcs (N : QNet) (L : N.G.V → ℝ) : Finset (Gprime N L).A :=
  Finset.univ.filter fun b => L (N.G.tail b.1) + N.τ b.1 < L (N.G.head b.1)

/-- The capacities `ν` restricted to `A′_ϑ`. -/
def nuPrime (N : QNet) (L : N.G.V → ℝ) : (Gprime N L).A → ℝ := fun b => N.ν b.1

/-- `r = ϱ^{G′}(ν′₀)` for the triple `G′ = (V, A′, A*)` with capacities `ν` (pp. 11–12):
* if `(V, A′, A*)` is a shortest path graph with resetting (Definition 3), `r` are the
  corresponding labels, with label `1` at `s`, of a normalized thin `s`–`t`-flow with resetting
  of value `ν′₀` (by Corollary 15 there is only one such `r` for `ν′₀ ≥ 0`);
* otherwise (p. 12), with `U` the set of vertices reachable from `s` in `A′`, `r v = 0` for
  `v ∈ U` and `r v = 1` for `v ∉ U`. -/
def IsRhoExt (H : Net) (Astar : Finset H.A) (ν : H.A → ℝ) (nu0 : ℝ) (r : H.V → ℝ) : Prop :=
  (IsShortestPathGraph H →
    r H.s = 1 ∧ ∃ x : H.A → ℝ, IsStaticFlow H x nu0 ∧ IsThinFlowLabels H Astar ν x r) ∧
  (¬ IsShortestPathGraph H →
    ∀ v, (Reaches H H.s v → r v = 0) ∧ (¬ Reaches H H.s v → r v = 1))

/-- The derivative condition of (DE) at time `ϑ` (p. 12): `ℓ` is differentiable at `ϑ` and its
derivative is `ϱ^{G′_ϑ}(ν₀(ϑ))`, where `G′_ϑ = (V, A′_ϑ, A*_ϑ)` is computed from `ℓ(ϑ)`. -/
def DEDeriv (N : QNet) (ν0 : ℝ → ℝ) (ℓ : ℝ → N.G.V → ℝ) (ϑ : ℝ) : Prop :=
  ∃ d : N.G.V → ℝ, HasDerivAt ℓ d ϑ ∧
    IsRhoExt (Gprime N (ℓ ϑ)) (starArcs N (ℓ ϑ)) (nuPrime N (ℓ ϑ)) (ν0 ϑ) d

/-- `ℓ` is a locally absolutely continuous solution of the differential equation (DE) (p. 12):
every component `ℓ_v` is absolutely continuous on every bounded interval,
`ℓ(ϑ) = (ϑ + ℓ⁰_v)_{v ∈ V}` for all `ϑ ≤ 0`, and `dℓ/dϑ(ϑ) = ϱ^{G′_ϑ}(ν₀(ϑ))` for almost
every `ϑ ≥ 0`. -/
def SolvesDE (N : QNet) (ν0 : ℝ → ℝ) (ℓ : ℝ → N.G.V → ℝ) : Prop :=
  (∀ v, ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun θ => ℓ θ v) a b) ∧
  (∀ θ ≤ 0, ∀ v, ℓ θ v = θ + dist0 N v) ∧
  ∀ᵐ θ, 0 ≤ θ → DEDeriv N ν0 ℓ θ

/-- `ℓ` fulfils (DE) on `(-∞, ϑ]` (Theorem 21, p. 15): only the values of `ℓ` on `(-∞, ϑ]` are
constrained; every component is absolutely continuous on every bounded interval inside
`(-∞, ϑ]`, the initial condition holds on `(-∞, 0]`, and the derivative condition holds for
almost every `θ ∈ [0, ϑ]`. -/
def SolvesDEUpTo (N : QNet) (ν0 : ℝ → ℝ) (ϑ : ℝ) (ℓ : ℝ → N.G.V → ℝ) : Prop :=
  (∀ v, ∀ a b : ℝ, a ≤ ϑ → b ≤ ϑ → AbsolutelyContinuousOnInterval (fun θ => ℓ θ v) a b) ∧
  (∀ θ ≤ 0, ∀ v, ℓ θ v = θ + dist0 N v) ∧
  ∀ᵐ θ, 0 ≤ θ → θ < ϑ → DEDeriv N ν0 ℓ θ

end ThinFlowSP.Breakpoints.Supplement


