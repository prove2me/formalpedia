-- Prove2me | Definitions.Def_ModelRiskOT_Duality_dualFeasible
-- name    : ModelRiskOT_Duality_dualFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:54:05.948307+00:00
-- url     : https://prove2.me/theorems/70e77802-439e-4cfa-8619-855a23842985
-- title:
--   Dual feasible sets $\Lambda_{c,f}$ (6b) and $\Lambda(K\times K)$ (29)
-- statement:
--   Let $S$ be a measurable space with its Borel σ-algebra. The **universal σ-algebra** is $\mathcal U(S)=\bigcap_{\mu\in P(S)}\mathcal B_\mu(S)$, where $\mathcal B_\mu(S)$ is the completion of the Borel σ-algebra under $\mu$. A function $\varphi:S\to[-\infty,\infty]$ is in $m\mathcal U(S;\bar{\mathbb R})$ if $\varphi^{-1}(B)\in\mathcal U(S)$ for every Borel set $B\subseteq[-\infty,\infty]$.
--
--   For a cost $c$, a function $f:S\to\mathbb R$ and a set $K\subseteq S$, the **dual feasible set** is
--
--   $$\Lambda(K\times K)=\{(\lambda,\varphi) : \lambda\ge0,\ \varphi\in m\mathcal U(S;\bar{\mathbb R}),\ \varphi(x)+\lambda c(x,y)\ge f(y)\text{ for all }x,y\in K\}.$$
--
--   For $K=S$ this is the dual feasible set $\Lambda_{c,f}$ of (6b); for a closed $K$ it is the set (29) used in Proposition 7.
--
--   **Formalization Note** Universal measurability uses the published definition `BertsekasShreve.AnalyticSelection.IsUniversallyMeasurable` ($\mu$-null-measurable for every probability measure $\mu$). In (29) the paper takes $\varphi\in m\mathcal U(K;\bar{\mathbb R})$; here $\varphi$ is a universally measurable function on all of $S$ with the constraint imposed only on $K\times K$. For closed $K$ the two are equivalent: $\mathcal U(K)$ is the trace of $\mathcal U(S)$ on $K$, and the dual objective only integrates $\varphi$ against a measure concentrated on $K$.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 4 (U(S), mU(S; R̄)), p. 6, Eqs. (4) and (6b); p. 20, Eq. (29)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability

namespace ModelRiskOT.Duality

open MeasureTheory BertsekasShreve.AnalyticSelection

/-- `φ ∈ mU(S; R̄)` (Blanchet & Murthy, arXiv:1604.01446v2, p. 4): `φ : S → [-∞, ∞]` is
measurable from `(S, U(S))` to `(R̄, B(R̄))`, i.e. the preimage of every Borel subset of `EReal`
is universally measurable (`U(S) = ⋂_{μ ∈ P(S)} B_μ(S)`, Bertsekas–Shreve Definition 7.18). -/
def IsUnivMeasurableEReal {S : Type*} [MeasurableSpace S] (φ : S → EReal) : Prop :=
  ∀ B : Set EReal, MeasurableSet B → IsUniversallyMeasurable (φ ⁻¹' B)

/-- The dual feasible set. For `K = Set.univ` this is **(6b)** of arXiv:1604.01446v2, p. 6:
`Λ_{c,f} = {(λ, φ) : λ ≥ 0, φ ∈ mU(S; R̄), φ(x) + λ c(x, y) ≥ f(y) for all x, y ∈ S}`.
For a closed `K ⊆ S` it is the set `Λ(K × K)` of **(29)** (p. 20), with the constraint imposed
only for `x, y ∈ K`; there the paper takes `φ ∈ mU(K; R̄)`, here `φ` is a universally measurable
function on all of `S` (equivalent for closed `K`, since `U(K)` is the trace of `U(S)` on `K` and
the dual objective only integrates `φ` against a `μ` concentrated on `K`). -/
def dualFeasible {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (f : S → ℝ) (K : Set S) :
    Set (ℝ × (S → EReal)) :=
  {p | 0 ≤ p.1 ∧ IsUnivMeasurableEReal p.2 ∧
    ∀ x ∈ K, ∀ y ∈ K, (f y : EReal) ≤ p.2 x + ((p.1 * c x y : ℝ) : EReal)}

end ModelRiskOT.Duality


