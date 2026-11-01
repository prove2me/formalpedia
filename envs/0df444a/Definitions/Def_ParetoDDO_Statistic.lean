-- Prove2me | Definitions.Def_ParetoDDO_Statistic
-- name    : ParetoDDO_Statistic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:07.893972+00:00
-- url     : https://prove2.me/theorems/16a41324-806f-4a4a-8a33-85843fb897aa
-- title:
--   Statistics (Definition 2.5), compressed pairs $\tilde{\mathcal X}$ (Definition 2.6) and the restricted meta-problem (2.6b)
-- statement:
--   1. **Definition 2.5 (statistic).** A process $\widehat S_T\in\mathbb R^d$ adapted to $\{\mathcal F_T\}$ with closed state space $\mathbb S\subseteq\mathbb R^d$, together with a local homeomorphism $S_\infty:\Theta\to\mathbb S$ such that $\widehat S_T\to S_\infty(\theta)$ in $\mathbb P_\theta$-probability for every $\theta\in\Theta$. As on p.16, $\mathbb S$ is the smallest closed set with $\mathbb P_\theta[\widehat S_T\in\mathbb S]=1$ for all $\theta\in\Theta$ and $T$. We write $\mathbb S_\infty=\{S_\infty(\theta):\theta\in\Theta\}$.
--   2. **Definition 2.6 (compressed predictor and prescriptor).** $\tilde c:X\times\mathbb S\to\mathbb R$ is a compressed data-driven predictor if it is bounded and continuous in $x$ on $X\times\mathbb S$ and continuous in $(x,s)$ on $X\times\mathbb S_\infty$. $\tilde x:\mathbb S\to X$ is a compressed data-driven prescriptor if it is quasi-continuous on $\mathbb S_\infty$ and some compressed predictor $\tilde c$ induces it: $\tilde x(s)\in\arg\min_{x\in X}\tilde c(x,s)$ for all $s\in\mathbb S$. $\tilde{\mathcal X}$ is the set of pairs $(\tilde c,\tilde x)$ with $\tilde x$ induced by $\tilde c$.
--   3. A compressed pair and the statistic induce $\widehat c_T(x)=\tilde c(x,\widehat S_T)$ and $\widehat x_T=\tilde x(\widehat S_T)$.
--   4. **Restricted meta-problem (2.6b).** $(\tilde c,\tilde x)\in\tilde{\mathcal X}$ is feasible if for every $\theta\in\Theta$
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P_\theta\big[c(\tilde x(\widehat S_T),\theta)>\tilde c(\tilde x(\widehat S_T),\widehat S_T)\big]\le-r ,
--   $$
--   with objectives $\tilde c(\tilde x(S_\infty(\theta)),S_\infty(\theta))$, $\theta\in\Theta$; a feasible pair is Pareto dominant if its objective is no larger than that of every feasible pair, for every $\theta$.
--
--   These compress the observation history into a statistic of fixed dimension.
--
--   **Formalization Note** $\widehat S_T(\omega)\in\mathbb S$ is required at every sample point and $T\ge1$ (a change on a set that is null for every $\theta$). $S_\infty$ is a function on $\mathbb R^d$ whose restriction $\Theta\to\mathbb S$ is a local homeomorphism of subspaces. Quasi-continuity on $\mathbb S_\infty$ is that of the restriction of $\tilde x$ to $\mathbb S_\infty$. The disappointment probability is an outer measure, since $\tilde x$ need not be measurable.
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Definition 2.5 and the state-space convention, p.16; Definition 2.6, p.17; induced pairs, p.17; (2.6b), p.18

import Mathlib
import Definitions.Def_ParetoDDO_Setting

open MeasureTheory Filter Topology

namespace ParetoDDO

variable {Ω : Type*} [MeasurableSpace Ω] {m n d : ℕ}

/-- **Definition 2.5** (statistic; arXiv:2010.06606v4, p.16). A process `Ŝ = {Ŝ_T}` with closed
state space `S ⊆ ℝ^d` is a statistic if it is adapted to `{F_T}` and there is a local homeomorphism
`S∞ : Θ → S` such that `Ŝ_T → S∞(θ)` in `P_θ`-probability for every `θ ∈ Θ`. As on p.16, `S` is the
smallest closed set with `P_θ[Ŝ_T ∈ S] = 1` for all `θ ∈ Θ` and `T`.

**Formalization Note** `Ŝ_T(ω) ∈ S` is required at every sample point (the paper's `P_θ`-almost sure
membership; changing `Ŝ_T` on an `F_T`-set that is null for every `θ` changes no probability).
`S∞` is a function on `ℝ^d`; only its values on `Θ` matter, and the local-homeomorphism condition
is on the subspaces `Θ` and `S`. Time is `T ∈ {1, 2, …}`. -/
structure IsStatistic (ξ : ℕ → Ω → Vec m) (P : Vec d → Measure Ω) (Θ : Set (Vec d))
    (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d)) (Sinf : Vec d → Vec d) : Prop where
  /-- The state space is closed. -/
  isClosed : IsClosed S
  /-- `Ŝ_T` takes values in `S`. -/
  mem : ∀ T, 1 ≤ T → ∀ ω, Ŝ T ω ∈ S
  /-- `S` is the smallest closed set carrying every `Ŝ_T` under every `P_θ`. -/
  minimal : ∀ S' : Set (Vec d), IsClosed S' →
    (∀ θ ∈ Θ, ∀ T, 1 ≤ T → P θ {ω | Ŝ T ω ∉ S'} = 0) → S ⊆ S'
  /-- `Ŝ` is adapted to `{F_T}`. -/
  adapted : ∀ T, 1 ≤ T → Measurable[histSigma ξ T] (Ŝ T)
  /-- `S∞` maps `Θ` into `S`. -/
  mapsTo : Set.MapsTo Sinf Θ S
  /-- `S∞ : Θ → S` is a local homeomorphism. -/
  isLocalHomeomorph : IsLocalHomeomorph (mapsTo.restrict Sinf Θ S)
  /-- `Ŝ_T → S∞(θ)` in `P_θ`-probability. -/
  tendstoInMeasure : ∀ θ ∈ Θ, TendstoInMeasure (P θ) Ŝ atTop (fun _ => Sinf θ)

/-- **Definition 2.6**, first part (compressed data-driven predictor; arXiv:2010.06606v4, p.17):
`c̃ : X × S → ℝ` is bounded and continuous in `x` on `X × S`, and continuous in `(x, s)` on `X × S∞`,
where `S∞ = {S∞(θ) : θ ∈ Θ}`. -/
structure IsCompressedPredictor (X : Set (Vec n)) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (Θ : Set (Vec d)) (ct : Vec n → Vec d → ℝ) : Prop where
  /-- `c̃` is bounded on `X × S`. -/
  bounded : ∃ B : ℝ, ∀ x ∈ X, ∀ s ∈ S, |ct x s| ≤ B
  /-- `c̃` is continuous in `x` on `X × S`. -/
  continuousOn_left : ∀ s ∈ S, ContinuousOn (fun x => ct x s) X
  /-- `c̃` is jointly continuous on `X × S∞`. -/
  continuousOn : ContinuousOn (fun p : Vec n × Vec d => ct p.1 p.2) (X ×ˢ (Sinf '' Θ))

/-- `c̃` induces `x̃`: `x̃(s) ∈ argmin_{x∈X} c̃(x, s)` for all `s ∈ S` (arXiv:2010.06606v4,
Definition 2.6, p.17). -/
def CompressedInduces (X : Set (Vec n)) (S : Set (Vec d)) (ct : Vec n → Vec d → ℝ)
    (xt : Vec d → Vec n) : Prop :=
  ∀ s ∈ S, xt s ∈ X ∧ IsMinOn (fun x => ct x s) X (xt s)

/-- **Definition 2.6**, second part (compressed data-driven prescriptor; arXiv:2010.06606v4, p.17):
`x̃ : S → X` is quasi-continuous on `S∞` and induced by some compressed data-driven predictor. -/
def IsCompressedPrescriptor (X : Set (Vec n)) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (Θ : Set (Vec d)) (xt : Vec d → Vec n) : Prop :=
  QuasiContinuousOn (Sinf '' Θ) xt ∧
    ∃ ct, IsCompressedPredictor X S Sinf Θ ct ∧ CompressedInduces X S ct xt

/-- Membership in `X̃`, the set of compressed data-driven predictor-prescriptor pairs `(c̃, x̃)` with
`x̃` induced by `c̃` (arXiv:2010.06606v4, p.18). -/
def IsCompressedPair (X : Set (Vec n)) (S : Set (Vec d)) (Sinf : Vec d → Vec d)
    (Θ : Set (Vec d)) (ct : Vec n → Vec d → ℝ) (xt : Vec d → Vec n) : Prop :=
  IsCompressedPredictor X S Sinf Θ ct ∧ IsCompressedPrescriptor X S Sinf Θ xt ∧
    CompressedInduces X S ct xt

/-- The data-driven predictor `ĉ_T(x) = c̃(x, Ŝ_T)` induced by a compressed predictor and the
statistic (arXiv:2010.06606v4, p.17). -/
def inducedPredictor (ct : Vec n → Vec d → ℝ) (Ŝ : ℕ → Ω → Vec d) : ℕ → Vec n → Ω → ℝ :=
  fun T x ω => ct x (Ŝ T ω)

/-- The data-driven prescriptor `x̂_T = x̃(Ŝ_T)` induced by a compressed prescriptor and the statistic
(arXiv:2010.06606v4, p.17). -/
def inducedPrescriptor (xt : Vec d → Vec n) (Ŝ : ℕ → Ω → Vec d) : ℕ → Ω → Vec n :=
  fun T ω => xt (Ŝ T ω)

/-- Feasibility in the restricted meta-optimization problem **(2.6b)** (arXiv:2010.06606v4, p.18):
`(c̃, x̃) ∈ X̃` and, for every `θ ∈ Θ`,
`limsup_{T→∞} (1/T) log P_θ[c(x̃(Ŝ_T), θ) > c̃(x̃(Ŝ_T), Ŝ_T)] ≤ −r`.

**Formalization Note** The disappointment event need not be measurable (`x̃` is only
quasi-continuous); its probability is the outer measure. -/
def IsFeasible26b (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (Ŝ : ℕ → Ω → Vec d)
    (S : Set (Vec d)) (Sinf : Vec d → Vec d) (X : Set (Vec n)) (c : Vec n → Vec d → ℝ) (r : ℝ)
    (ct : Vec n → Vec d → ℝ) (xt : Vec d → Vec n) : Prop :=
  IsCompressedPair X S Sinf Θ ct xt ∧
    ∀ θ ∈ Θ, decayRate (P θ) (fun T => {ω | ct (xt (Ŝ T ω)) (Ŝ T ω) < c (xt (Ŝ T ω)) θ}) ≤
      -(r : EReal)

/-- `(c̃, x̃)` is a **Pareto dominant** (strong) solution of **(2.6b)** (arXiv:2010.06606v4, Notation,
p.6, and (2.6b), p.18): it is feasible and, for every feasible `(c̃', x̃')` and every `θ ∈ Θ`,
`c̃(x̃(S∞(θ)), S∞(θ)) ≤ c̃'(x̃'(S∞(θ)), S∞(θ))`. -/
def IsParetoDominant26b (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (Ŝ : ℕ → Ω → Vec d)
    (S : Set (Vec d)) (Sinf : Vec d → Vec d) (X : Set (Vec n)) (c : Vec n → Vec d → ℝ) (r : ℝ)
    (ct : Vec n → Vec d → ℝ) (xt : Vec d → Vec n) : Prop :=
  IsFeasible26b P Θ Ŝ S Sinf X c r ct xt ∧
    ∀ (ct' : Vec n → Vec d → ℝ) (xt' : Vec d → Vec n), IsFeasible26b P Θ Ŝ S Sinf X c r ct' xt' →
      ∀ θ ∈ Θ, ct (xt (Sinf θ)) (Sinf θ) ≤ ct' (xt' (Sinf θ)) (Sinf θ)

end ParetoDDO


