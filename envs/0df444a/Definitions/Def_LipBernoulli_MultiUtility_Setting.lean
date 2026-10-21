-- Prove2me | Definitions.Def_LipBernoulli_MultiUtility_Setting
-- name    : LipBernoulli_MultiUtility_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:43.832506+00:00
-- url     : https://prove2.me/theorems/28c0bfcf-f100-43c8-9f2a-423ff766b912
-- title:
--   (2), (3), (9)–(11), Definition 4.1, (17), pp. 4–16 — Δ1(X), W1, mixtures, affine preorders, the Lipschitz property, Lipschitz multi-utility representation
-- statement:
--   Let $X = (X, d)$ be a metric space carrying its Borel $\sigma$-algebra. A **lottery** is a Borel probability measure on $X$. This file fixes the objects of Ok and Weaver's expected-utility theory with Lipschitz Bernoulli utilities.
--
--   1. **Finite-mean lotteries** ((2), p. 4).
--   $$
--   \Delta_1(X) := \Big\{ p \text{ a Borel probability measure on } X : \int_{X\times X} d\,\mathrm d(p\times p) < \infty \Big\}.
--   $$
--   2. **Wasserstein 1-metric** ((3), p. 5). For lotteries $p, q$,
--   $$
--   W_1(p,q) := \inf_{\mu} \int_{X\times X} d\,\mathrm d\mu,
--   $$
--   the infimum over all **couplings** $\mu$ of $p$ and $q$, i.e. Borel probability measures on $X\times X$ with first marginal $p$ and second marginal $q$. The value lies in $[0,\infty]$.
--   3. **Mixtures** ((11), p. 9). For $\lambda \in [0,1]$, $p \oplus_\lambda q := (1-\lambda)p + \lambda q$.
--   4. **Preorders on a set** (p. 8). A relation $\succsim$ is a preorder on a set $S$ of measures if it is reflexive and transitive on $S$; a set $S$ is convex if it is closed under $\oplus_\lambda$ for $\lambda\in[0,1]$.
--   5. **Weak affinity and affinity** ((9)–(10), p. 8). $\succsim$ is weakly affine on $S$ if $p \succsim q$ implies $(1-\lambda)p+\lambda r \succsim (1-\lambda)q+\lambda r$ for all $p,q,r\in S$ and $\lambda\in[0,1)$; it is affine if moreover the converse implication holds, i.e.
--   $$
--   p \succsim q \iff (1-\lambda)p+\lambda r \succsim (1-\lambda)q+\lambda r \qquad (p,q,r\in S,\ \lambda\in[0,1)).
--   $$
--   6. **Lipschitz preorders** (Definition 4.1, p. 12). A preorder $\succsim$ on $\Delta_1(X)$ is Lipschitz if for all $p, q \in \Delta_1(X)$ such that $q \succsim p$ fails there is $K = K(p,q) > 0$ such that, for all $p', q' \in \Delta_1(X)$,
--   $$
--   q \oplus_\lambda q' \succsim p \oplus_\lambda p' \text{ fails whenever } 0 \le \lambda < \frac{K}{K + W_1(p',q')}.
--   $$
--   7. **Lipschitz multi-utility representation** ((17), p. 16). A family $\mathcal U$ of Lipschitz functions on $X$ represents $\succsim$ if for all $p, q \in \Delta_1(X)$,
--   $$
--   p \succsim q \iff \int_X u\,\mathrm dp \ge \int_X u\,\mathrm dq \text{ for every } u \in \mathcal U.
--   $$
--
--   These are the objects in which the paper's main theorem (Theorem 4.6) and its supporting results are stated.
--
--   **Formalization Note** $\Delta_1(X)$ is a set of measures, not a subtype, and a preorder is any relation on measures that is reflexive and transitive on the given set; its values outside the set are never constrained. $W_1$ is the published optimal-transport cost `RWPI.SqrtLasso.transportCost` with cost $d$ (an infimum over probability couplings of a lower Lebesgue integral), valued in $[0,\infty]$. On $\Delta_1(X)$ it is finite (the product coupling has finite cost), so the real number $W_1(p',q')$ in Definition 4.1 is its `toReal`, which is the paper's value. The mixing weight $\lambda$ is named `t` in Lean, since `λ` is a keyword. Integrals are Bochner integrals; they are only taken against $p \in \Delta_1(X)$, where every Lipschitz function is integrable (Proposition 2.1). Each $u \in \mathcal U$ has its own Lipschitz constant.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, (2) p. 4, (3) p. 5, (9)–(10) p. 8, (11) p. 9, Definition 4.1 p. 12, (17) p. 16

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- `Δ₁(X)` ((2), p. 4): the Borel probability measures `p` on the metric space `X` with
`∫_{X×X} d d(p × p) < ∞`. A set of measures, not a subtype. -/
def Delta1 (X : Type*) [MetricSpace X] [MeasurableSpace X] : Set (Measure X) :=
  {p | IsProbabilityMeasure p ∧ ∫⁻ z, edist z.1 z.2 ∂(p.prod p) < ∞}

/-- The Wasserstein 1-metric `W₁(p, q)` ((3), p. 5): the infimum of `∫_{X×X} d dμ` over all
couplings `μ` of `p` and `q` (probability measures on `X × X` with marginals `p` and `q`), through
the published optimal-transport cost `RWPI.SqrtLasso.transportCost` with cost `d`. Valued in
`[0, ∞]`. -/
noncomputable def W1 {X : Type*} [MetricSpace X] [MeasurableSpace X] (p q : Measure X) : ℝ≥0∞ :=
  RWPI.SqrtLasso.transportCost (fun x y => edist x y) p q

/-- The mixture `p ⊕_t q := (1 − t)p + tq` ((11), p. 9). The paper's weight `λ` is named `t`. -/
noncomputable def mix {X : Type*} [MeasurableSpace X] (t : ℝ) (p q : Measure X) : Measure X :=
  ENNReal.ofReal (1 - t) • p + ENNReal.ofReal t • q

/-- `R` is a preorder on the set `S` (p. 8): reflexive and transitive on `S`. Values of `R` outside
`S` are not constrained. -/
def IsPreorderOn {X : Type*} [MeasurableSpace X] (S : Set (Measure X))
    (R : Measure X → Measure X → Prop) : Prop :=
  (∀ p ∈ S, R p p) ∧ ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, R p q → R q r → R p r

/-- `S` is convex: closed under the mixtures `p ⊕_t q`, `t ∈ [0, 1]`. -/
def IsConvexSet {X : Type*} [MeasurableSpace X] (S : Set (Measure X)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → mix t p q ∈ S

/-- Weak affinity (9), p. 8: `p ≿ q` implies `(1 − λ)p + λr ≿ (1 − λ)q + λr` for every
`p, q, r ∈ S` and `λ ∈ [0, 1)`. -/
def IsWeaklyAffine {X : Type*} [MeasurableSpace X] (S : Set (Measure X))
    (R : Measure X → Measure X → Prop) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, ∀ t : ℝ, 0 ≤ t → t < 1 → R p q → R (mix t p r) (mix t q r)

/-- Affinity (10), p. 8: `p ≿ q` iff `(1 − λ)p + λr ≿ (1 − λ)q + λr` for every `p, q, r ∈ S` and
`λ ∈ [0, 1)`. -/
def IsAffine {X : Type*} [MeasurableSpace X] (S : Set (Measure X))
    (R : Measure X → Measure X → Prop) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, ∀ t : ℝ, 0 ≤ t → t < 1 → (R p q ↔ R (mix t p r) (mix t q r))

/-- Definition 4.1, p. 12: the preorder `≿` on `Δ₁(X)` is Lipschitz if for every `p, q ∈ Δ₁(X)`
such that `q ≿ p` fails there is `K = K(p, q) > 0` such that, for any `p', q' ∈ Δ₁(X)`,
`q ⊕_λ q' ≿ p ⊕_λ p'` fails whenever `0 ≤ λ < K / (K + W₁(p', q'))`. -/
def IsLipschitzPref {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (R : Measure X → Measure X → Prop) : Prop :=
  ∀ p ∈ Delta1 X, ∀ q ∈ Delta1 X, ¬ R q p →
    ∃ K : ℝ, 0 < K ∧ ∀ p' ∈ Delta1 X, ∀ q' ∈ Delta1 X, ∀ t : ℝ,
      0 ≤ t → t < K / (K + (W1 p' q').toReal) → ¬ R (mix t q q') (mix t p p')

/-- (17), p. 16: `U` is a family of Lipschitz functions on `X` with `p ≿ q` iff
`∫ u dp ≥ ∫ u dq` for every `u ∈ U`, for all `p, q ∈ Δ₁(X)`. -/
def RepresentedBy {X : Type*} [MetricSpace X] [MeasurableSpace X] (U : Set (X → ℝ))
    (R : Measure X → Measure X → Prop) : Prop :=
  (∀ u ∈ U, ∃ L : ℝ≥0, LipschitzWith L u) ∧
  ∀ p ∈ Delta1 X, ∀ q ∈ Delta1 X, (R p q ↔ ∀ u ∈ U, ∫ x, u x ∂q ≤ ∫ x, u x ∂p)

end LipBernoulli.MultiUtility


