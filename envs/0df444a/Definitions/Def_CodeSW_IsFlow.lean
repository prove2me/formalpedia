-- Prove2me | Definitions.Def_CodeSW_IsFlow
-- name    : CodeSW_IsFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:33.711212+00:00
-- url     : https://prove2.me/theorems/2380c4c1-b8c5-4387-8010-bd33d51d85be
-- title:
--   Paths of a Markov chain, flows for a distribution (Definition 14) and the congestion $\rho(f)$
-- statement:
--   Let $P$ be a Markov chain on $\Omega$. A **path** is a nonempty sequence $\gamma=(\gamma_0,\dots,\gamma_{L(\gamma)})$ of states with $P(\gamma_i,\gamma_{i+1})>0$; its length is $L(\gamma)$, and $(Z,Z')\in\gamma$ means that $(Z,Z')$ is a consecutive pair of $\gamma$. A **flow** for a distribution $p$ on $\Omega$ is a function $f$ on paths, with values in $[0,1]$, such that
--   $$\sum_{\gamma\in\Gamma(I,F)}f(\gamma)=p(I)p(F)\quad\text{for all }I\ne F\in\Omega,$$
--   where $\Gamma(I,F)$ is the set of paths from $I$ to $F$. The **congestion** of $f$ is
--   $$\rho(f):=\max_{(Z,Z'):\,P(Z,Z')>0}\frac1{p(Z)P(Z,Z')}\sum_{\gamma\ni(Z,Z')}f(\gamma)L(\gamma).$$
--   Each path is counted once in a sum over $\gamma\ni(Z,Z')$.
--
--   These notions bound mixing times of reversible chains (Theorem 15) and are general: they involve no code.
--
--   **Formalization Note** Paths are nonempty lists and $f$ takes values in $\mathbb R_{\ge0}\cup\{\infty\}$ with $f\le1$, vanishing off the paths of $P$. Sums are `tsum`s in `ℝ≥0∞`, so no summability condition and no finite support is imposed. The congestion is an `ℝ≥0∞`-valued supremum.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), §3.3.2 and Definition 14, pp.18–19; Lemma 22, p.22

import Mathlib
open scoped ENNReal
noncomputable section

namespace CodeSW

/-- A **path** of the Markov chain `P` on `Ω`: a nonempty sequence `γ = (γ_0, …, γ_{L(γ)})` of
states with `P(γ_i, γ_{i+1}) > 0`, i.e. every step is an edge of `E(P)`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, §3.3.2, pp.18–19).

**Formalization Note** Paths are nonempty lists `List Ω`. -/
def IsPath {Ω : Type*} (P : Matrix Ω Ω ℝ) (γ : List Ω) : Prop :=
  γ ≠ [] ∧ List.IsChain (fun a b => 0 < P a b) γ

/-- The length `L(γ)` of a path: its number of steps (arXiv:2510.08446, manuscript sha256
4e4abb5e…, p.19). -/
def pathLength {Ω : Type*} (γ : List Ω) : ℕ := γ.length - 1

/-- The transition `(Z, Z')` lies on `γ`, written `(Z, Z') ∈ γ`: some consecutive pair of `γ` is
`(Z, Z')` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, p.19). -/
def UsesStep {Ω : Type*} (γ : List Ω) (Z Z' : Ω) : Prop :=
  (Z, Z') ∈ γ.zip γ.tail

open Classical in
/-- The total weight `∑_{γ ∋ (Z, Z')} f(γ)` of the paths through the transition `(Z, Z')`, each
path counted once (arXiv:2510.08446, manuscript sha256 4e4abb5e…, Lemma 22, p.22; proof of
Theorem 16, p.23). -/
def stepLoad {Ω : Type*} (f : List Ω → ℝ≥0∞) (Z Z' : Ω) : ℝ≥0∞ :=
  ∑' γ : List Ω, if UsesStep γ Z Z' then f γ else 0

open Classical in
/-- **Definition 14 (flow).** A flow for a distribution `p` on `Ω` (with respect to the chain `P`)
is a function `f : Ω* → [0, 1]` on paths with `∑_{γ ∈ Γ(I,F)} f(γ) = p(I) p(F)` for all
`I ≠ F ∈ Ω`, where `Γ(I, F)` is the set of paths from `I` to `F`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, Definition 14, p.19).

**Formalization Note** `f : List Ω → ℝ≥0∞` with `f γ ≤ 1`, vanishing off the paths of `P`; the
sum over `Γ(I, F)` is an `ℝ≥0∞`-valued `tsum`, so no summability condition and no finiteness of
the support is imposed. -/
def IsFlow {Ω : Type*} (P : Matrix Ω Ω ℝ) (p : Ω → ℝ) (f : List Ω → ℝ≥0∞) : Prop :=
  (∀ γ, f γ ≤ 1) ∧ (∀ γ, f γ ≠ 0 → IsPath P γ) ∧
    ∀ I F : Ω, I ≠ F →
      (∑' γ : List Ω, if γ.head? = some I ∧ γ.getLast? = some F then f γ else 0) =
        ENNReal.ofReal (p I * p F)

open Classical in
/-- The **congestion** of a flow,
`ρ(f) := max_{(Z,Z') ∈ E(P)} (1 / (p(Z) P(Z,Z'))) ∑_{γ ∈ Γ, (Z,Z') ∈ γ} f(γ) L(γ)`,
with `E(P) = {(U, V) : P(U, V) > 0}` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, p.19).

**Formalization Note** Valued in `ℝ≥0∞`: a supremum over the transitions with `P(Z, Z') > 0`
(`0` if there are none) of an `ℝ≥0∞` `tsum`; `1/(p(Z)P(Z,Z'))` is `ℝ≥0∞`-inversion, `⊤` when
`p(Z) = 0`. -/
def congestion {Ω : Type*} (P : Matrix Ω Ω ℝ) (p : Ω → ℝ) (f : List Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (Z : Ω) (Z' : Ω) (_ : 0 < P Z Z'),
    (ENNReal.ofReal (p Z * P Z Z'))⁻¹ *
      ∑' γ : List Ω, if UsesStep γ Z Z' then f γ * (pathLength γ : ℝ≥0∞) else 0

end CodeSW


