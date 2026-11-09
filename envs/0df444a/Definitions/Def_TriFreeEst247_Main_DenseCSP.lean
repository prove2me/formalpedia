-- Prove2me | Definitions.Def_TriFreeEst247_Main_DenseCSP
-- name    : TriFreeEst247_Main_DenseCSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:56:45.462071+00:00
-- url     : https://prove2.me/theorems/edcb8d6b-f0df-4ca9-8d47-4899e24466ac
-- title:
--   Dense normalized 3-CSPs, sampled optima, and local-function queries
-- statement:
--   Let $V=[n]$, $n\ge3$, and let $A$ be a finite alphabet with $|A|\ge2$. A dense normalized 3-CSP assigns a function $Q_{xyz}:A^3\to[0,1]$ to each ordered triple of distinct vertices, and requires each such function to attain one. Writing $(n)_3=n(n-1)(n-2)$, define
--
--   $$\operatorname{val}_Q(\sigma)=\frac{1}{(n)_3}\sum_{x,y,z\text{ distinct}}Q_{xyz}(\sigma x,\sigma y,\sigma z),\qquad \mathrm{OPT}_{\mathrm{CSP}}(Q)=\max_\sigma\operatorname{val}_Q(\sigma).$$
--
--   For a subset $U$ of size $N\ge3$, retain the original functions and define
--
--   $$\mathrm{OPT}_{\mathrm{CSP}}(Q;U)=\frac{(n/N)^3}{(n)_3}\max_{\sigma:U\to A}\sum_{x,y,z\in U\text{ distinct}}Q_{xyz}(\sigma x,\sigma y,\sigma z).$$
--
--   The expected sampled optimum is the uniform average over all $N$-element subsets. A local-function query returns $Q_{xyz}$ on all label triples at once. The CSP algorithm is a randomized decision tree with these whole functions as answers.
--
--   This interface is shared by the compression and subsampling results; it imposes no graph origin on a general CSP.
--
--   **Formalization Note** Values on repeated-variable triples are total extensions and never enter the objective. Maxima are real suprema of finite nonempty ranges on valid instances. Sample labelings are extended to all vertices, changing no attainable sum because the alphabet is nonempty. An empty subset gives zero by total division, and the average over an empty family is zero; theorem hypotheses exclude both situations.
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.7–8, Definition 2.3; local-function access model

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical

noncomputable section

namespace TriFreeEst247.Main

/-- Definition 2.3, pp.7--8. Values on repeated-variable triples are unused. -/
abbrev CSP (n : ℕ) (A : Type) := Fin n → Fin n → Fin n → A → A → A → ℝ

def distinct3 {n : ℕ} (x y z : Fin n) : Prop := x ≠ y ∧ y ≠ z ∧ z ≠ x

def falling3 (n : ℕ) : ℕ := n * (n - 1) * (n - 2)

def isDense {n : ℕ} {A : Type} [Fintype A] (Q : CSP n A) : Prop :=
  3 ≤ n ∧ 2 ≤ Fintype.card A ∧
  ∀ x y z, distinct3 x y z →
    (∀ a b c, 0 ≤ Q x y z a b c ∧ Q x y z a b c ≤ 1) ∧
    ∃ a b c, Q x y z a b c = 1

def cspValue {n : ℕ} {A : Type} (Q : CSP n A) (σ : Fin n → A) : ℝ := by
  classical
  exact (∑ x, ∑ y, ∑ z, if distinct3 x y z then Q x y z (σ x) (σ y) (σ z) else 0) /
    (falling3 n : ℝ)

/-- Finite maximum whenever the alphabet is finite and nonempty. -/
def cspOpt {n : ℕ} {A : Type} [Fintype A] (Q : CSP n A) : ℝ :=
  sSup (Set.range (cspValue Q))

/-- A labeling on all vertices is used only through its restriction to U.
Every U-labeling extends when A is nonempty. The full n-dependent Q is retained. -/
def sampledOpt {n : ℕ} {A : Type} [Fintype A] (Q : CSP n A)
    (U : Finset (Fin n)) : ℝ := by
  classical
  exact ((n : ℝ) / (U.card : ℝ))^3 / (falling3 n : ℝ) *
    sSup (Set.range (fun σ : Fin n → A =>
      ∑ x ∈ U, ∑ y ∈ U, ∑ z ∈ U,
        if distinct3 x y z then Q x y z (σ x) (σ y) (σ z) else 0))

/-- Uniform expectation over N-subsets, without replacement. -/
def expectedSampledOpt {n : ℕ} {A : Type} [Fintype A] (Q : CSP n A) (N : ℕ) : ℝ := by
  classical
  let subsets := (Finset.univ : Finset (Fin n)).powersetCard N
  exact (∑ U ∈ subsets, sampledOpt Q U) / (subsets.card : ℝ)

/-- One query returns the entire local function, including all label choices. -/
abbrev CSPAlgorithm (n : ℕ) (A : Type) :=
  QAlgorithms.RandDecisionTree (Fin n × Fin n × Fin n) (A × A × A → ℝ) ℝ

def cspOracle {n : ℕ} {A : Type} (Q : CSP n A) :
    (Fin n × Fin n × Fin n) → (A × A × A → ℝ) :=
  fun p a => Q p.1 p.2.1 p.2.2 a.1 a.2.1 a.2.2

end TriFreeEst247.Main


