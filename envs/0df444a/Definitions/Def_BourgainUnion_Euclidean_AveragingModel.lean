-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_AveragingModel
-- name    : BourgainUnion_Euclidean_AveragingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:00.483428+00:00
-- url     : https://prove2.me/theorems/258e9d26-96e2-418d-9d58-aa3076a4aa5b
-- title:
--   Separate pairwise extension factors and the averaging product
-- statement:
--   For an ambient set $Y$, an added subset $B\subseteq Y$ and prescribed map $f$ on $Y\setminus B$, an extension with factors $t,s$ agrees with $f$, expands pairs in $B$ by at most $t$, expands crossing pairs by at most $s$, and has all values in $\operatorname{conv}(f(Y\setminus B))$.
--
--   A geometric condition $P(Y,B)$ is restriction stable when restricting the ambient and added sets preserves it. It permits extensions with fixed $t,s$ when every eligible pair with nonempty $Y\setminus B$ permits the preceding extension for every $1$-Lipschitz prescribed map. These are the conditional assumptions of Lemma 4.8, separate from the unconditional goal. For $\eta=\max\{t-1,2(s-1)\}$ define
--   $$P_m(\eta)=\prod_{r=1}^m(1+\eta/r),\qquad P_0(\eta)=1.$$
--   A partition of the complement consists of nonempty disjoint sets. This model keeps both factors and the convex-hull clause available to the averaging theorem.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 19–20, Lemmas 4.7–4.8, equation (14)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- A map prescribed on Y minus B, with the two factors and the convex-hull conclusion. -/
def PairwiseExtension {X : Type*} [PseudoMetricSpace X]
    (t s : ℝ) (Y B : Set X) (f F : X → H2) : Prop :=
  Set.EqOn F f (Y \ B) ∧ LipOn t F B ∧
    (∀ a ∈ Y \ B, ∀ b ∈ B, dist (F a) (F b) ≤ s * dist a b) ∧
    F '' Y ⊆ convexHull ℝ (f '' (Y \ B))

/-- Geometric conditions are properties of actual ambient/subset pairs, in a fixed finite X. -/
def RestrictionStable {X : Type*} (P : Set X → Set X → Prop) : Prop :=
  ∀ Y B Y' B', P Y B → Y' ⊆ Y → B' ⊆ B → B' ⊆ Y' → P Y' B'

def PermitsExtensions {X : Type*} [PseudoMetricSpace X]
    (P : Set X → Set X → Prop) (t s : ℝ) : Prop :=
  ∀ Y B, B ⊆ Y → P Y B → (Y \ B).Nonempty →
    ∀ f : X → H2, LipOn 1 f (Y \ B) →
      ∃ F : X → H2, PairwiseExtension t s Y B f F

def PartitionComplement {X : Type*} {m : ℕ} (A : Set X) (B : Fin m → Set X) : Prop :=
  (∀ x, x ∉ A ↔ ∃ i, x ∈ B i) ∧ (∀ i, (B i).Nonempty) ∧
    ∀ i j, i ≠ j → Disjoint (B i) (B j)

def productFactor (η : ℝ) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.range m, (1 + η / (r+1 : ℕ))

end BourgainUnion.Euclidean


