-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_ExtensionModel
-- name    : BourgainUnion_Euclidean_ExtensionModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:44.123659+00:00
-- url     : https://prove2.me/theorems/c8131693-e55c-4a5c-aeb7-57f95e3f1cb4
-- title:
--   Ambient Lipschitz extension factors and their maximum
-- statement:
--   For a subset $A$ of a pseudometric space $X$, a factor $K\ge1$ is admissible if every $L$-Lipschitz map $f:A\to H_2$, for every real $L\ge0$, extends to $F:X\to H_2$ with
--   $$F|_A=f,\qquad \|F(x)-F(y)\|\le KLd(x,y).$$
--   The quantity $e_X(A)$ is the infimum of these factors in $[0,\infty]$. For a finite cover $U$, the maximum $e_{\max}$ discards empty members and has value one on the empty space. Constants, including $L=0$, are included.
--
--   This is an ambient-space dependent extension constant, universally quantified over maps. It is used in the comparison with distortion. Subset maps are represented by total ambient functions whose values off the prescribed subset are irrelevant. Infima do not assert existence of an extension at the optimal factor.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 3, 11–12, §1.2 and §3

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- All Lipschitz maps, including constants; total representatives of maps on A. -/
def ExtensionFactor {X : Type*} [PseudoMetricSpace X] (A : Set X) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ (L : ℝ), 0 ≤ L → ∀ f : X → H2, LipOn L f A →
    ∃ F : X → H2, Set.EqOn F f A ∧ LipOn (K * L) F Set.univ

def extensionConstant {X : Type*} [PseudoMetricSpace X] (A : Set X) : ℝ≥0∞ :=
  sInf {q | ∃ K : ℝ, ExtensionFactor A K ∧ q = ENNReal.ofReal K}

/-- Empty members are discarded. The empty-space convention is one. -/
def eMax {X : Type*} [PseudoMetricSpace X] {k : ℕ} (U : Fin k → Set X) : ℝ≥0∞ :=
  max 1 (⨆ i, ⨆ (_ : (U i).Nonempty), extensionConstant (U i))

end BourgainUnion.Euclidean


