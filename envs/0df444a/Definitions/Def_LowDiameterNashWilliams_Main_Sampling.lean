-- Prove2me | Definitions.Def_LowDiameterNashWilliams_Main_Sampling
-- name    : LowDiameterNashWilliams_Main_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:05.7809+00:00
-- url     : https://prove2.me/theorems/9c0c401d-af19-4cac-9694-18a7ba7a40c8
-- title:
--   Independent neighbor-subset laws and perfect matchings
-- statement:
--   A simple bipartite graph with two classes of size $m$ is represented by the neighbor set $N(j)$ on the left of each right vertex $j$. Its two minimum degrees count distinct neighbors. A perfect matching is a bijection assigning every right vertex a neighboring left vertex.
--
--   For an arbitrary probability mass function $\mu_j$ on whole subsets of the left class, define
--
--   $$a_j(X)=\sum_{S:S\cap X=\varnothing}\mu_j(S),\qquad
--   q=\sum_{s:\,s\text{ has a perfect matching}}\prod_j\mu_j(s_j).$$
--
--   Thus $a_j$ is the avoidance probability and $q$ is the perfect-matching probability under independent sampling across right vertices. Individual edges within one sampled subset need not be independent. Support inside the graph's actual neighbor sets and exponential avoidance are hypotheses of Lemma 4.4, not assumptions bundled into these definitions. This finite probability interface represents every law permitted by the source.
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 4.4, p. 16 (PDF p. 17)

import Mathlib

set_option autoImplicit false
open scoped ENNReal NNReal
open Classical
open scoped BigOperators

namespace LowDiameterNashWilliams.Main

/-! Lemma 4.4 (PDF 17): a bipartite simple graph is its right-neighbor map.
Arbitrary laws on whole neighbor subsets are independent across right vertices only. -/
noncomputable def leftMin {m : ℕ} (N : Fin m → Finset (Fin m)) : ℕ :=
  if h : (Finset.univ : Finset (Fin m)).Nonempty then
    Finset.univ.inf' h (fun i => (Finset.univ.filter fun j => i ∈ N j).card) else 0

noncomputable def rightMin {m : ℕ} (N : Fin m → Finset (Fin m)) : ℕ :=
  if h : (Finset.univ : Finset (Fin m)).Nonempty then
    Finset.univ.inf' h (fun j => (N j).card) else 0

def PerfectMatching {m : ℕ} (N : Fin m → Finset (Fin m)) : Prop :=
  ∃ f : Fin m ≃ Fin m, ∀ j, f j ∈ N j

noncomputable def avoidance {m : ℕ} (μ : PMF (Finset (Fin m))) (X : Finset (Fin m)) : ℝ≥0∞ :=
  ∑ S : Finset (Fin m), if Disjoint S X then μ S else 0

noncomputable def matchingProbability {m : ℕ}
    (μ : Fin m → PMF (Finset (Fin m))) : ℝ≥0∞ :=
  ∑ s : Fin m → Finset (Fin m), if PerfectMatching s then ∏ j, μ j (s j) else 0

end LowDiameterNashWilliams.Main


