-- Prove2me | Definitions.Def_RecGaussColoring_Main_Progress
-- name    : RecGaussColoring_Main_Progress
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:06.20301+00:00
-- url     : https://prove2.me/theorems/5fb8e125-b55c-4fba-a591-2f53841f018b
-- title:
--   Blum progress and sparse–dense graph domains
-- statement:
--   Let $G$ be an $n$-vertex graph, $C$ a constant and $f$ a scale. A progress output is a tagged list giving one of:
--
--   1. an independent set $S$ with $n\le Cf|S|$;
--   2. a nonempty independent set $S$ with $|N(S)|\le Cf|S|$;
--   3. distinct vertices $u,v$ receiving the same color in every proper three-coloring.
--
--   Thus
--   $$
--   \operatorname{IsProgress}(C,f,G,o)=P1\ \lor\ P2\ \lor\ P3.
--   $$
--   Tags are $1,2,3$. Set payloads are exact characteristic lists; pair payloads contain two vertex indices. The separate P1 predicate accepts the untagged characteristic payload used by the independent-set routine. Sparse and dense domains consist of three-colorable graphs satisfying respectively $\Delta\le n^\beta$ and $\delta\ge n^\beta$, together with $n\ge n_0$.
--
--   This module supplies only the output relation and domains. Polynomial running time and randomized success are expressed by the published RAM's solving predicates.
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Appendix B, pp. 25–26, p. 25. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Graph
import Definitions.Def_RecGaussColoring_Main_Parameters
import Definitions.Def_CongruencyTU_Machine

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- P1 uses exactly the independent-set routine's characteristic-vector payload. -/
def IsProgressP1 (C f : ℝ) (I : Graph3) (out : List ℤ) : Prop :=
  ∃ S : Finset (Fin I.n), DecodesSet I out S ∧ Independent I S ∧
    (I.n : ℝ) ≤ C*f*(S.card : ℝ)

/-- Appendix B: tags 1, 2, 3; exact payloads and no correctness bundled into decoding. -/
def IsProgress (C f : ℝ) (I : Graph3) (out : List ℤ) : Prop :=
  (∃ payload, out = 1 :: payload ∧ IsProgressP1 C f I payload) ∨
  (∃ payload S, out = 2 :: payload ∧ DecodesSet I payload S ∧ Independent I S ∧
    S.Nonempty ∧ ((neighbors I S).card : ℝ) ≤ C*f*(S.card : ℝ)) ∨
  (∃ u v : Fin I.n, out = [3, (u.val : ℤ), (v.val : ℤ)] ∧ u ≠ v ∧
    ∀ color : Fin I.n → Fin 3,
      (∀ i j, I.G.Adj i j → color i ≠ color j) → color u = color v)

def SparseDomain (β : ℝ) (n₀ : ℕ) (I : Graph3) : Prop :=
  ThreeColorable I ∧ (maxDeg I : ℝ) ≤ (I.n : ℝ)^β ∧ n₀ ≤ I.n

def DenseDomain (β : ℝ) (n₀ : ℕ) (I : Graph3) : Prop :=
  ThreeColorable I ∧ (I.n : ℝ)^β ≤ (minDeg I : ℝ) ∧ n₀ ≤ I.n

end RecGaussColoring.Main


