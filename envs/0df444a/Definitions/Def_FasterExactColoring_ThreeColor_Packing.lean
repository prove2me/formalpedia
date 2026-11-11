-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Packing
-- name    : FasterExactColoring_ThreeColor_Packing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:08:00.947658+00:00
-- url     : https://prove2.me/theorems/6257143f-4543-473f-8b9a-0acf5abec459
-- title:
--   Uniform constructive cubic and subcubic packing specifications
-- statement:
--   A constructive cubic packing algorithm is one deterministic finite program which, on every connected cubic graph, outputs an actual distance-two packing within a uniform polynomial time bound. Given fixed $\alpha$ and loss $L$, its guarantee is
--   $$|P|\ge\alpha n-L.$$
--   The subcubic version requires every selected vertex to have original graph degree three and guarantees $|P|\ge\alpha n_3-L$, where $n_3$ counts those vertices.
--
--   The program, polynomial coefficient and exponent, and additive loss are fixed before the graph is supplied. These are operational predicates used in the premise and conclusion of Lemma 4.6; neither is an assumed solver object. A connected graph is nonempty. The case $n_3=0$ remains included in the subcubic conclusion.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemmas 4.5–4.6, p. 7 (PDF p. 9)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_GraphInput
import Definitions.Def_FasterExactColoring_ThreeColor_Execution

namespace FasterExactColoring.ThreeColor

/-- Constructive packing specifications, with the loss and polynomial uniform in G. -/
def cubicPackingAlgorithm (A : Program) (α loss C : ℝ) (d : ℕ) : Prop :=
  deterministic A ∧ ∀ (n : ℕ) (G : GraphInput n),
    connected G → (∀ v, degree G v = 3) →
    runWithin A (graphCode G) (polynomial C d (graphCode G))
      (fun y => ∃ X : Finset (Fin n), y = vertexSetCode X ∧
        twoPacking G X ∧ α*n-loss ≤ (X.card:ℝ))

def subcubicPackingAlgorithm (A : Program) (α loss C : ℝ) (d : ℕ) : Prop :=
  deterministic A ∧ ∀ (n : ℕ) (G : GraphInput n),
    connected G → (∀ v, degree G v ≤ 3) →
    runWithin A (graphCode G) (polynomial C d (graphCode G))
      (fun y => ∃ X : Finset (Fin n), y = vertexSetCode X ∧
        twoPacking G X ∧ (∀ v ∈ X, degree G v = 3) ∧
        α*(degreeSet G 3).card-loss ≤ (X.card:ℝ))

end FasterExactColoring.ThreeColor


