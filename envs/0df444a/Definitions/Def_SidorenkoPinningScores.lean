-- Prove2me | Definitions.Def_SidorenkoPinningScores
-- name    : SidorenkoPinningScores
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-08T16:51:05.239019+00:00
-- url     : https://prove2.me/theorems/52be430e-769c-49df-a533-701626d8b9dd
-- title:
--   Incidence corners and vertex-pair scores
-- statement:
--   Let $I,J,E$ be finite sets, with incidence maps $t:E\to I$ and $h:E\to J$. Real vertex weights $L,R$ and pair weights $P$ assign the following score to arbitrary maps $a:I\to I$ and $b:J\to J$:
--   $$
--   S(a,b)=\sum_{i\in I}L_{a(i)}+\sum_{j\in J}R_{b(j)}
--          +\sum_{e\in E}P_{a(t(e)),\,b(h(e))}.
--   $$
--   The interface also enumerates the 66 corners of the fixed incidence pattern as $\mathrm{Fin}(22)\times\mathrm{Fin}(3)$, using the three distinct points of each prescribed face.
--
--   These scores express the finite pinning property used to isolate the identity assignment in the kernel construction. There are no sign restrictions on the score weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Dilution.lean#L140, VertexPairScores and VertexPairScores.score; Exposure.lean#L62, faceVertex; Activation.lean#L12, ActCorner and cornerPoint.

import Mathlib
import Definitions.Def_SidorenkoCounterexample

namespace OAI.SidorenkoCounterexample
open scoped BigOperators
def faceVertex : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]
abbrev ActCorner := Fin 22 × Fin 3
def cornerPoint (k : ActCorner) : Fin 13 := faceVertex k.1 k.2
structure VertexPairScores (I J : Type*) where
  left : I → ℝ
  right : J → ℝ
  pair : I → J → ℝ
variable {I J E : Type*} [Fintype I] [Fintype J] [Fintype E]
noncomputable def VertexPairScores.score (s : VertexPairScores I J) (t : E → I) (h : E → J)
    (a : I → I) (b : J → J) : ℝ := ∑ i,s.left (a i)+(∑ j,s.right (b j))+∑ e,s.pair (a (t e)) (b (h e))
end OAI.SidorenkoCounterexample


