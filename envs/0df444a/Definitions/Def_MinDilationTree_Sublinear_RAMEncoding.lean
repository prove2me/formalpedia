-- Prove2me | Definitions.Def_MinDilationTree_Sublinear_RAMEncoding
-- name    : MinDilationTree_Sublinear_RAMEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:25:52.853271+00:00
-- url     : https://prove2.me/theorems/9cd4cffd-9a28-4ab8-baab-0c1ff71341f3
-- title:
--   Point-set input and undirected output graph
-- statement:
--   The input consists of a point count followed by the Euclidean coordinates in label order:
--
--   $$
--   \operatorname{enc}(p)=[n,x_0,y_0,\ldots,x_{n-1},y_{n-1}].
--   $$
--
--   After the program halts, the next $n^2$ real cells are read as a row-major matrix $M$. Distinct labels $i,j$ form an undirected edge exactly when $M_{ij}\ne0$ or $M_{ji}\ne0$. Diagonal entries are ignored. The output graph at time $t$ is decoded from the state at that time; halting must be established separately.
--
--   This fixes the representation for Theorem 1 independently of the program and of every input. The model uses the published real RAM and the published admissibility predicate, which permits square roots and rational real literals and excludes random draws.
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 1 (PDF p. 2), Theorem 1; p. 30 (PDF p. 31), Theorem 1; encoding and machine reading R0

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_GeometricGraph
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible

set_option autoImplicit false

namespace MinDilationTree.Sublinear

/-- Fixed input of Theorem 1: n followed by x₀,y₀,…,xₙ₋₁,yₙ₋₁. -/
noncomputable def enc {n : ℕ} (p : Fin n → Plane) : List ℝ :=
  [(n : ℝ)] ++ (List.finRange n).flatMap (fun i => [p i 0, p i 1])

/-- Fixed symmetric graph decoder. Output cells contain an n×n matrix.
A nonzero entry in either orientation declares the undirected edge. Diagonal entries are ignored. -/
noncomputable def decodeGraph {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (M i j ≠ 0 ∨ M j i ≠ 0)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Read the graph at a specified step. Every algorithmic statement also asserts HaltsAt. -/
noncomputable def outputGraph {n : ℕ} (A : MatMulTimeLP.Program)
    (p : Fin n → Plane) (ω : MatMulTimeLP.Tape) (t : ℕ) : SimpleGraph (Fin n) :=
  decodeGraph (MatMulTimeLP.outputMatAt A (enc p) ω t 0 n n)

end MinDilationTree.Sublinear


