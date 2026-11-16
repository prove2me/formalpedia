-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_Supplement_rCuts
-- name    : MaxCutSample2027_Coreset_Supplement_rCuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:58:34.575221+00:00
-- url     : https://prove2.me/theorems/2f51089d-fb46-4947-8373-5289f403ca0e
-- title:
--   Matrix adapter for the published r-way cut optimum
-- statement:
--   For a real matrix $B$ on a finite vertex set $W$ and an integer $r\ge2$, an assignment $f:W\to\{0,\ldots,r-1\}$ specifies a partition into at most $r$ parts. Empty parts are allowed. Its value and optimum are
--   $$\operatorname{Cut}_r(B,f)=\sum_{u,v:\ f(u)<f(v)}B_{uv},\qquad
--   \operatorname{MaxCut}_r(B)=\max_f\operatorname{Cut}_r(B,f).$$
--   For symmetric matrices, each crossing edge is counted exactly once. The general graph, cut, and finite maximum are reused from the published Max3CutHard definitions. The adapter lists each ordered pair with half its matrix weight, so symmetry gives exactly the displayed sum. At r = 0 the wrapper returns zero, a case excluded by every theorem here. In particular, applying this definition to $\widehat A$ optimizes over assignments of sample positions in $\operatorname{Fin}(k)$; copies of a repeated vertex may be assigned independently. Only the matrix adapter is new; the general r-way cut object is published and independent of the fractional comparison model. Vertex types in the adapter inhabit Type, which represents every finite source vertex set.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §5, r-way cut definition, p. 23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_cuts
import Definitions.Def_Max3CutHard_maxCutR
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

/-- Two oriented half-weight entries represent each undirected matrix edge. -/
def matrixGraph {V : Type} [Fintype V] [DecidableEq V]
    (A : V → V → ℝ) : Max3CutHard.RGraph V :=
  (Finset.univ : Finset (V × V)).toList.map (fun uv => (uv, A uv.1 uv.2 / 2))

/-- The published general cut functional, applied to the matrix adapter. -/
def cutValueR {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}
    (A : V → V → ℝ) (f : V → Fin r) : ℝ :=
  Max3CutHard.cutR f (matrixGraph A)

/-- Reuse the published finite maximum; r = 0 lies outside every statement here. -/
def maxCutR {V : Type} [Fintype V] [DecidableEq V] (r : ℕ) (A : V → V → ℝ) : ℝ :=
  if h : r = 0 then 0 else
    letI : NeZero r := ⟨h⟩
    Max3CutHard.maxCutR r (matrixGraph A)

end MaxCutSample2027.Coreset.Supplement


