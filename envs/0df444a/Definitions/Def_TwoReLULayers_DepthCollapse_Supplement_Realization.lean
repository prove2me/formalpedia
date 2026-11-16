-- Prove2me | Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Realization
-- name    : TwoReLULayers_DepthCollapse_Supplement_Realization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T22:26:02.893207+00:00
-- url     : https://prove2.me/theorems/4e4fb5cb-7f45-4dbf-b9da-3652a0f6150c
-- title:
--   Rational coning realization with its prescribed orientation
-- statement:
--   Let $n,k\ge0$ and fix an orientation for every edge of the standard $n$-simplex. For a cubical basis label $(\gamma,\{i_1<\cdots<i_k\})$, let $B=\gamma+\sum_j[0,t_{i_j}]$ be its actual geometric box. Define its coning realization by
--   $$\rho(\gamma\otimes e_{i_1}\wedge\cdots\wedge e_{i_k})=
--   [\operatorname{conv}(\{0\}\cup B)]\in P_{k+1}^n,$$
--   with the ordered orientation $t_{i_1}\wedge\cdots\wedge t_{i_k}\wedge\gamma$. If those $k+1$ vectors are dependent, the class is zero by the explicit invalid-frame relation of the geometric quotient. The formal cubical generator itself is retained. Extend by finite rational linear combinations.
--
--   This is the actual coning map from formal cubes to geometric paramids. Its definition does not assume commutation with the boundary, surjectivity onto the paramid span, or a coning preimage of the simplex.
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026). Use this pinned PDF and its own labels; no arXiv version is asserted. p. 15, Section 3.1.

import Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Cubical

namespace TwoReLULayers.DepthCollapse.Supplement

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The ordered geometric frame is tᵢ₁,...,tᵢₖ,γ, with γ last. -/
def coneFrame {n k : ℕ} (o : EdgeOrientations n) (b : CubeLabel n k) :
    Fin (k + 1) → QSpace n :=
  Fin.snoc (fun j => rationalLattice (edgeZ o (b.2.val.orderEmbOfFin b.2.property j)))
    (rationalLattice b.1)

/-- Actual rational cone conv({0} ∪ box); dependent frames give zero in the
geometric quotient by its invalid-frame relation, without killing the cube itself. -/
def coneClass {n k : ℕ} (o : EdgeOrientations n) (b : CubeLabel n k) : P n (k + 1) :=
  polyClass ⟨coneFrame o b, insert 0 (cubeVertices o b)⟩

def rho {n k : ℕ} (o : EdgeOrientations n) (x : C n k) : P n (k + 1) :=
  x.sum (fun b q => q • coneClass o b)

end
end TwoReLULayers.DepthCollapse.Supplement


