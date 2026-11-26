-- Prove2me | Definitions.Def_HurewiczSketchV2
-- name    : HurewiczSketchV2
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-26T07:07:46.57562+00:00
-- url     : https://prove2.me/theorems/dc98afca-7dae-5bb4-a29c-fc7f397b92a5
-- title:
--   Reduced CW model (repaired) for the Hurewicz proof
-- statement:
--   A **reduced cellular model** in degree $r$ is a topological space $Y$ that carries a CW structure and whose homotopy groups below degree $r$ all vanish:
--
--   $$
--   \pi_k(Y,y)=0\qquad\text{for every }k<r\text{ and every }y\in Y.
--   $$
--
--   This is the homotopical form of the statement that the $(r-1)$-skeleton of the CW model has been reduced to a single point. It is the output of the cellular-reduction step in the proof of the Hurewicz theorem, and it is the hypothesis under which the cellular chain complex of $Y$ starts in degree $r$ and the cellular comparison identifies $\pi_r(Y,y)$ with $H_r(Y;\mathbb{Z})$.
--
--   **Formalization Note** The CW clause requires `Nonempty (Topology.CWComplex (Set.univ : Set Y))`, i.e. the whole space is a CW complex; this is deliberately stronger than the earlier vacuous formulation using an arbitrary subset. The collapsed skeleton is encoded by `Subsingleton` of `HomotopyGroup.Pi k Y y`.
-- source:
--   Tzuchien, 同伦论（5）：Hurewicz 定理, https://zhuanlan.zhihu.com/p/2063085365225863035, §2 定理 2.1 证明第一步至第三步; A. Hatcher, Algebraic Topology, Cambridge University Press (2002), Theorem 4.32, p. 366.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4Homology

set_option autoImplicit false

namespace HurewiczSketchV2

/-- A genuine reduced cellular model in degree `r`: the whole space carries a CW structure,
and all homotopy groups in degrees below `r` vanish at every base point.  Unlike the earlier
`HurewiczSketch.ReducedCWModel`, the CW clause uses `Set.univ`, so the empty subset cannot
satisfy it vacuously. -/
def ReducedCWModel (r : ℕ) (Y : Type) [TopologicalSpace Y] : Prop :=
  Nonempty (Topology.CWComplex (Set.univ : Set Y)) ∧
    ∀ k : ℕ, k < r → ∀ y : Y, Subsingleton (HomotopyGroup.Pi k Y y)

end HurewiczSketchV2


