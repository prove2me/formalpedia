-- Prove2me | Definitions.Def_HurewiczSketch
-- name    : HurewiczSketch
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-25T13:03:02.446012+00:00
-- url     : https://prove2.me/theorems/4261c51a-5046-5719-834a-be93267b1688
-- title:
--   Reduced cellular model for the Hurewicz proof
-- statement:
--   A **reduced cellular model** in degree $r$ is a topological space $Y$ that admits a CW structure and whose homotopy groups below degree $r$ all vanish:
--
--   $$
--   \pi_k(Y,y)=0\qquad\text{for every }k<r\text{ and every }y\in Y.
--   $$
--
--   This is the homotopical form of the statement that the $(r-1)$-skeleton of the CW model has been reduced to a single point. It is the output of the cellular-reduction step in the proof of the Hurewicz theorem, and it is the hypothesis under which the cellular chain complex of $Y$ starts in degree $r$ and the cellular comparison identifies $\pi_r(Y,y)$ with $H_r(Y;\mathbb{Z})$.
--
--   **Formalization Note** The CW structure is encoded as the existence of a set $C\subseteq Y$ carrying an instance of Mathlib's `Topology.CWComplex`; the collapsed skeleton is encoded by `Subsingleton` of `HomotopyGroup.Pi k Y y`, i.e. triviality of the homotopy group, since the skeleton itself is not named in this formalization.
-- source:
--   Tzuchien, 同伦论（5）：Hurewicz 定理, https://zhuanlan.zhihu.com/p/2063085365225863035, §2 定理 2.1 证明第一步至第三步; A. Hatcher, Algebraic Topology, Cambridge University Press (2002), Theorem 4.32, p. 366.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4Homology

set_option autoImplicit false

namespace HurewiczSketch

def ReducedCWModel (r : ℕ) (Y : Type) [TopologicalSpace Y] : Prop :=
  (∃ C : Set Y, Nonempty (Topology.CWComplex C)) ∧
    ∀ k : ℕ, k < r → ∀ y : Y, Subsingleton (HomotopyGroup.Pi k Y y)

end HurewiczSketch


