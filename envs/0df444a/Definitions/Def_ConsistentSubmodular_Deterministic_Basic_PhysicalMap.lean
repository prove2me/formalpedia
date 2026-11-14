-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalMap
-- name    : ConsistentSubmodular_Deterministic_Basic_PhysicalMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:08.469638+00:00
-- url     : https://prove2.me/theorems/649e6e90-fbff-47b2-984b-0ebb15570db3
-- title:
--   Physical marginal vector $z(p)=\sum_i p_i\,\mathbf 1_{O_i}$ of a type vector
-- statement:
--   Let $O_0,\dots,O_m\subseteq\{0,\dots,n-1\}$ be a family of sets (`cores`) and let $p\in\mathbb R^{m+1}$ be a weight vector (`Point m`). The file defines one function.
--
--   - `physicalProbability cores p`: the vector $z(p)\in\mathbb R^{n}$ with coordinates
--   $$z(p)_e=\sum_{i=0}^{m}\mathbf 1[e\in O_i]\,p_i ,\qquad e<n,$$
--   that is, $z(p)=\sum_i p_i\mathbf 1_{O_i}$. When $p\in\Delta$ is a probability distribution on the sets, $z(p)_e$ is the probability that the element $e$ belongs to the set drawn according to $p$.
--
--   This is the same map as `WindowInstance.physicalVector` (equation (20) of the paper), stated for an arbitrary family of cores, independently of a window instance. It carries a mixture over candidates to a fractional vector on the physical elements, which is where the multilinear extension is evaluated in the comparison of mixtures with physical sampling (Appendix B.2).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/PhysicalMap.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n m : ℕ}

def physicalProbability (cores : Fin (m + 1) → Finset (Fin n))
    (p : Point m) (e : Fin n) : ℝ :=
  ∑ i, if e ∈ cores i then p i else 0

end ConsistentSubmodular

end


