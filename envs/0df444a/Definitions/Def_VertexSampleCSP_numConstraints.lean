-- Prove2me | Definitions.Def_VertexSampleCSP_numConstraints
-- name    : VertexSampleCSP_numConstraints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:25.271448+00:00
-- url     : https://prove2.me/theorems/fabeb9e7-a661-4288-a85d-fcc7c6d94aca
-- title:
--   Number of constraints $m$ of an instance
-- statement:
--   An $r$-subset $e$ **carries a constraint** if its table is not identically zero, $f_e\ne0$. The number of constraints $m$ of $\mathcal I$ is the number of such $r$-subsets.
--
--   This is the quantity that makes the error bound of the mission's goal theorem sensitive to the density of the instance.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), §1.1, p.2 (PDF p.4); Corollary D.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance

namespace VertexSampleCSP

open Classical in
/-- **Number of constraints `m`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction
Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), §1.1, p.2 (PDF p.4): "the set e
carries a constraint if fe ≠ 0, and m is the number of constraints"; Corollary D.1, p.18: "m tables
are nonzero".

`numConstraints I` is the number of `r`-subsets `e ⊆ V` whose table `f_e` is not identically zero. -/
noncomputable def numConstraints {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) : ℕ :=
  ((Finset.powersetCard r Finset.univ).filter (fun e => I.f e ≠ 0)).card

end VertexSampleCSP


