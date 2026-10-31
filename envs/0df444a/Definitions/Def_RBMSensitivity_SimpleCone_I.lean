-- Prove2me | Definitions.Def_RBMSensitivity_SimpleCone_I
-- name    : RBMSensitivity_SimpleCone_I
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:10.087566+00:00
-- url     : https://prove2.me/theorems/54a4bf9e-5f39-4c61-b2d6-cb9e3ec84047
-- title:
--   The face index set $\mathcal I(x)$
-- statement:
--   For each $i$, the $i$th face is $F_i:=\{x\in\partial G:\langle x,n_i\rangle=0\}$. For $x\in G$,
--   $$\mathcal I(x):=\{i\in\mathcal I:x\in F_i\}$$
--   is the (possibly empty) set of indices of the faces that contain $x$.
--
--   **Formalization Note** The formal definition is $\{i:\langle x,n_i\rangle=0\}$. On $G$ it agrees with the paper's, because a point of $G$ on such a hyperplane is on $\partial G$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, (2.1), p.5

import Mathlib
import Definitions.Def_RBMSensitivity_SimpleCone
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The index set `I(x)` of (2.1): arXiv:1907.00472v2, §2.1, p.5.

**Formalization Note.** The paper has `F_i := {x ∈ ∂G : ⟨x, n_i⟩ = 0}` and `I(x) := {i : x ∈ F_i}`.
A point of `G` on the hyperplane `⟨x, n_i⟩ = 0` lies in `∂G`, so for `x ∈ G` this definition agrees
with the paper. The whole index set `I` of the paper is `Set.univ`. -/
def SimpleCone.I {J : ℕ} (C : SimpleCone J) (x : E J) : Set (Fin J) :=
  {i | ⟪x, C.n i⟫ = 0}

end RBMSensitivity


