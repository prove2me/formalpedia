-- Prove2me | Definitions.Def_ParamSDPTraj_pair
-- name    : ParamSDPTraj_pair
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:42.191368+00:00
-- url     : https://prove2.me/theorems/b4813dbd-b631-44fd-a19e-d2a66f929c0e
-- title:
--   Trace pairing $\langle M,X\rangle$
-- statement:
--   For real $n\times n$ matrices $M$ and $X$, the **trace pairing** is
--
--   $$\langle M,X\rangle=\operatorname{trace}(MX).$$
--
--   On symmetric matrices this is the entrywise scalar product $\sum_{i,j}M_{i,j}X_{i,j}$. It is the inner product of the space $\mathbb S^n$ in which the whole mission lives.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, §2.1, p.5

import Mathlib

namespace ParamSDPTraj

/-- **Trace pairing ⟨M, X⟩.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, §2.1, p.5: "their scalar product is denoted by ⟨X, Z⟩ = trace(XZ)".

**Formalization Note** Defined on all square matrices; on symmetric matrices it is the entrywise
sum `∑ i j, X i j * Z i j`. -/
noncomputable def pair {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (M * X).trace

end ParamSDPTraj


