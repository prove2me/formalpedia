-- Prove2me | Definitions.Def_QCQPTightness_Exact_Proj
-- name    : QCQPTightness_Exact_Proj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:58.087864+00:00
-- url     : https://prove2.me/theorems/4d40ebb2-5871-4b44-b848-b24ad961ffe9
-- title:
--   §1.3 and Theorem 3, pp. 6, 23 — Proj_{𝒱(ℱ)} {b(γ) : γ ∈ ℱ}
-- statement:
--   For a subspace $V\subseteq\mathbb R^N$ and $x\in\mathbb R^N$, $\mathrm{Proj}_V x$ is the orthogonal projection of $x$ onto $V$ (§1.3). For a set $\mathcal F\subseteq\mathbb R^m$ with shared zero eigenspace $\mathcal V(\mathcal F)$, the set
--
--   $$\mathrm{Proj}_{\mathcal V(\mathcal F)}\{b(\gamma):\gamma\in\mathcal F\} = \{\mathrm{Proj}_{\mathcal V(\mathcal F)}\,b(\gamma) : \gamma\in\mathcal F\}\subseteq\mathbb R^N$$
--
--   collects the projections of the linear parts $b(\gamma)=b_0+\sum_i\gamma_ib_i$ over $\gamma\in\mathcal F$. Theorem 3 asks that it avoid $0$ on every semidefinite face.
--
--   **Formalization Note** The projection is taken in `EuclideanSpace ℝ (Fin N)`, which carries the standard inner product. The plain function type `Fin N → ℝ` carries the sup norm and has no inner product. `VE P F` is $\mathcal V(\mathcal F)$ transported there, and `starProjection` is Mathlib's orthogonal projection as an endomorphism.
-- source:
--   arXiv:1911.09195v3, §1.3 p. 6 (Proj_V), Theorem 3 p. 23

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces

noncomputable section

namespace QCQPTightness.Exact

/-- The shared zero eigenspace `𝒱(ℱ)` of `F`, transported to Euclidean space `ℝ^N`
(`EuclideanSpace ℝ (Fin N)`, which carries the standard inner product). -/
def VE {N m : ℕ} (P : QCQP N m) (F : Set (Fin m → ℝ)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
  (P.V F).map (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap

/-- `Proj_{𝒱(ℱ)} {b(γ) : γ ∈ ℱ}` (§1.3, p. 6; Theorem 3, p. 23): the image of `F` under
`γ ↦` the orthogonal projection of `b(γ)` onto `𝒱(ℱ)`. -/
def projB {N m : ℕ} (P : QCQP N m) (F : Set (Fin m → ℝ)) : Set (EuclideanSpace ℝ (Fin N)) :=
  (fun γ => (VE P F).starProjection (WithLp.toLp 2 (P.bγ γ))) '' F

end QCQPTightness.Exact


