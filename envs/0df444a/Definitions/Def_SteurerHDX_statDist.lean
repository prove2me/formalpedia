-- Prove2me | Definitions.Def_SteurerHDX_statDist
-- name    : SteurerHDX_statDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:04.639197+00:00
-- url     : https://prove2.me/theorems/5044590d-21ca-467a-9100-c352bc7382d2
-- title:
--   Stationary distribution $\mu(x)=D(x)/\sum_y D(y)$
-- statement:
--   For a weighted graph with weights $W$ and degrees $D$, the stationary distribution of the simple random walk is
--   $$\mu(x)=\frac{D(x)}{\sum_y D(y)} ,$$
--   which satisfies $\mu^{T}P=\mu$ for $P=D^{-1}W$ when $W$ is symmetric.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.1, p.3

import Mathlib
import Definitions.Def_SteurerHDX_vdeg

namespace SteurerHDX

/-- **Stationary distribution μ.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.1, p.3: "μ the stationary distribution of
the walk, i.e., we have μᵀP = μ and P1 = 1".

**Formalization Note.** For a symmetric weight matrix the stationary distribution of D⁻¹W is
μ(x) = D(x)/∑_y D(y); this explicit formula is used. -/
noncomputable def statDist {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (x : ι) : ℝ :=
  vdeg W x / ∑ y, vdeg W y

end SteurerHDX


