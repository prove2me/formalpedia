-- Prove2me | Definitions.Def_ArbLindbladLearn_suppQ
-- name    : ArbLindbladLearn_suppQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:34.411903+00:00
-- url     : https://prove2.me/theorems/7a4e362f-0019-4de0-bcf6-c56031d5b5a8
-- title:
--   Support-learning parameters $q, T, W, p_j, \alpha$
-- statement:
--   Fix a threshold $\eta\in(0,\Lambda]$. The support-learning stage uses
--   $$T=\frac1\Lambda,\quad q=\min\{q'\in\mathbb N_{>0}:(q'+1)!\ge4\Lambda/\eta\},\quad W=\sum_{j=1}^q|\ell_j'(0)|,\quad p_j=\frac{|\ell_j'(0)|}{W},\quad\alpha=\frac{\eta^2}{4W^2}.$$
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), setup before eq. (18), p.21; Algorithm 1 lines 1–2, p.23

import Mathlib
import Definitions.Def_ArbLindbladLearn_lagDeriv0
import Definitions.Def_ArbLindbladLearn_qSel
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The support-learning interpolation degree `q = min{q′ ∈ ℕ_{>0} : (q′+1)! ≥ 4Λ/η}` (setup before
eq. (18), Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.21; Algorithm 1 line 1, p.23). -/
def suppQ (Λ η : ℝ) : ℕ := qSel (4 * Λ / η)

/-- The support-learning time horizon `T = 1/Λ` (p.21). -/
def suppT (Λ : ℝ) : ℝ := 1 / Λ

/-- `W = Σ_{j=1}^q |ℓ′_j(0)|` for the support-learning nodes (p.21). -/
def suppW (Λ η : ℝ) : ℝ := chebW (suppQ Λ η) (suppT Λ)

/-- The node probabilities `p_j = |ℓ′_j(0)|/W`, `1 ≤ j ≤ q` (p.21). -/
def suppP (Λ η : ℝ) (j : ℕ) : ℝ := |lagDeriv0 (suppQ Λ η) (suppT Λ) j| / suppW Λ η

/-- The heaviness threshold `α = η²/(4W²)` (p.21). -/
def suppAlpha (Λ η : ℝ) : ℝ := η ^ 2 / (4 * suppW Λ η ^ 2)

end ArbLindbladLearn


