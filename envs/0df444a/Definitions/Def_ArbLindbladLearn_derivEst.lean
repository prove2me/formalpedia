-- Prove2me | Definitions.Def_ArbLindbladLearn_derivEst
-- name    : ArbLindbladLearn_derivEst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:45.080744+00:00
-- url     : https://prove2.me/theorems/a14210bd-027f-4195-85d8-385ec3deb9f0
-- title:
--   Algorithm 2: degree $q$ and the witness-derivative estimate $\hat f_A'(0)$
-- statement:
--   Algorithm 2 sets $T=1/\Lambda$ and $q=\min\{q'\in\mathbb N_{>0}:(q'+1)!\ge12\Lambda/\varepsilon\}$, and estimates each witness derivative by
--   $$\hat f_A'(0)=\ell_0'(0)\Big|\frac1d\mathrm{tr}A\Big|^2+\sum_{j=1}^q\ell_j'(0)\hat f_A(t_j),$$
--   where $\hat f_A(t_j)$ are node estimates and $|\mathrm{tr}A/d|^2=f_A(0)$ (Lemma 4.1).
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Algorithm 2 lines 2 and 23, p.31

import Mathlib
import Definitions.Def_ArbLindbladLearn_lagDeriv0
import Definitions.Def_ArbLindbladLearn_qSel
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The coefficient-learning interpolation degree `q = min{q′ ∈ ℕ_{>0} : (q′+1)! ≥ 12Λ/ε}`
(Algorithm 2, line 2, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.31). The time horizon is `T = 1/Λ`. -/
def coefQ (Λ ε : ℝ) : ℕ := qSel (12 * Λ / ε)

/-- The witness-derivative estimate of Algorithm 2, line 23 (p.31):
`f̂′_A(0) = ℓ′₀(0)|tr A / d|² + Σ_{j=1}^q ℓ′_j(0) F_j`, where `F_j` is the estimate of `f_A(t_j)`
and `|tr A/d|² = f_A(0)` (Lemma 4.1, p.26). -/
def derivEst {n : ℕ} (q : ℕ) (T : ℝ) (A : Op (Qubits n)) (F : ℕ → ℝ) : ℝ :=
  lagDeriv0 q T 0 * Complex.normSq (A.trace / (2 : ℂ) ^ n) +
    ∑ j ∈ Finset.Icc 1 q, lagDeriv0 q T j * F j

end ArbLindbladLearn


