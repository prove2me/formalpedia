-- Prove2me | Definitions.Def_MaxCompForest_normLap
-- name    : MaxCompForest_normLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:57.145404+00:00
-- url     : https://prove2.me/theorems/d4fd431d-a51a-495f-8d1d-6bd70de17731
-- title:
--   Mass-normalized Laplacian $N_W=W^{-1/2}LW^{-1/2}$
-- statement:
--   Let $L$ be the combinatorial Laplacian of a finite loopless weighted graph on $V$, and $W=\mathrm{diag}(w_v)$ a diagonal matrix of positive vertex masses. The **mass-normalized Laplacian** is
--   $$
--   N_W=W^{-1/2}\,L\,W^{-1/2}.
--   $$
--   Taking $W=D$, the weighted degree matrix, gives the normalized Laplacian $N_G=D^{-1/2}L_GD^{-1/2}$.
--
--   Section 2 proves its bounds for arbitrary positive masses, so that the graph may be disconnected; the forest algorithm uses the degree masses.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), §2.1, p.7; p.2

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_massInvSqrt
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The mass-normalized Laplacian** `N_W = W^{-1/2} L W^{-1/2}`; `N_G` is `W = deg`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), §2.1, p.7; p.2 for `N_G = D^{-1/2} L_G D^{-1/2}`.

**Formalization Note.** `L` is the published `laplacian`, `Bᵀ C B` with `B` edges × vertices; the
paper's `B` is vertices × edges (p.14), the same matrix `L`. -/
noncomputable def normLap (G : WGraph V E) (W : V → ℝ) : Matrix V V ℝ :=
  massInvSqrt W * G.laplacian * massInvSqrt W

/-- `N_W` is symmetric, for every mass vector. -/
theorem normLap_isHermitian (G : WGraph V E) (W : V → ℝ) : (normLap G W).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [normLap, massInvSqrt, WGraph.laplacian, WGraph.weightMatrix, Matrix.transpose_mul,
    Matrix.diagonal_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]

end MaxCompForest


