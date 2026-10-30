-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P30
-- name    : QAlgorithms_Papers_Independent_Bridge50_P30
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:31:23.504875+00:00
-- url     : https://prove2.me/theorems/2f99cef8-dd0f-4bce-bc9f-20f48acd6bde
-- title:
--   Definitions for Von Neumann Entropy-Preserving Quantum Operations
-- statement:
--   The objects the formalized statements of *Von Neumann Entropy-Preserving Quantum Operations* (arXiv:1104.2992) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsBistochastic`: PDF p.2, Section 1: a bi-stochastic operation is a trace-preserving CP map that preserves the identity. The accepted finite Kraus predicate `IsChannel` encodes CP and trace preservation on every operator; complex linearity is bundled.
--   - `mapEntropy`: PDF p.2, Section 1: map entropy S(J(Phi)/N). The accepted Choi matrix is unnormalized and output-first. All theorem uses have N > 0 and a channel Phi.
--   - `krausMatrix`: PDF p.5, Section 3: the Kraus matrix B(Phi). Its (i,j) entry is the output i population of the input matrix unit |j><j|, equivalently sum_mu |M_mu(i,j)|^2 for any Kraus representation of the channel. This coordinate expression is independent of the choice of Kraus representation.
-- source:
--   Von Neumann Entropy-Preserving Quantum Operations, arXiv:1104.2992v4, https://arxiv.org/abs/1104.2992v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

/-!
Statements from Zhang and Wu, *Von Neumann Entropy-Preserving Quantum Operations*,
arXiv:1104.2992v4. All locators are PDF pages. The system is C^(Fin N), N > 0,
with its coordinate orthonormal basis. Entropies are in bits and allow zero eigenvalues.
The full structural Theorem 2.1 and its extension in Remark 2.2 are deferred:
the single invariant block decomposition in (iii) fails for Hadamard after dephasing.
The separately inventoried equivalence (i) iff (ii) is explicitly proved on PDF p.3.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P30

open QAlgorithms.Papers.Independent.Information100.P50
  (M Lin choiMatrix hilbertSchmidtAdjoint)
open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- PDF p.2, Section 1: a bi-stochastic operation is a trace-preserving CP map
that preserves the identity. The accepted finite Kraus predicate `IsChannel`
encodes CP and trace preservation on every operator; complex linearity is bundled. -/
def IsBistochastic {N : ℕ} (Phi : Lin N N) : Prop :=
  IsChannel Phi ∧ Phi 1 = 1

/-- PDF p.2, Section 1: map entropy S(J(Phi)/N). The accepted Choi matrix is
unnormalized and output-first. All theorem uses have N > 0 and a channel Phi. -/
def mapEntropy {N : ℕ} (Phi : Lin N N) : ℝ :=
  vnEntropy (((N : ℂ)⁻¹) • choiMatrix Phi)

/-- PDF p.5, Section 3: the Kraus matrix B(Phi). Its (i,j) entry is the
output i population of the input matrix unit |j><j|, equivalently
sum_mu |M_mu(i,j)|^2 for any Kraus representation of the channel.
This coordinate expression is independent of the choice of Kraus representation. -/
def krausMatrix {N : ℕ} (Phi : Lin N N) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (Phi (Matrix.single j j 1) i i).re

/-- Sanity check: the identity channel is bi-stochastic in every finite dimension. -/
example (N : ℕ) : IsBistochastic (LinearMap.id : Lin N N) := by
  refine ⟨?_, rfl⟩
  refine ⟨1, fun _ => 1, ?_, ?_⟩
  · simp [IsKrausFamily]
  · intro X
    simp [krausApply]

/-- Sanity check: the one-dimensional zero map has zero normalized Choi matrix. -/
example : mapEntropy (0 : Lin 1 1) =
    vnEntropy (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by
  have hchoi : choiMatrix (0 : Lin 1 1) =
      (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := rfl
  simp only [mapEntropy, hchoi, smul_zero]

/-- Sanity check: B(id) has its single entry equal to one when N = 1. -/
example : krausMatrix (LinearMap.id : Lin 1 1) 0 0 = 1 := by
  simp [krausMatrix, Matrix.single]

end QAlgorithms.Papers.Independent.Bridge50.P30


