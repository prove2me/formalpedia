-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementK
-- name    : Formalism_HermitianCurvature_StatementK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:26.275264+00:00
-- url     : https://prove2.me/theorems/520db273-5dbf-445f-a6ff-7f4a86d6f1aa
-- title:
--   Statement K
-- statement:
--   Definitions and structural lemmas for Statement K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementK.lean

import Definitions.Def_Formalism_HermitianCurvature_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.K
open Matrix Finset Real
def IsUpUni {K : Type} [Field K] {n : ℕ} (u : Matrix (Fin n) (Fin n) K) : Prop :=
  u.BlockTriangular id ∧ ∀ a, u a a = 1
def w0 {K : Type} [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun a b => if (a : ℕ) + (b : ℕ) + 1 = n then 1 else 0
def BigCellFree : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (v v' u u' : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    IsUpUni v → IsUpUni v' → IsUpUni u → IsUpUni u' → (∀ a, d a ≠ 0) →
    u * (v * w0 n * Matrix.diagonal d * v') * u' = v * w0 n * Matrix.diagonal d * v' →
    u = 1 ∧ u' = 1
def JointTheoremA : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C' C : ℝ, ∀ (Kx Θ : ℝ) (f r : ℕ) (e σ : ℕ → ℝ),
    4 ≤ Kx → 1 ≤ f → C' ≤ Θ → (r : ℝ) * (C₀ / Θ) ^ f ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + (C₀ * Θ ^ (-(Kx - 5/2))) ^ f) * √(1 + e i) * σ (i - 1) +
        ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ f) ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2
end Formalism.FourierDecayAlt.K


