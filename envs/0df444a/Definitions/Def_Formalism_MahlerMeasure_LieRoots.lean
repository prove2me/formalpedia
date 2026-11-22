-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_LieRoots
-- name    : Formalism_MahlerMeasure_LieRoots
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:47.825736+00:00
-- url     : https://prove2.me/theorems/22fc1910-661b-42f9-abb1-d2777d784159
-- title:
--   Lie Roots
-- statement:
--   Definitions and structural lemmas for Lie Roots, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/LieRoots.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open Finset Polynomial
open Classical in
def LieMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (t₀ : ℤ)
    (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    (∀ i j k, ‖c i j k‖ ≤ 1) → (∀ i j, ‖U i j‖ ≤ 1) → (∀ i j, ‖V i j‖ ≤ 1) →
    ‖U.det‖ = 1 → ‖V.det‖ = 1 → 0 ≤ E → del₀ ≤ p ^ h →
    (binMatK K del₀ c).map (Polynomial.eval (t₀ : K)) = U * Matrix.diagonal d * V →
    (gaussR (Real.toNNReal ((p : ℝ) ^ (-E)))
        (((binMatK K del₀ c).det).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))) : ℝ) ≤
      (p : ℝ) ^ (-(E * (univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card))
def LieRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (h β : ℕ) (E : ℝ) (D : K[X]) (lead : K) (roots : Multiset K) (t₀ : ℤ),
    0 ≤ E → lead ≠ 0 →
    D = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (gaussR (Real.toNNReal ((p : ℝ) ^ (-E)))
        (D.comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))) : ℝ) ≤ (p : ℝ) ^ (-(E * β)) →
    (β : ℝ) * E ≤
      (-Real.logb p ‖lead‖ + (roots.map (fun ζ => vmin p h ((t₀ : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)
end Formalism.GM


