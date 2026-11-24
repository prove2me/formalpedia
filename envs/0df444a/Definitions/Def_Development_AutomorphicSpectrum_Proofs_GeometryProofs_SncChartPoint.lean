-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
-- name    : Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:36.646012+00:00
-- url     : https://prove2.me/theorems/45a76fc1-20fd-44b7-a434-50c6a08de1fd
-- title:
--   Snc Chart Point
-- statement:
--   Definitions and structural lemmas for Snc Chart Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/SncChartPoint.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SncRes
def SncChart {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (e : ℕ) (h : Ω) : Prop :=
  ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ A) ∧ (∀ l, a l ∈ A) ∧ ∑ l, a l * f l = 1 ∧
    ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (f l)⁻¹ (A : Set Ω)) →
      Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
        LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
        ∀ q : Ideal S, q.IsPrime →
          ((∀ s : S, (s : Ω) = h → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)
end GlobalTheory.CompanionTheory.Ar.SncRes


