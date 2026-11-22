-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementA
-- name    : Formalism_HermitianCurvature_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:11.550827+00:00
-- url     : https://prove2.me/theorems/073d698a-9a66-4e20-b9bb-5fb6b23f2d53
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementA.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.A
open Formalism.DoubleCosetMeasures MeasureTheory
def LevelOneKernelPoint : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (l : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (C : Type) [AddCommGroup C] [Module R C] (e : C)
    (lam : C →ₗ[R] KR R) (μ₁ : Measure (lowW K (l ++ [1]) t))
    (μ₂ : Measure (upUniG K (l ++ [1]).sum)),
    BB R (l ++ [1]) t ψ C e lam μ₁ μ₂ ≠ 0 →
      lam e = Submodule.Quotient.mk (((t l.length)⁻¹ : Kˣ) : K)
def LevelOneKernelPair : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (l l' : List ℕ) (t t' : ℕ → Kˣ) (ψ : AddChar K ℂ)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (μ₁ : Measure (lowW K (l ++ [1]) t)) (μ₂ : Measure (upUniG K (l ++ [1]).sum))
    (μ₁' : Measure (lowW K (l' ++ [1]) t')) (μ₂' : Measure (upUniG K (l' ++ [1]).sum)),
    BB R (l ++ [1]) t ψ C e lam μ₁ μ₂ ≠ 0 → BB R (l' ++ [1]) t' ψ C e lam μ₁' μ₂' ≠ 0 →
      (((t l.length)⁻¹ : Kˣ) : K) - (((t' l'.length)⁻¹ : Kˣ) : K) ∈ R
end Formalism.FourierDecayAlt.A


