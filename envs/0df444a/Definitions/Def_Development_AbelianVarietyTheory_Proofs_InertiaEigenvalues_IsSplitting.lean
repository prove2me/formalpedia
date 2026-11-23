-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:47.901785+00:00
-- url     : https://prove2.me/theorems/d47f7af2-f8d6-4449-8992-a88fdf0bad91
-- title:
--   Is Splitting
-- statement:
--   Definitions and structural lemmas for Is Splitting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSplitting.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
def WeilAt (A : Et F E) : Prop :=
  ∀ ψ : AddChar F ℂ, IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) →
    ∃ γ W, A.IsWeil ψ x A.etaK μ γ W
def IsSplitting (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L) : Prop :=
  (∀ k : A.K, eL (algebraMap A.K A.L k) = (algebraMap A₁.K A₁.L (eK k).1, algebraMap A₂.K A₂.L (eK k).2)) ∧
  (∀ e : E, eL (algebraMap E A.L e) = (algebraMap E A₁.L e, algebraMap E A₂.L e)) ∧
  ∀ y : A.L, eL (star y) = (star (eL y).1, star (eL y).2)
end GlobalTheory.JR


