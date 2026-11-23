-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:47.078074+00:00
-- url     : https://prove2.me/theorems/146a81fe-5b55-44c7-8b4b-c7200a5086b7
-- title:
--   Is Exp Lie Algebra Complex Units
-- statement:
--   Definitions and structural lemmas for Is Exp Lie Algebra Complex Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsExpLieAlgebraComplexUnits.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GroundTheory.Automorphic
namespace GlobalTheory.HCA
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤) {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤)
structure SmFn [MeasurableSpace G] (μ : Measure G) (S : Submodule ℂ (G → ℂ)) (K : Set G)
    (Λ : List (Fin d) → (G → ℂ) → ℂ) : Prop where
  lin : ∀ l, ∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ l (c • f + f') = c * Λ l f + Λ l f'
  bdd : ∀ l, ∃ C : ℝ, ∀ f ∈ S, ‖Λ l f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ
  der : ∀ l i, ∀ f ∈ S, HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) (Λ (i :: l) f) 0
def solG (P : Polynomial ℂ) : Submodule ℂ (G → ℂ) :=
  (LinearMap.ker (Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P)).map
    (h.smoothFuns (F := ℂ)).subtype
namespace SmFnEx
def idChar : (⊤ : Subgroup ℂˣ) →* ℂ := (Units.coeHom ℂ).comp (Subgroup.subtype ⊤)
end SmFnEx
end GlobalTheory.HCA
end


