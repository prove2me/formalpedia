-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorPlaceNorm
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorPlaceNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:47.385381+00:00
-- url     : https://prove2.me/theorems/34eff639-eec3-4d40-8dc2-79465aa02821
-- title:
--   Tensor Place Norm
-- statement:
--   Definitions and structural lemmas for Tensor Place Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TensorPlaceNorm.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm
open Formalism.BasicNotions Formalism.L2.DIV
variable {ι : Type} [Fintype ι] {n n' : ℕ}
def placeNorm (lam : DomWeight n) (f : nablaSq ℂ n lam) : ℝ :=
  Real.sqrt (normFock lam f.1 f.1).re
def coefNorm (lam : ι → DomWeight n) (F : VV ℂ lam) : ℝ :=
  Real.sqrt (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) F F).re
def pureTen (lam : ι → DomWeight n) (f : ∀ τ, nablaSq ℂ n (lam τ)) : VV ℂ lam :=
  ⟨ten fun τ => (f τ).1, Submodule.subset_span ⟨fun τ => (f τ).1, fun τ => (f τ).2, rfl⟩⟩
def IsTensorMap (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') : Prop :=
  ∀ f : ∀ τ, nablaSq ℂ n (lam τ), T (pureTen lam f) = pureTen lam' fun τ => A τ (f τ)
def TensorNormBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (c : ι → ℝ),
    (∀ τ, 0 ≤ c τ) →
    (∀ τ (f : nablaSq ℂ n (lam τ)), placeNorm (lam' τ) (A τ f) ≤ c τ * placeNorm (lam τ) f) →
    (∃! T : VV ℂ lam →ₗ[ℂ] VV ℂ lam', IsTensorMap lam lam' A T) ∧
      ∀ T : VV ℂ lam →ₗ[ℂ] VV ℂ lam', IsTensorMap lam lam' A T →
        ∀ F : VV ℂ lam, coefNorm lam' (T F) ≤ (∏ τ, c τ) * coefNorm lam F
end GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm


