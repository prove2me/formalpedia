-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MiracleFlatness_MulXProjQExact
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MiracleFlatness_MulXProjQExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:09.552657+00:00
-- url     : https://prove2.me/theorems/a5255b46-75cd-43c3-b010-498cddfe5e66
-- title:
--   Mul XProj QExact
-- statement:
--   Definitions and structural lemmas for Mul XProj QExact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MiracleFlatness/MulXProjQExact.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MiracleFlatness_FromQuotTensorToQuotTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open TensorProduct
namespace PI.UnitaryGroupMassFormula.MF
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
noncomputable def mulMap (𝔞 : Ideal A) : B ⊗[A] 𝔞 →ₗ[B] B :=
  (AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ AlgebraTensorModule.lTensor B B 𝔞.subtype
@[simp] lemma mulMap_tmul (𝔞 : Ideal A) (b : B) (a : 𝔞) : mulMap 𝔞 (b ⊗ₜ a) = (a : A) • b := by
  simp [mulMap]
variable (x : A)
noncomputable def mulX (𝔞 𝔟 : Ideal A) (h1 : ∀ b ∈ 𝔟, x * b ∈ 𝔞) : 𝔟 →ₗ[A] 𝔞 :=
  (LinearMap.mulLeft A x).restrict (p := 𝔟) (q := 𝔞) h1
@[simp] lemma mulX_apply (𝔞 𝔟 : Ideal A) (h1 : ∀ b ∈ 𝔟, x * b ∈ 𝔞) (b : 𝔟) :
    ((mulX x 𝔞 𝔟 h1 b : 𝔞) : A) = x * b := rfl
noncomputable def projQ (𝔞 : Ideal A) : 𝔞 →ₗ[A] (𝔞.map (Ideal.Quotient.mk (Ideal.span {x}))) where
  toFun a := ⟨Ideal.Quotient.mk _ a, Ideal.mem_map_of_mem _ a.2⟩
  map_add' a b := by ext; simp
  map_smul' c a := by
    ext
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
end PI.UnitaryGroupMassFormula.MF


