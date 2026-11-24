-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:21.767104+00:00
-- url     : https://prove2.me/theorems/35df0338-08b0-4102-bfc1-ac979fd73675
-- title:
--   Base Change CB
-- statement:
--   Definitions and structural lemmas for Base Change CB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
variable {σ : Type} [Fintype σ]
noncomputable def quotExtEquiv (𝔭 : Ideal (MvPolynomial σ ℚ)) :
    (ℂ ⊗[ℚ] (MvPolynomial σ ℚ ⧸ 𝔭)) ≃+* (MvPolynomial σ ℂ ⧸ Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ℚ) ℂ (MvPolynomial σ ℚ) ℂ 𝔭).toRingEquiv.trans
    (Ideal.quotientEquiv _ _ (algebraTensorAlgEquiv ℚ ℂ).toRingEquiv (by
      have h : (algebraTensorAlgEquiv (σ := σ) ℚ ℂ).toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight : MvPolynomial σ ℚ →ₐ[ℚ] ℂ ⊗[ℚ] MvPolynomial σ ℚ).toRingHom
          = MvPolynomial.map (algebraMap ℚ ℂ) := by
        apply RingHom.ext
        intro p
        simp [Algebra.TensorProduct.includeRight_apply, algebraTensorAlgEquiv_tmul]
      rw [← h, ← Ideal.map_map]
      rfl))
section Rad
end Rad
section GD
attribute [local instance] MvPolynomial.algebraMvPolynomial
end GD
end ReciprocityTheory.AnForm.R.BaseChangeC


