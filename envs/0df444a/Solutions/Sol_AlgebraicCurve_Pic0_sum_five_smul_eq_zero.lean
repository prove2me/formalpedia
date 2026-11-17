-- Prove2me | solution 1 for AlgebraicCurve.Pic0.sum_five_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:42.59707+00:00
-- url     : https://prove2.me/submissions/07f00f76-e29d-4468-8d4b-cba069ed89e0

import Mathlib
import Theorems.Thm_AlgEquiv_exists_fin_five_equiv_of_orderOf_eq_finrank
import Theorems.Thm_AlgebraicCurve_Pic0_sum_galois_smul_eq_zero_of_subsingleton
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve.Pic0

/-- An order-five automorphism over a degree-five subfield with trivial
Picard group has zero trace on the covering curve's degree-zero classes. -/
theorem _root_.solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F₀ F : IntermediateField K L) (hle : F₀ ≤ F)
    [HasPrincipalDivisors K F] [Subsingleton (Pic0 K F₀)]
    (g : F ≃ₐ[K] F) (horder : orderOf g = 5)
    (hdegree : F₀.relfinrank F = 5)
    (hfix : ∀ a : F₀, g ⟨a.val, hle a.property⟩ = ⟨a.val, hle a.property⟩)
    (x : Pic0 K F) :
    ∑ i : Fin 5, SemilinearAut.ofAlgAut (g ^ i.val) • x = 0 := by
  classical
  let a : Algebra F₀ F := inferInstanceAs (Algebra F₀ ↥(IntermediateField.extendScalars hle))
  let : Module F₀ F := @Algebra.toModule F₀ F _ _ a
  let : IsScalarTower K F₀ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hdim : Module.finrank F₀ F = 5 :=
    (IntermediateField.relfinrank_eq_finrank_of_le hle).symm.trans hdegree
  let : FiniteDimensional F₀ F := FiniteDimensional.of_finrank_pos (by rw [hdim]; decide)
  let s : F ≃ₐ[F₀] F := { g.toRingEquiv with commutes' := hfix }
  have hs : orderOf s = 5 := by
    have hinj : Function.Injective (AlgEquiv.restrictScalarsHom K :
        (F ≃ₐ[F₀] F) →* (F ≃ₐ[K] F)) := AlgEquiv.restrictScalars_injective K
    rw [← orderOf_injective (AlgEquiv.restrictScalarsHom K) hinj]
    exact horder
  obtain ⟨hgalois,e,he⟩ := AlgEquiv.exists_fin_five_equiv_of_orderOf_eq_finrank s hs hdim
  let : IsGalois F₀ F := hgalois
  have htrace := sum_galois_smul_eq_zero_of_subsingleton (K := K) (F := F₀) (E := F) x
  rw [← e.sum_comp] at htrace
  have hr (i : Fin 5) : (e i).restrictScalars K = g ^ i.val := by
    rw [he]
    change (AlgEquiv.restrictScalarsHom K) (s ^ i.val) = _
    rw [map_pow]
    rfl
  simpa only [hr] using htrace

end AlgebraicCurve.Pic0
