-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:56.941641+00:00
-- url     : https://prove2.me/theorems/8029e18e-46a8-4b51-993c-8aaa75a13589
-- title:
--   Map Domain Mem Of Dvd
-- statement:
--   Definitions and structural lemmas for Map Domain Mem Of Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace BlockPoly
open MvPolynomial
section Diag
variable {K σ : Type*} [Field K]
noncomputable def diag (c : σ → K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun t => C (c t) * X t
theorem diag_X (c : σ → K) (t : σ) : diag c (X t) = C (c t) * X t := by
  unfold diag
  rw [aeval_X]
noncomputable def diagEquiv {c : σ → K} (hc : ∀ t, c t ≠ 0) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (diag c) (diag fun t => (c t)⁻¹)
    (algHom_ext fun t => by
      simp only [AlgHom.comp_apply, diag_X, map_mul, algHom_C, algebraMap_eq, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (hc t), C_1, one_mul])
    (algHom_ext fun t => by
      simp only [AlgHom.comp_apply, diag_X, map_mul, algHom_C, algebraMap_eq, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc t), C_1, one_mul])
@[simp] theorem diagEquiv_apply {c : σ → K} (hc : ∀ t, c t ≠ 0) (g : MvPolynomial σ K) :
    diagEquiv hc g = diag c g := rfl
end Diag
section Blocks
variable {K : Type*} [Field K] {D N : ℕ}
def bdeg (b : Fin (D + 1)) (s : Fin (D + 1) × Fin (N + 1) →₀ ℕ) : ℕ := ∑ j, s (b, j)
def cb (b : Fin (D + 1)) (μ : K) : Fin (D + 1) × Fin (N + 1) → K :=
  fun t => if t.1 = b then μ else 1
def eT (e : Equiv.Perm (Fin (D + 1))) : Fin (D + 1) × Fin (N + 1) ≃ Fin (D + 1) × Fin (N + 1) :=
  Equiv.prodCongr e (Equiv.refl _)
noncomputable def transl (a : Fin (N + 1) → K) :
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →ₐ[K] MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
  aeval fun t => if t.1 = 0 then X t + C (a t.2) else X t
theorem transl_X (a : Fin (N + 1) → K) (t : Fin (D + 1) × Fin (N + 1)) :
    transl a (X t) = if t.1 = 0 then X t + C (a t.2) else X t := by
  unfold transl
  rw [aeval_X]
noncomputable def translEquiv (a : Fin (N + 1) → K) :
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K ≃ₐ[K] MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
  AlgEquiv.ofAlgHom (transl a) (transl (-a))
    (algHom_ext fun t => by by_cases h : t.1 = 0 <;> simp [transl_X, h])
    (algHom_ext fun t => by by_cases h : t.1 = 0 <;> simp [transl_X, h])
end Blocks
end BlockPoly


