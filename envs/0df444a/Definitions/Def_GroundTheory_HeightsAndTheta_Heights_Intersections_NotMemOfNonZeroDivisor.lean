-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:32.513135+00:00
-- url     : https://prove2.me/theorems/d26963f5-9408-4285-bb35-0c3c53c4955f
-- title:
--   Not Mem Of Non Zero Divisor
-- statement:
--   Definitions and structural lemmas for Not Mem Of Non Zero Divisor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
namespace regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
abbrev toFrac (P : Ideal (MRing ι)) : MRing ι →+* FractionRing (MRing ι ⧸ P) :=
  (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))).comp (Ideal.Quotient.mk P)
def formSub (P : Ideal (MRing ι)) : Submonoid (MRing ι ⧸ P) :=
  Submonoid.closure {y | ∃ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a ∧ v ∉ P ∧ Ideal.Quotient.mk P v = y}
omit [Fintype K] in
theorem formSub_le (P : Ideal (MRing ι)) [P.IsPrime] : formSub P ≤ nonZeroDivisors (MRing ι ⧸ P) := by
  refine Submonoid.closure_le.mpr ?_
  rintro _ ⟨v, a, -, hv, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
abbrev locForms (P : Ideal (MRing ι)) [P.IsPrime] :
    Subalgebra (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) :=
  Localization.subalgebra (FractionRing (MRing ι ⧸ P)) (formSub P) (formSub_le P)
omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem not_mem_of_nonZeroDivisor {P : Ideal (MRing ι)} [P.IsPrime] {v : MRing ι}
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)) : v ∉ P := fun h =>
  nonZeroDivisors.ne_zero hv (Ideal.Quotient.eq_zero_iff_mem.mpr h)
theorem funField_le (P : Ideal (MRing ι)) [P.IsPrime] : funField P ≤ (locForms P).toSubring := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨u, v, a, hv, -, hva, rfl⟩
  exact ⟨Ideal.Quotient.mk P u, Ideal.Quotient.mk P v,
    Submonoid.subset_closure ⟨v, a, hva, not_mem_of_nonZeroDivisor hv, rfl⟩, rfl⟩
def evalQ (P : Ideal (MRing ι)) (t : (Σ k, ι k) → ℂ) (ht : t ∈ mcPts P) : MRing ι ⧸ P →+* ℂ :=
  Ideal.Quotient.lift P ((eval t).comp (map (Int.castRingHom ℂ))) fun f hf => ht.2 f hf
omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem evalQ_mk {P : Ideal (MRing ι)} {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P) (f : MRing ι) :
    evalQ P t ht (Ideal.Quotient.mk P f) = eval t (map (Int.castRingHom ℂ) f) :=
  Ideal.Quotient.lift_mk _ _ _
theorem isUnit_evalQ {P : Ideal (MRing ι)} {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P)
    (hne : ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → v ∉ P → eval t (map (Int.castRingHom ℂ) v) ≠ 0)
    (y : formSub P) : IsUnit (evalQ P t ht y) := by
  obtain ⟨y, hy⟩ := y
  induction hy using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨v, a, hva, hvP, rfl⟩ := hx
    rw [evalQ_mk]
    exact isUnit_iff_ne_zero.mpr (hne v a hva hvP)
  | one => simp
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact hx.mul hy
def sigmaAt (P : Ideal (MRing ι)) [P.IsPrime] (t : (Σ k, ι k) → ℂ) (ht : t ∈ mcPts P)
    (hne : ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → v ∉ P → eval t (map (Int.castRingHom ℂ) v) ≠ 0) :
    funField P →+* ℂ :=
  (IsLocalization.lift (M := formSub P) (S := locForms P) (isUnit_evalQ ht hne)).comp
    (Subring.inclusion (funField_le P))
def chartHom {P : Ideal (MRing ι)} (r : (Σ k, ι k) → funField P) : MRing ι →+* funField P :=
  eval₂Hom (Int.castRingHom _) r
end regularityEmbedding_holds
end
end GroundTheory.Heights₂.Heights.Inter


