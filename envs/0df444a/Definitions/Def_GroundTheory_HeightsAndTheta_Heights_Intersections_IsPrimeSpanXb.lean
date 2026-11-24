-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsPrimeSpanXb
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IsPrimeSpanXb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:42.599188+00:00
-- url     : https://prove2.me/theorems/3c138836-0f56-495b-9434-c7b068f560be
-- title:
--   Is Prime Span Xb
-- statement:
--   Definitions and structural lemmas for Is Prime Span Xb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsPrimeSpanXb.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
def GenericPointExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')),
    W'.IsPrime → Nonempty (GenFibre v W')
section Inhabitants
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem imageZ_id (W : Ideal (MRing ι)) : imageZ (ι := ι) (ι' := ι) id W = W := by
  ext f
  simp [imageZ, rename_id]
def genFibreIdOf (W : Ideal (MRing ι)) [W.IsPrime] : GenFibre (ι := ι) (ι' := ι) id W where
  Φ := FnField W
  Φ' := FnField W
  x := genPt W
  x' := genPt W
  ker_x := by
    rw [imageZ_id]
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ W) c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨f, g, ?_, ?_⟩
    · rw [aeval_genPt]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [aeval_genPt, aeval_genPt]
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  compat _ := rfl
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


