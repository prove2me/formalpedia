-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_QuotientMapImageZInjective
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_QuotientMapImageZInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:17.456411+00:00
-- url     : https://prove2.me/theorems/00d88053-fed1-4375-8a7a-4d31455ad90e
-- title:
--   Quotient Map Image ZInjective
-- statement:
--   Definitions and structural lemmas for Quotient Map Image ZInjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/QuotientMapImageZInjective.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsPrimeSpanXb
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
section GenPt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem quotientMap_imageZ_injective (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    Function.Injective (Ideal.quotientMap W' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom
      (le_refl (imageZ v W'))) :=
  Ideal.quotientMap_injective' le_rfl
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

instance imageZ_isPrime (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) [W'.IsPrime] :
    (imageZ v W').IsPrime :=
  Ideal.IsPrime.comap _
def genFibreOf (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) [W'.IsPrime] : GenFibre v W' :=
  letI g : MRing ι ⧸ imageZ v W' →+* FnField W' :=
    (algebraMap (MRing ι' ⧸ W') (FnField W')).comp
      (Ideal.quotientMap W' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom (le_refl (imageZ v W')))
  have hg : Function.Injective g :=
    (IsFractionRing.injective (MRing ι' ⧸ W') (FnField W')).comp (quotientMap_imageZ_injective v W')
  letI alg : Algebra (FnField (imageZ v W')) (FnField W') :=
    (IsFractionRing.lift (K := FnField (imageZ v W')) hg).toAlgebra
  { Φ := FnField (imageZ v W')
    Φ' := FnField W'
    alg := alg
    x := genPt (imageZ v W')
    x' := genPt W'
    ker_x := by
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk (imageZ v W')) f
    gen := fun c => by
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ imageZ v W') c
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨f, g, ?_, ?_⟩
      · rw [aeval_genPt]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      · rw [aeval_genPt, aeval_genPt]
    genericFibre_ker_target := by
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W') f
    compat := fun p => by
      show genPt W' (v p) = IsFractionRing.lift hg (genPt (imageZ v W') p)
      rw [genPt, genPt, IsFractionRing.lift_algebraMap]
      simp [g, Ideal.quotientMap_mk] }
end GenPt
end GroundTheory.Heights₂.Heights.Inter


