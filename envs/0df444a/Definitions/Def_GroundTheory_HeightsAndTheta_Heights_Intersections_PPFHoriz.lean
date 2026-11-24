-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:20.260717+00:00
-- url     : https://prove2.me/theorems/ceee3a07-3867-4bd7-8f3f-d5b95e07caa7
-- title:
--   PPFHoriz
-- statement:
--   Definitions and structural lemmas for PPFHoriz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace PFHoriz
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
def genMap (G : GenFibre v P') : MRing ι ⧸ imageZ v P' →+* G.Φ :=
  Ideal.Quotient.lift _ (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
    (fun a ha => by rw [← G.ker_x] at ha; exact RingHom.mem_ker.mp ha)
theorem genMap_mk (G : GenFibre v P') (f : MRing ι) :
    genMap G (Ideal.Quotient.mk _ f) = aeval G.x f := rfl
theorem genMap_injective (G : GenFibre v P') : Function.Injective (genMap G) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [genMap_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← G.ker_x]
  exact RingHom.mem_ker.mpr ha
theorem isFractionRing_genMap (G : GenFibre v P') :
    @IsFractionRing (MRing ι ⧸ imageZ v P') _ G.Φ _ (genMap G).toAlgebra := by
  letI := (genMap G).toAlgebra
  haveI : FaithfulSMul (MRing ι ⧸ imageZ v P') G.Φ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (genMap_injective G)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨f, g, -, rfl⟩ := G.gen z
  exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, rfl⟩
def quotIncl (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    MRing ι ⧸ imageZ v P' →+* FractionRing (MRing ι' ⧸ W) :=
  (algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap W (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom hW.symm.le)
theorem quotIncl_injective (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    Function.Injective (quotIncl W hW) :=
  (IsFractionRing.injective (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap_injective' (H := hW.symm.le) hW.le)
def genAlg (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    G.Φ →+* FractionRing (MRing ι' ⧸ W) :=
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  IsFractionRing.lift (quotIncl_injective W hW)
theorem genAlg_alt (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P')
    (p : Σ k, ι k) :
    genAlg G W hW (G.x p) =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X (v p))) := by
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  have hx : G.x p = algebraMap (MRing ι ⧸ imageZ v P') G.Φ (Ideal.Quotient.mk _ (X p)) := by
    show G.x p = genMap G (Ideal.Quotient.mk _ (X p))
    rw [genMap_mk, aeval_X]
  rw [hx]
  exact (IsFractionRing.lift_algebraMap (quotIncl_injective W hW) _).trans (by
    simp [quotIncl, Ideal.quotientMap_mk])
def xW (W : Ideal (MRing ι')) [W.IsPrime] (q : Σ k', ι' k') : FractionRing (MRing ι' ⧸ W) :=
  algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X q))
theorem aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] (f : MRing ι') :
    aeval (R := ℤ) (xW W) f =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, eq_intCast (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) a]
    exact (eq_intCast (((algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
      (Ideal.Quotient.mk W)).comp C) a).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, xW]
theorem ker_aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] :
    RingHom.ker (aeval (R := ℤ) (xW W)) = W := by
  ext f
  rw [RingHom.mem_ker, aeval_xW, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]
def genFibreOf (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    GenFibre v W where
  Φ := G.Φ
  Φ' := FractionRing (MRing ι' ⧸ W)
  alg := (genAlg G W hW).toAlgebra
  x := G.x
  x' := xW W
  ker_x := by rw [hW]; exact G.ker_x
  gen := G.gen
  genericFibre_ker_target := by
    refine Eq.trans ?_ (ker_aeval_xW W)
    ext f
    simp only [RingHom.mem_ker, aeval_def, algebraMap_int_eq]
    rw [RingHom.ext_int (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) (Int.castRingHom _)]
  compat p := (genAlg_alt G W hW p).symm
variable {W : Ideal (MRing ι')} [W.IsPrime] (hW : imageZ v W = imageZ v P')
end PFHoriz
end
end GroundTheory.Heights₂.Heights.Inter


