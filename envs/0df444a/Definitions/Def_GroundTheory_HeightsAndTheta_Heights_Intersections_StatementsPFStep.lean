-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFStep
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:50.964825+00:00
-- url     : https://prove2.me/theorems/e65d9051-2a46-4659-86de-c4d4552ebebe
-- title:
--   Statements PFStep
-- statement:
--   Definitions and structural lemmas for Statements PFStep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsPFStep.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I4_isBlockMap_inl

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
def PFAt (I : AllFam) (r : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    I K' ι' P' (d + r) (Fin.append L' N) =
      (J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L
def PFStep.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ r : ℕ, PFAt I r → PFAt I (r + 1)
section Inhabitants
abbrev PointLineBlocks : Unit ⊕ Unit → Type := Sum.elim (PBlk 1) (PBlk 2)
theorem imageZ_inlV_bot :
    imageZ (inlV (ι := PBlk 1) (ι₂ := PBlk 2)) (⊥ : Ideal (MRing PointLineBlocks)) = ⊥ :=
  Ideal.comap_bot_of_injective _ (rename_injective _ isBlockMap_inl.2.1)
theorem aeval_algebraMap_X_eq {σ : Type} {Φ : Type} [CommRing Φ] [Algebra (MvPolynomial σ ℤ) Φ]
    (f : MvPolynomial σ ℤ) :
    aeval (R := ℤ) (fun p => algebraMap (MvPolynomial σ ℤ) Φ (X p)) f = algebraMap (MvPolynomial σ ℤ) Φ f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, eq_intCast (algebraMap ℤ Φ) a]
    exact (eq_intCast ((algebraMap (MvPolynomial σ ℤ) Φ).comp C) a).symm
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, hp, aeval_X]
abbrev lineAlgBase : Algebra (MRing (PBlk 1)) (FractionRing (MRing PointLineBlocks)) :=
  ((algebraMap (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks))).comp
    (rename (inlV (ι := PBlk 1) (ι₂ := PBlk 2))).toRingHom).toAlgebra
theorem lineAlgBase_injective :
    Function.Injective (@algebraMap (MRing (PBlk 1)) (FractionRing (MRing PointLineBlocks)) _ _ lineAlgBase) :=
  (IsFractionRing.injective (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks))).comp
    (rename_injective _ isBlockMap_inl.2.1)
abbrev lineAlg : Algebra (FractionRing (MRing (PBlk 1))) (FractionRing (MRing PointLineBlocks)) :=
  letI := lineAlgBase
  haveI : FaithfulSMul (MRing (PBlk 1)) (FractionRing (MRing PointLineBlocks)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr lineAlgBase_injective
  FractionRing.liftAlgebra _ _
theorem lineAlg_algebraMap (f : MRing (PBlk 1)) :
    @algebraMap _ _ _ _ lineAlg (algebraMap (MRing (PBlk 1)) (FractionRing (MRing (PBlk 1))) f) =
      algebraMap (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks))
        (rename (inlV (ι := PBlk 1) (ι₂ := PBlk 2)) f) := by
  let := lineAlgBase
  have : FaithfulSMul (MRing (PBlk 1)) (FractionRing (MRing PointLineBlocks)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr lineAlgBase_injective
  exact IsFractionRing.lift_algebraMap lineAlgBase_injective f
def genFibreLine : GenFibre (inlV (ι := PBlk 1) (ι₂ := PBlk 2)) (⊥ : Ideal (MRing PointLineBlocks)) where
  Φ := FractionRing (MRing (PBlk 1))
  Φ' := FractionRing (MRing PointLineBlocks)
  alg := lineAlg
  x p := algebraMap (MRing (PBlk 1)) (FractionRing (MRing (PBlk 1))) (X p)
  x' q := algebraMap (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks)) (X q)
  ker_x := by
    rw [imageZ_inlV_bot]
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing (PBlk 1)) (FractionRing (MRing (PBlk 1))))
      (IsFractionRing.injective _ _) using 2
    exact aeval_algebraMap_X_eq f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing (PBlk 1)) c
    refine ⟨a, b, ?_, ?_⟩
    · convert IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (K := FractionRing (MRing (PBlk 1))) hb using 2
      exact aeval_algebraMap_X_eq b
    · exact (congrArg₂ (· / ·) (aeval_algebraMap_X_eq a) (aeval_algebraMap_X_eq b)).symm
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing PointLineBlocks) (FractionRing (MRing PointLineBlocks)))
      (IsFractionRing.injective _ _) using 2
    exact aeval_algebraMap_X_eq f
  compat p := by
    rw [lineAlg_algebraMap, rename_X]
def fibreLine : HermLine PointLineBlocks := HermLine.sqMetric (Sum.elim (fun _ => 0) fun _ => 1)
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Inter


