-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:05:11.292982+00:00
-- url     : https://prove2.me/theorems/11748717-99c0-45c1-8711-ef28424af967
-- title:
--   Jet Point Add Sq Zero Eq Prod Mul Tangent
-- statement:
--   Definitions and structural lemmas for Jet Point Add Sq Zero Eq Prod Mul Tangent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetPointAddSqZeroEqProdMulTangent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstJetEqProdTangent
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
open SqZero
section Pairs
variable (R : Type) [CommRing R] {A : Type} [CommRing A] [Algebra R A]
def congrPairs (J : Ideal A) : Subalgebra R (A × A) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R A A))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R A A))
variable {R}
theorem mem_congrPairs {J : Ideal A} {b : A × A} : b ∈ congrPairs R J ↔ b.2 - b.1 ∈ J :=
  Ideal.Quotient.eq
theorem mul_eq_aug_mul (aug : A →ₐ[R] R) {J : Ideal A} (hJ : J * RingHom.ker aug = ⊥) {δ : A}
    (hδ : δ ∈ J) (a : A) : δ * (a - algebraMap R A (aug a)) = 0 := by
  have : δ * (a - algebraMap R A (aug a)) ∈ J * RingHom.ker aug :=
    Ideal.mul_mem_mul hδ (by simp [RingHom.mem_ker])
  rwa [hJ] at this
def pairDiff (aug : A →ₐ[R] R) {J : Ideal A} (hJ : J * RingHom.ker aug = ⊥) :
    congrPairs R J →ₐ[R] A where
  toFun b := algebraMap R A (aug b.1.1) + (b.1.2 - b.1.1)
  map_one' := by simp
  map_mul' b c := by
    have hb := mem_congrPairs.1 b.2
    have hc := mem_congrPairs.1 c.2
    have h₁ := mul_eq_aug_mul aug hJ hb c.1.1
    have h₂ := mul_eq_aug_mul aug hJ hc b.1.1
    simp only [MulMemClass.coe_mul, Prod.fst_mul, Prod.snd_mul, map_mul]
    linear_combination h₁ + h₂
  map_zero' := by simp
  map_add' b c := by
    simp only [AddMemClass.coe_add, Prod.fst_add, Prod.snd_add, map_add]
    ring
  commutes' r := by simp
end Pairs
end GlobalTheory


