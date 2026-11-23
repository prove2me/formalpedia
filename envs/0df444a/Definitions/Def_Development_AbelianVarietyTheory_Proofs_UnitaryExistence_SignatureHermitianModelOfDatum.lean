-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:33.142497+00:00
-- url     : https://prove2.me/theorems/4b1352fe-5652-4188-9f56-349add595aa5
-- title:
--   Signature Hermitian Model Of Datum
-- statement:
--   Definitions and structural lemmas for Signature Hermitian Model Of Datum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SignatureHermitianModelOfDatum.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HermSign
section
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
def hostType (H : Host E) : CMType E where
  carrier := {τ | τ (H.rt : E) = H.rt0}
  mem_iff_conjugate_notMem' τ := by
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
      simpa using this
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h2 : conj (τ (H.rt : E)) = -τ (H.rt : E) := by
      have h3 : conj (τ (H.rt : E)) ^ 2 = τ (H.rt : E) ^ 2 := by rw [← map_pow, h1]; simp
      refine (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left fun h => ?_
      obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h
      rw [hx] at h1
      have : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
      nlinarith [sq_nonneg x]
    have h4 : H.rt0 ≠ 0 := by
      intro h
      have := H.sqrt_neg_disc_sq
      rw [h] at this
      have h5 : (H.d : ℝ) = 0 := by simpa using this
      exact hd.ne' h5
    simp only [Set.mem_setOf_eq, ComplexEmbedding.conjugate_coe_eq, h2]
    constructor
    · intro h h'
      rw [h] at h'
      exact h4 (by linear_combination (-1 / 2 : ℂ) * h')
    · intro h
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h6 | h6
      · exact h6
      · exact absurd (by rw [h6, neg_neg]) h
end
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {r : ℕ}
  (Φ : CMType E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
noncomputable def realMap : ℝ ⊗[ℤ] D.La →ₗ[ℝ] (Φ → Fin r → ℂ) :=
  LinearMap.liftBaseChange ℝ
    ({ toFun := fun x τ i => τ.1 (φ x i)
       map_add' := fun x y => by funext τ i; simp
       map_smul' := fun n x => by funext τ i; simp } : D.La →ₗ[ℤ] (Φ → Fin r → ℂ))
noncomputable def realAct (a : 𝓞 E) : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
  (DistribSMul.toLinearMap ℤ D.La a).baseChange ℝ
end Main
end GlobalTheory.HermSign


