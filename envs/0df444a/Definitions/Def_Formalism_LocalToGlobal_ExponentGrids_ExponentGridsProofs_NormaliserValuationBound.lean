-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound
-- name    : Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:26.654747+00:00
-- url     : https://prove2.me/theorems/dd1aba43-a1be-4375-8a36-98bd40f877c0
-- title:
--   Normaliser Valuation Bound
-- statement:
--   Definitions and structural lemmas for Normaliser Valuation Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ExponentGrids/ExponentGridsProofs/NormaliserValuationBound.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_SecondComplementColumnExponents
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_TranslateCocycles_TranslateCocycleProofs_TranslateScale
import Definitions.Def_Formalism_TranslateCocycles_TranslateCocycleProofs_NetGLMapSurjective
import Definitions.Def_Formalism_TranslateCocycles_TranslateCocycleProofs_HcBlockSumBounds
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl lw PlOver IsConjAt)
open Formalism.CG (HCdeg HCDplus HCDminus)
noncomputable section
namespace Formalism.AtG
namespace ValuationJets
open Formalism.DivisionValues.ValuationRepresentative Formalism.DivisionValues.PlaceSumConjugation
variable {K : Type} [Field K] [NumberField K] [StarRing K]
theorem val_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    w.valuation K (x : K) = WithZero.exp (-(vw w (x : K))) := by
  have h1 : (x : K) = algebraMap (𝓞 K) K x := rfl
  rw [h1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hx]
  congr 1
  rw [neg_inj]
  symm
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w (by simpa using hx)]
theorem val_eq (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0) :
    w.valuation K a = WithZero.exp (-(vw w a)) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hx0 : algebraMap (𝓞 K) K x ≠ 0 := (div_ne_zero_iff.mp ha).1
  have hy0 : algebraMap (𝓞 K) K y ≠ 0 := (div_ne_zero_iff.mp ha).2
  have hx : x ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  have hy1 : y ≠ 0 := fun h => hy0 (by rw [h, map_zero])
  have vx := val_int w x hx
  have vy := val_int w y hy1
  rw [show ((x : K)) = algebraMap (𝓞 K) K x from rfl] at vx
  rw [show ((y : K)) = algebraMap (𝓞 K) K y from rfl] at vy
  have hmul : vw w (algebraMap (𝓞 K) K x) =
      vw w (algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K y) + vw w (algebraMap (𝓞 K) K y) := by
    rw [← vw_mul w _ _ ha hy0, div_mul_cancel₀ _ hy0]
  rw [map_div₀, vx, vy, ← WithZero.exp_sub]
  congr 1
  linarith
theorem vw_add (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (vw w a) (vw w b) ≤ vw w (a + b) := by
  have h1 := (w.valuation K).map_add a b
  rw [val_eq w a ha, val_eq w b hb, val_eq w _ hab] at h1
  rcases le_max_iff.mp h1 with h | h
  · have h2 := WithZero.exp_le_exp.mp h
    exact le_trans (min_le_left _ _) (by linarith)
  · have h2 := WithZero.exp_le_exp.mp h
    exact le_trans (min_le_right _ _) (by linarith)
open Classical in

def fQ (w : HeightOneSpectrum (𝓞 K)) (e : ℚ) (a : K) : WithTop ℚ :=
  if a = 0 then ⊤ else (((vw w a : ℚ) / e : ℚ) : WithTop ℚ)
theorem fQ_ne (w : HeightOneSpectrum (𝓞 K)) (e : ℚ) (a : K) (ha : a ≠ 0) :
    fQ w e a = (((vw w a : ℚ) / e : ℚ) : WithTop ℚ) := by
  unfold fQ
  exact if_neg ha
theorem fQ_zero (w : HeightOneSpectrum (𝓞 K)) (e : ℚ) : fQ w e (0 : K) = ⊤ := by
  unfold fQ
  exact if_pos rfl
def valQ (w : HeightOneSpectrum (𝓞 K)) (e : ℚ) (he : 0 < e) : AddValuation K (WithTop ℚ) :=
  AddValuation.of (fQ w e) (fQ_zero w e)
    (by rw [fQ_ne w e 1 one_ne_zero, vw_one]; simp)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      by_cases hxy : x + y = 0
      · rw [hxy]; simp [fQ]
      rw [fQ_ne w e x hx, fQ_ne w e y hy, fQ_ne w e _ hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
      have h := vw_add w x y hx hy hxy
      rcases min_le_iff.mp h with h | h
      · refine le_trans (min_le_left _ _) ?_
        exact div_le_div_of_nonneg_right (by exact_mod_cast h) he.le
      · refine le_trans (min_le_right _ _) ?_
        exact div_le_div_of_nonneg_right (by exact_mod_cast h) he.le)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp [fQ]
      by_cases hy : y = 0
      · subst hy; simp [fQ]
      rw [fQ_ne w e x hx, fQ_ne w e y hy, fQ_ne w e _ (mul_ne_zero hx hy), vw_mul w x y hx hy,
        ← WithTop.coe_add]
      congr 1
      push_cast
      ring)
end ValuationJets
open ValuationJets Formalism.DivisionValues.ValuationRepresentative Formalism.DivisionValues.PlaceSumConjugation
end Formalism.AtG


