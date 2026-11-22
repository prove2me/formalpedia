-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:05.167962+00:00
-- url     : https://prove2.me/theorems/289949bb-e484-48b6-aa95-d1c200142424
-- title:
--   HCFFrom Recip A
-- statement:
--   Definitions and structural lemmas for HCFFrom Recip A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors
namespace ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
theorem comp_mul (a b : Ideles K) (v : HeightOneSpectrum (𝓞 K)) :
    ((a * b : Ideles K) : AdeleRing (𝓞 K) K).2 v = (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v := rfl
theorem comp_one (v : HeightOneSpectrum (𝓞 K)) : ((1 : Ideles K) : AdeleRing (𝓞 K) K).2 v = 1 := rfl
theorem comp_mul_inv (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) :
    (a : AdeleRing (𝓞 K) K).2 v * (a⁻¹ : Ideles K).val.2 v = 1 := by
  rw [← comp_mul K a a⁻¹ v, mul_inv_cancel, comp_one]
theorem comp_ne_zero (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) : (a : AdeleRing (𝓞 K) K).2 v ≠ 0 := by
  intro h
  have := comp_mul_inv K a v
  rw [h, zero_mul] at this
  exact zero_ne_one this
theorem valued_comp_ne_zero (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((a : AdeleRing (𝓞 K) K).2 v) ≠ 0 := (Valuation.ne_zero_iff _).mpr (comp_ne_zero K a v)
theorem valued_comp_eventually (a : Ideles K) :
    ∀ᶠ v in Filter.cofinite, Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1 := by
  have h1 := ((a : AdeleRing (𝓞 K) K).2).2
  have h2 := (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2).2
  filter_upwards [h1, h2] with v hv1 hv2
  have e1 : Valued.v ((a : AdeleRing (𝓞 K) K).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hv1
  have e2 : Valued.v (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hv2
  have e3 : Valued.v ((a : AdeleRing (𝓞 K) K).2 v) * Valued.v (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v) = 1 := by
    rw [← map_mul, comp_mul_inv, map_one]
  refine le_antisymm e1 ?_
  calc (1 : _) = _ := e3.symm
    _ ≤ _ := mul_le_of_le_one_right' e2
def ordAt (v : HeightOneSpectrum (𝓞 K)) (a : Ideles K) : ℤ :=
  -WithZero.log (Valued.v ((a : AdeleRing (𝓞 K) K).2 v))
theorem ordAt_mul (v : HeightOneSpectrum (𝓞 K)) (a b : Ideles K) :
    ordAt K v (a * b) = ordAt K v a + ordAt K v b := by
  simp only [ordAt, comp_mul, map_mul,
    WithZero.log_mul (valued_comp_ne_zero K a v) (valued_comp_ne_zero K b v)]
  ring
theorem ordAt_one (v : HeightOneSpectrum (𝓞 K)) : ordAt K v 1 = 0 := by
  rw [ordAt, comp_one]
  simp
theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (a : Ideles K) :
    ordAt K v a = 0 ↔ Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1 := by
  have hne := valued_comp_ne_zero K a v
  unfold ordAt
  rw [neg_eq_zero]
  constructor
  · intro h
    rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]
theorem ordAt_eventually (a : Ideles K) : ∀ᶠ v in Filter.cofinite, ordAt K v a = 0 := by
  exact (valued_comp_eventually K a).mono fun v hv => (ordAt_eq_zero_iff K v a).mpr hv
def idealFI (a : Ideles K) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ ordAt K v a
theorem prime_ne_zero (v : HeightOneSpectrum (𝓞 K)) : (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact v.ne_bot
theorem mulSupport_finite (a : Ideles K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ ordAt K v a).Finite := by
  refine (Filter.eventually_cofinite.mp (ordAt_eventually K a)).subset ?_
  intro v hv h
  apply hv
  simp [h]
theorem idealFI_ne_zero (a : Ideles K) : idealFI K a ≠ 0 := by
  rw [idealFI, finprod_eq_prod _ (mulSupport_finite K a)]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (prime_ne_zero K v)
theorem idealFI_mul (a b : Ideles K) : idealFI K (a * b) = idealFI K a * idealFI K b := by
  simp only [idealFI, ordAt_mul, zpow_add₀ (prime_ne_zero K _)]
  exact finprod_mul_distrib (mulSupport_finite K a) (mulSupport_finite K b)
theorem idealFI_one : idealFI K 1 = 1 := by
  simp [idealFI, ordAt_one]
def idealOf : Ideles K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun a := Units.mk0 (idealFI K a) (idealFI_ne_zero K a)
  map_one' := Units.ext (idealFI_one K)
  map_mul' a b := Units.ext (idealFI_mul K a b)
def classOf : Ideles K →* ClassGroup (𝓞 K) := (ClassGroup.mk (K := K)).comp (idealOf K)
end ReciprocityTheory.Neutral.Bridge.HCFR


