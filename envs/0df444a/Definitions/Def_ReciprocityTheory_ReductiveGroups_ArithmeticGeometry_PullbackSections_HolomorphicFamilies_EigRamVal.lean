-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:55:54.761326+00:00
-- url     : https://prove2.me/theorems/50ec5fd3-ea24-41fa-8578-8bda7abeae6a
-- title:
--   Eig Ram Val
-- statement:
--   Definitions and structural lemmas for Eig Ram Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamVal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Formalism.L2.Pj
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]
theorem vV_alg_nonneg (v : V) : 0 ≤ vV V (algebraMap V k v) := by
  have hle : valV V (K' := k) (algebraMap V k v) ≤ 1 := by
    unfold valV
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ v
  unfold vV
  by_cases h0 : valV V (K' := k) (algebraMap V k v) = 0
  · rw [h0, WithZero.log_zero]; simp
  · have := (WithZero.log_le_log h0 one_ne_zero).2 hle
    rw [WithZero.log_one] at this
    linarith
theorem int_mem_range (ψ : E →+* k) (x : 𝓞 E) : ψ (x : E) ∈ (algebraMap V k).range := by
  have h1 : IsIntegral ℤ (ψ (x : E)) := (RingOfIntegers.isIntegral_coe x).map ψ.toIntAlgHom
  have h2 : IsIntegral V (ψ (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩
theorem w_nonneg (ψ : E →+* k) (x : 𝓞 E) : 0 ≤ vV V (ψ (x : E)) := by
  obtain ⟨y, hy⟩ := int_mem_range (V := V) ψ x
  rw [← hy]
  exact vV_alg_nonneg y
def primeOf (ψ : E →+* k) (hψ : Function.Injective ψ) : Ideal (𝓞 E) where
  carrier := {x | 0 < vV V (ψ (x : E)) ∨ x = 0}
  add_mem' := by
    intro a b ha hb
    change 0 < vV V (ψ (a : E)) ∨ a = 0 at ha
    change 0 < vV V (ψ (b : E)) ∨ b = 0 at hb
    change 0 < vV V (ψ ((a + b : 𝓞 E) : E)) ∨ a + b = 0
    have key : ∀ z : k, z ≠ 0 → (0 < vV V z ↔ valV V (K' := k) z < 1) := by
      intro z hz
      have hz' : valV V (K' := k) z ≠ 0 := (valV V (K' := k)).ne_zero_iff.mpr hz
      unfold vV
      constructor
      · intro h
        apply not_le.mp
        intro h1
        have h2 := (WithZero.log_le_log one_ne_zero hz').mpr h1
        rw [WithZero.log_one] at h2
        linarith
      · intro h
        by_contra hc
        have hc' := not_lt.mp hc
        have h2 : WithZero.log (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.log (valV V (K' := k) z) := by
          rw [WithZero.log_one]
          linarith
        exact absurd ((WithZero.log_le_log one_ne_zero hz').mp h2) (not_le.mpr h)
    have cz : ∀ z : 𝓞 E, z ≠ 0 → ψ (z : E) ≠ 0 := fun z hz => (map_ne_zero ψ).mpr (by exact_mod_cast hz)
    by_cases hab : a + b = 0
    · exact Or.inr hab
    left
    by_cases ha0 : a = 0
    · subst ha0
      rw [zero_add] at hab ⊢
      exact hb.resolve_right hab
    by_cases hb0 : b = 0
    · subst hb0
      rw [add_zero] at hab ⊢
      exact ha.resolve_right hab
    have ha' := ha.resolve_right ha0
    have hb' := hb.resolve_right hb0
    rw [key _ (cz _ hab)]
    have hsum : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := by simp
    rw [hsum, map_add]
    calc valV V (K' := k) (ψ (a : E) + ψ (b : E))
        ≤ max (valV V (K' := k) (ψ (a : E))) (valV V (K' := k) (ψ (b : E))) := (valV V (K' := k)).map_add _ _
      _ < 1 := max_lt ((key _ (cz a ha0)).mp ha') ((key _ (cz b hb0)).mp hb')
  zero_mem' := Or.inr rfl
  smul_mem' := by
    intro c x hx
    change 0 < vV V (ψ (x : E)) ∨ x = 0 at hx
    change 0 < vV V (ψ ((c • x : 𝓞 E) : E)) ∨ c • x = 0
    rw [smul_eq_mul]
    by_cases hcx : c * x = 0
    · exact Or.inr hcx
    left
    have hc : c ≠ 0 := left_ne_zero_of_mul hcx
    have hx0 : x ≠ 0 := right_ne_zero_of_mul hcx
    have hxv : 0 < vV V (ψ (x : E)) := hx.resolve_right hx0
    have hcE : ψ (c : E) ≠ 0 := (map_ne_zero ψ).mpr (by exact_mod_cast hc)
    have hxE : ψ (x : E) ≠ 0 := (map_ne_zero ψ).mpr (by exact_mod_cast hx0)
    have hmul : ((c * x : 𝓞 E) : E) = (c : E) * (x : E) := by simp
    have hcv := w_nonneg (V := V) ψ c
    rw [hmul, map_mul]
    unfold vV at hcv hxv ⊢
    rw [map_mul, WithZero.log_mul ((valV V (K' := k)).ne_zero_iff.mpr hcE)
      ((valV V (K' := k)).ne_zero_iff.mpr hxE)]
    linarith
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam


