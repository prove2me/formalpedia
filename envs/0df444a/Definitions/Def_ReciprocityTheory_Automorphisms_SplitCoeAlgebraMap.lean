-- Prove2me | Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
-- name    : ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:44.686411+00:00
-- url     : https://prove2.me/theorems/2c5a3658-53c9-4c09-8fc1-be0ba2063bff
-- title:
--   Split Coe Algebra Map
-- statement:
--   Definitions and structural lemmas for Split Coe Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Automorphisms/SplitCoeAlgebraMap.lean

import Definitions.Def_ReciprocityTheory_Automorphisms_Unitary
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.Aut
open NumberField IsDedekindDomain
variable {L : Type*} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => maximalRealSubfield L
theorem SplitPlace.split_le_one (s : SplitPlace L) (x : 𝓞 L) : Valued.v (s.i (x : L)) ≤ 1 := by
  have hx : IsIntegral ℤ (x : L) := x.isIntegral_coe
  have h1 : IsIntegral ℤ (s.i (x : L)) := by
    first
      | exact hx.map (s.i.restrictScalars ℤ)
      | convert hx.map (s.i : L →+* s.v.adicCompletion L⁺).toIntAlgHom
  have h2 : IsIntegral (Valued.v : Valuation (s.v.adicCompletion L⁺) _).integer (s.i (x : L)) :=
    h1.tower_top
  exact (Valuation.mem_integer_iff _ _).mp ((Valuation.integer.integers _).mem_of_integral h2)
theorem split_coe_algebraMap (a : 𝓞 L⁺) :
    ((algebraMap (𝓞 L⁺) (𝓞 L) a : 𝓞 L) : L) = algebraMap L⁺ L (a : L⁺) := rfl
theorem SplitPlace.split_val_alg (s : SplitPlace L) (a : 𝓞 L⁺) :
    Valued.v (s.i ((algebraMap (𝓞 L⁺) (𝓞 L) a : 𝓞 L) : L)) = s.v.valuation L⁺ (a : L⁺) := by
  rw [split_coe_algebraMap, s.i.commutes]
  first
    | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' s.v (a : L⁺)
    | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
def SplitPlace.ideal (s : SplitPlace L) : Ideal (𝓞 L) where
  carrier := {x | Valued.v (s.i (x : L)) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, RingOfIntegers.coe_eq_algebraMap, map_add] at *
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  zero_mem' := by
    simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul] at *
    calc Valued.v (s.i (algebraMap (𝓞 L) L c)) * Valued.v (s.i (algebraMap (𝓞 L) L x))
          ≤ 1 * Valued.v (s.i (algebraMap (𝓞 L) L x)) := by
          gcongr; exact s.split_le_one c
      _ < 1 := by rwa [one_mul]
theorem SplitPlace.split_mem_ideal (s : SplitPlace L) (x : 𝓞 L) :
    x ∈ s.ideal ↔ Valued.v (s.i (x : L)) < 1 := Iff.rfl
theorem SplitPlace.ideal_isPrime (s : SplitPlace L) : s.ideal.IsPrime := by
  rw [Ideal.isPrime_iff]
  constructor
  · rw [Ne, Ideal.eq_top_iff_one, s.split_mem_ideal]
    simp
  · intro x y hxy
    rw [s.split_mem_ideal, s.split_mem_ideal]
    rw [s.split_mem_ideal] at hxy
    by_contra h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at hxy h1 h2
    exact not_lt.mpr (one_le_mul h1 h2) hxy
theorem SplitPlace.split_alg_mem (s : SplitPlace L) (a : 𝓞 L⁺) :
    algebraMap (𝓞 L⁺) (𝓞 L) a ∈ s.ideal ↔ a ∈ s.v.asIdeal := by
  rw [s.split_mem_ideal, s.split_val_alg, RingOfIntegers.coe_eq_algebraMap]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem s.v a
theorem SplitPlace.ideal_ne_bot (s : SplitPlace L) : s.ideal ≠ ⊥ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.v.ne_bot
  intro h
  have hm : algebraMap (𝓞 L⁺) (𝓞 L) a ∈ s.ideal := (s.split_alg_mem a).mpr ha
  rw [h, Ideal.mem_bot] at hm
  apply ha0
  have h2 : ((algebraMap (𝓞 L⁺) (𝓞 L) a : 𝓞 L) : L) = 0 := by rw [hm]; simp
  rw [split_coe_algebraMap] at h2
  have h3 : ((a : 𝓞 L⁺) : L⁺) = 0 := (map_eq_zero_iff _ (algebraMap L⁺ L).injective).mp h2
  first
    | exact RingOfIntegers.ext h3
    | exact Subtype.ext h3
    | exact_mod_cast h3
def SplitPlace.w (s : SplitPlace L) : HeightOneSpectrum (𝓞 L) :=
  ⟨s.ideal, s.ideal_isPrime, s.ideal_ne_bot⟩
def SplitPlace.q (s : SplitPlace L) : ℕ := Nat.card (𝓞 L⁺ ⧸ s.v.asIdeal)
def SplitPlace.Above (s : SplitPlace L) (l : ℕ) : Prop := ((l : ℕ) : 𝓞 L⁺) ∈ s.v.asIdeal
variable (L) in

structure LPlaces (l : ℕ) where
  ι : Type
  fin : Fintype ι
  s : ι → SplitPlace L
  inj : ∀ a b, (s a).v = (s b).v → a = b
  above : ∀ a, (s a).Above l
  cover : ∀ v : HeightOneSpectrum (𝓞 L⁺), ((l : ℕ) : 𝓞 L⁺) ∈ v.asIdeal → ∃ a, (s a).v = v
  ϖ : ∀ a, (s a).v.adicCompletion L⁺
  unif : ∀ a, Valued.v (ϖ a) = WithZero.exp (-1 : ℤ)
end ReciprocityTheory.Aut


