-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_Places
-- name    : GroundTheory_GlobalFields_Artin_Places
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:10:50.600268+00:00
-- url     : https://prove2.me/theorems/88afdc3e-63bf-465d-aa2c-69a64a773660
-- title:
--   Places
-- statement:
--   Definitions and structural lemmas for Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Places.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobeniusEmbed
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
import Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Artin.extendByZero_coe
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
namespace GroundTheory.Global.Artin
section Action
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
instance : MulAction Gal(L/K) (HeightOneSpectrum (𝓞 L)) where
  smul σ w := ⟨σ • w.asIdeal, Ideal.IsPrime.smul σ, fun h ↦ w.ne_bot (by
    rw [← inv_smul_smul σ w.asIdeal, h, Ideal.smul_bot])⟩
  one_smul w := HeightOneSpectrum.ext (one_smul _ w.asIdeal)
  mul_smul σ τ w := HeightOneSpectrum.ext (mul_smul σ τ w.asIdeal)
@[simp]
theorem asIdeal_smul (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).asIdeal = σ • w.asIdeal :=
  rfl
end Action
section FixedField
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
instance isGaloisGroup_fixedField : IsGaloisGroup H (fixedField H) L :=
  IsGaloisGroup.subgroup Gal(L/K) K L H
instance isGaloisGroup_ringOfIntegers_fixedField : IsGaloisGroup H (𝓞 (fixedField H)) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing H (𝓞 (fixedField H)) (𝓞 L) (fixedField H) L
end FixedField
section Finite
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))
def subfieldPlace (x : Gal(L/K)) : HeightOneSpectrum (𝓞 (fixedField H)) :=
  (x • w).under (𝓞 (fixedField H))
omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem asIdeal_subfieldPlace (x : Gal(L/K)) :
    (subfieldPlace H w x).asIdeal = (x • w.asIdeal).under (𝓞 (fixedField H)) :=
  rfl
instance liesOver_subfieldPlace (x : Gal(L/K)) :
    (x • w.asIdeal).LiesOver (subfieldPlace H w x).asIdeal :=
  ⟨rfl⟩
theorem subfieldPlace_liesOver [w.asIdeal.LiesOver v.asIdeal] (x : Gal(L/K)) :
    (subfieldPlace H w x).asIdeal.LiesOver v.asIdeal :=
  Ideal.LiesOver.tower_bot (x • w.asIdeal) _ v.asIdeal
theorem subfieldPlace_eq_iff (x y : Gal(L/K)) :
    subfieldPlace H w x = subfieldPlace H w y ↔
      DoubleCoset.mk H (MulAction.stabilizer Gal(L/K) w.asIdeal) x =
        DoubleCoset.mk H (MulAction.stabilizer Gal(L/K) w.asIdeal) y := by
  rw [DoubleCoset.eq, HeightOneSpectrum.ext_iff, asIdeal_subfieldPlace, asIdeal_subfieldPlace]
  constructor
  · intro hxy
    have : (y • w.asIdeal).LiesOver ((x • w.asIdeal).under (𝓞 (fixedField H))) := ⟨hxy⟩
    obtain ⟨h, hh⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      ((x • w.asIdeal).under (𝓞 (fixedField H))) (x • w.asIdeal) (y • w.asIdeal) H
    have hh' : (h : Gal(L/K)) • x • w.asIdeal = y • w.asIdeal := hh
    refine ⟨h, h.2, (y⁻¹ * h * x)⁻¹, Subgroup.inv_mem _ ?_, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hh', inv_smul_smul]
  · rintro ⟨h, hh, d, hd, rfl⟩
    rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 hd,
      show h • x • w.asIdeal = (⟨h, hh⟩ : H) • (x • w.asIdeal) from rfl]
    exact (Ideal.under_smul (𝓞 (fixedField H)) (x • w.asIdeal) (⟨h, hh⟩ : H)).symm
theorem exists_subfieldPlace_eq [w.asIdeal.LiesOver v.asIdeal]
    (u : HeightOneSpectrum (𝓞 (fixedField H))) [u.asIdeal.LiesOver v.asIdeal] :
    ∃ x : Gal(L/K), subfieldPlace H w x = u := by
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) u.asIdeal
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q u.asIdeal v.asIdeal
  obtain ⟨x, hx⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal Q Gal(L/K)
  refine ⟨x, HeightOneSpectrum.ext ?_⟩
  rw [asIdeal_subfieldPlace, hx, ← hQ.over]
def subfieldPlaceEquiv [w.asIdeal.LiesOver v.asIdeal] :
    DoubleCoset.Quotient (H : Set Gal(L/K)) (MulAction.stabilizer Gal(L/K) w.asIdeal) ≃
      {u : HeightOneSpectrum (𝓞 (fixedField H)) // u.asIdeal.LiesOver v.asIdeal} :=
  Equiv.ofBijective
    (Quotient.lift (fun x ↦ ⟨subfieldPlace H w x, subfieldPlace_liesOver H v w x⟩)
      (fun a b hab ↦ Subtype.ext ((subfieldPlace_eq_iff H w a b).2 (Quotient.sound hab))))
    ⟨by
      rintro ⟨a⟩ ⟨b⟩ hab
      exact (subfieldPlace_eq_iff H w a b).1 (congrArg Subtype.val hab),
    by
      rintro ⟨u, hu⟩
      obtain ⟨x, hx⟩ := exists_subfieldPlace_eq H v w u
      exact ⟨DoubleCoset.mk _ _ x, Subtype.ext hx⟩⟩
end Finite
end GroundTheory.Global.Artin


