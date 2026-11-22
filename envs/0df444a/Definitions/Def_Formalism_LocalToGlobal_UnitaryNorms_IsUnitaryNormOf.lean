-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
-- name    : Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:39:21.251307+00:00
-- url     : https://prove2.me/theorems/8fe2094f-646c-4bf7-b315-5aaf90ba3ace
-- title:
--   Is Unitary Norm Of
-- statement:
--   Definitions and structural lemmas for Is Unitary Norm Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR nonZeroDivisors
namespace Formalism.L2.Host
variable (L : Type) [Field L] [NumberField L]
def hcharSub : Subgroup (Ideles L →* ℂˣ) where
  carrier := {χ | Continuous χ ∧ ∀ k : Lˣ, χ (diagUnits L k) = 1}
  one_mem' := ⟨continuous_const, fun _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, fun k => by
    rw [MonoidHom.mul_apply, ha.2 k, hb.2 k, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨ha.1.inv, fun k => by rw [MonoidHom.inv_apply, ha.2 k, inv_one]⟩
abbrev HChar : Type := ↥(hcharSub L)
variable {L}
def atFin (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* (v.adicCompletion L)ˣ :=
  Units.map (algebraMap L (v.adicCompletion L)).toMonoidHom
def atInf (w : InfinitePlace L) : Lˣ →* (w.Completion)ˣ :=
  Units.map (algebraMap L w.Completion).toMonoidHom
def IsUnitAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = 1
def IsUnifAt (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) : Prop :=
  Valued.v (x : v.adicCompletion L) = WithZero.exp (-1 : ℤ)
def ordF (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : ℤ := -WithZero.log (v.valuation L (k : L))
def infDiag : Lˣ →* Ideles L := ∏ w : InfinitePlace L, (infIdele L w).comp (atInf w)
theorem exists_unif (v : HeightOneSpectrum (𝓞 L)) : ∃ k : Lˣ, IsUnifAt v (atFin v k) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨Units.mk0 π h0, ?_⟩
  show Valued.v ((algebraMap L (v.adicCompletion L)) π) = _
  rw [← hπ]
  exact v.valuedAdicCompletion_eq_valuation' π
def unif (v : HeightOneSpectrum (𝓞 L)) : Lˣ := Classical.choose (exists_unif v)
namespace HChar
variable (χ : HChar L)
def loc (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* ℂˣ := χ.1.comp (localIdele L v)
def locInf (w : InfinitePlace L) : (w.Completion)ˣ →* ℂˣ := χ.1.comp (infIdele L w)
def locK (v : HeightOneSpectrum (𝓞 L)) : Lˣ →* ℂˣ := (χ.loc v).comp (atFin v)
def inf : Lˣ →* ℂˣ := χ.1.comp infDiag
def LevelLe (v : HeightOneSpectrum (𝓞 L)) (n : ℕ) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x →
    Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ.loc v x = 1
def UnrAt (v : HeightOneSpectrum (𝓞 L)) : Prop := ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ.loc v x = 1
def TameAt (v : HeightOneSpectrum (𝓞 L)) : Prop := χ.LevelLe v 1
def IsCond (𝔣 : Ideal (𝓞 L)) : Prop :=
  𝔣 ≠ ⊥ ∧ ∀ (v : HeightOneSpectrum (𝓞 L)) (n : ℕ), χ.LevelLe v n ↔ ¬ v.asIdeal ^ (n + 1) ∣ 𝔣
def val (v : HeightOneSpectrum (𝓞 L)) : ℂˣ := χ.locK v (unif v)
def onId (I : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 L), χ.val v ^ FractionalIdeal.count L v I
def valTw (s : ℝ) (v : HeightOneSpectrum (𝓞 L)) : ℂ :=
  (χ.val v : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))
def IsUnitary : Prop := ∀ x : Ideles L, ‖((χ.1 x : ℂˣ) : ℂ)‖ = 1
def OrderDvd (n : ℕ) : Prop := χ ^ n = 1
def HasInf {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) : Prop :=
  ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i
def HasInfQ {I : Type} [Fintype I] (φ : I → L →+* ℂ) (a : I → ℚ) : Prop :=
  ∃ n : I → ℤ, (∀ i, (n i : ℚ) = 2 * a i) ∧ χ.HasInf φ n
def IsAlg (n : (L →+* ℂ) → ℤ) : Prop :=
  ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ n φ
def IsAbsPow (s : ℝ) : Prop :=
  (∀ v, χ.UnrAt v) ∧ (∀ v, ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ))) ∧
    ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ)
def IsUnitaryNormOf (χ' : HChar L) (s : ℝ) : Prop :=
  χ.IsUnitary ∧ ∃ ν : HChar L, ν.IsAbsPow s ∧ χ' = χ * ν
def ValuesIn (s : ℝ) {C : Type} [Field C] (e : C →+* ℂ) : Prop :=
  ∀ v, χ.UnrAt v → ∃ y : C, e y = χ.valTw s v
def ProductRule : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 L)), (∀ v, v ∉ S → χ.UnrAt v) → ∀ k : Lˣ,
    χ.inf k * (∏ v ∈ S, χ.locK v k) * (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1
@[simp] theorem loc_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 L)) (x) : (χ * χ').loc v x = χ.loc v x * χ'.loc v x := rfl
@[simp] theorem loc_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (x) : (χ⁻¹).loc v x = (χ.loc v x)⁻¹ := rfl
@[simp] theorem loc_one (v : HeightOneSpectrum (𝓞 L)) (x) : (1 : HChar L).loc v x = 1 := rfl
@[simp] theorem locInf_mul (χ χ' : HChar L) (w : InfinitePlace L) (x) : (χ * χ').locInf w x = χ.locInf w x * χ'.locInf w x := rfl
@[simp] theorem locInf_inv (χ : HChar L) (w : InfinitePlace L) (x) : (χ⁻¹).locInf w x = (χ.locInf w x)⁻¹ := rfl
@[simp] theorem val_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ * χ').val v = χ.val v * χ'.val v := rfl
@[simp] theorem val_inv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : (χ⁻¹).val v = (χ.val v)⁻¹ := rfl
@[simp] theorem inf_mul (χ χ' : HChar L) (k : Lˣ) : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
@[simp] theorem inf_inv (χ : HChar L) (k : Lˣ) : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
def bar : HChar L :=
  ⟨(Units.map (starRingEnd ℂ).toMonoidHom).comp χ.1,
    (Continuous.units_map _ Complex.continuous_conj).comp χ.2.1, fun k => by
      rw [MonoidHom.comp_apply, χ.2.2 k, map_one]⟩
end HChar
abbrev AlgHChar (L : Type) [Field L] [NumberField L] : Type := {χ : HChar L // ∃ n, χ.IsAlg n}
section Res
variable (F : Type) [Field F] [NumberField F] [Algebra F L]
theorem finite_aboveF (v : HeightOneSpectrum (𝓞 F)) :
    {P : HeightOneSpectrum (𝓞 L) | P.under (𝓞 F) = v}.Finite := by
  have hne : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) v.asIdeal ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne,
      Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))]
    exact v.ne_bot
  refine (Ideal.finite_factors hne).subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq] at hP ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hP,
    IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
def aboveF (v : HeightOneSpectrum (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 L)) := (finite_aboveF F v).toFinset
open Classical in

def aboveInf (w : InfinitePlace F) : Finset (InfinitePlace L) :=
  Finset.univ.filter fun w' => w'.comap (algebraMap F L) = w
def upF : Fˣ →* Lˣ := Units.map (algebraMap F L).toMonoidHom
variable {F}
def HChar.resFin (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* ℂˣ :=
  ∏ P ∈ aboveF (L := L) F v, (χ.locK P).comp (upF F)
def HChar.resInf (χ : HChar L) (w : InfinitePlace F) : Fˣ →* ℂˣ :=
  ∏ w' ∈ aboveInf (L := L) F w, ((χ.locInf w').comp (atInf w')).comp (upF F)
variable (F)
def HChar.TrivOn (χ : HChar L) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ), χ.resFin v k = 1) ∧ ∀ (w : InfinitePlace F) (k : Fˣ), χ.resInf w k = 1
def etaFin (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : ℂˣ :=
  if (aboveF (L := L) F v).card = 1 then (-1) ^ ordF v k else 1
def etaInf (w : InfinitePlace F) (k : Fˣ) : ℂˣ := if (w.embedding (k : F)).re < 0 then -1 else 1
def HChar.ResEta (χ : HChar L) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ), χ.resFin v k = etaFin (L := L) F v k) ∧
    ∀ (w : InfinitePlace F) (k : Fˣ), χ.resInf w k = etaInf F w k
end Res
end Formalism.L2.Host


