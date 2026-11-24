-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
-- name    : Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:07:00.652235+00:00
-- url     : https://prove2.me/theorems/b2c7a49c-af95-4a6b-8f87-a6921f5666d8
-- title:
--   Tuples P
-- statement:
--   Definitions and structural lemmas for Tuples P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Theorems.Thm_Formalism_UG_P_afsplit_eps_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
namespace Formalism.L2.DIV
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E]
end Gen
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Main
section A2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
end A2
section C
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
def c_lat (x : (AfE F E)ˣ) : Submodule (𝓞 E) E where
  carrier := {e | ((x⁻¹ : (AfE F E)ˣ) : AfE F E) * ιE e ∈ RInt F E}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add, mul_add] at *
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_def, map_mul, mul_left_comm]
    exact mul_mem (Formalism.UG.CS.incl_int c) ha
def integralAdeleSpan (N : Submodule (𝓞 E) E) : Submodule (RInt F E) (AfE F E) :=
  Submodule.span (RInt F E) (ιE '' (N : Set E))
end C
section B
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def bEps (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : RInt F E :=
  ⟨afsplitEps E v, afsplit_eps_int v⟩
end B
section B2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end B2
section B3
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def bUnder (F : Type) [Field F] [NumberField F] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 F) :=
  ⟨P.asIdeal.under (𝓞 F), have := P.isPrime; inferInstance, Ideal.under_ne_bot (𝓞 F) P.ne_bot⟩
variable {L : Type} [Field L]
end B3
section B4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
theorem under_eq_of_le_lemma {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)}
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal) : P.asIdeal.under (𝓞 F) = v.asIdeal := by
  have h1 : v.asIdeal ≤ P.asIdeal.under (𝓞 F) := Ideal.map_le_iff_le_comap.mp h
  exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) h1).symm
theorem b_under_of_split (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    P.asIdeal.under (𝓞 F) = v.asIdeal ∧ P'.asIdeal.under (𝓞 F) = v.asIdeal := by
  have h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal := by
    rw [h]
    first
    | exact Ideal.mul_le_right
    | exact le_trans Ideal.mul_le_inf inf_le_left
    | exact Ideal.mul_le.mpr (fun r hr s _ => Ideal.mul_mem_right _ _ hr)
  have h2 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P'.asIdeal := by
    rw [h]
    first
    | exact Ideal.mul_le_left
    | exact le_trans Ideal.mul_le_inf inf_le_right
    | exact Ideal.mul_le.mpr (fun r _ s hs => Ideal.mul_mem_left _ _ hs)
  exact ⟨under_eq_of_le_lemma h1, under_eq_of_le_lemma h2⟩
end B4
def TpExU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)), P.asIdeal.under (𝓞 F) = v.asIdeal →
    ∀ a : (𝓞 E ⧸ P.asIdeal)ˣ, ∃ (u : (RInt F E)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a ∧
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v ∧
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)
def TpWild : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (u : (RInt F E)ˣ),
    Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
    (∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)) →
    Units.map (RInt F E).subtype.toMonoidHom u ∈ wildAt E v
def TpApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (s : RInt F E), ∃ b : 𝓞 E, s - toRInt F E b ∈ P.asIdeal.map (toRInt F E)
def TpComap : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), toRInt F E c ∈ P.asIdeal.map (toRInt F E) → c ∈ P.asIdeal
def TpOff : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.under (𝓞 F) ≠ v.asIdeal →
    ∀ u : (RInt F E)ˣ, Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
      (u : RInt F E) - 1 ∈ P.asIdeal.map (toRInt F E)
section D1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem d_under {v : HeightOneSpectrum (𝓞 F)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    P.asIdeal.under (𝓞 F) = v.asIdeal := by
  exact (b_under_of_split v P P' hv).1
def d_resMap (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : P.asIdeal.under (𝓞 F) = v.asIdeal) : (𝓞 F ⧸ v.asIdeal) →+* (𝓞 E ⧸ P.asIdeal) :=
  Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 E)) (le_of_eq h.symm)
end D1
section D2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
set_option quotPrecheck false in
local notation "uIn" => Units.map (RInt F E).subtype.toMonoidHom
end D2
end Formalism.L2.DIV
end


