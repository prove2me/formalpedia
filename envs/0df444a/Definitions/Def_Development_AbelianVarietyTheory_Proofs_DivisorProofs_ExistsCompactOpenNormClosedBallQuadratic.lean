-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenNormClosedBallQuadratic
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenNormClosedBallQuadratic
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:11:15.124572+00:00
-- url     : https://prove2.me/theorems/369381ea-4479-4b64-8895-0e98b46c446b
-- title:
--   Exists Compact Open Norm Closed Ball Quadratic
-- statement:
--   Definitions and structural lemmas for Exists Compact Open Norm Closed Ball Quadratic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenNormClosedBallQuadratic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel
namespace GlobalTheory.NormBall
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
lemma eval_zero_quadratic_mem_maximalIdeal (t : F) (ht : valuation F t < 1) (htmem : t ∈ 𝒪[F]) :
    Polynomial.eval 0 (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) :
      Polynomial 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    zero_pow two_ne_zero, zero_add]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one]
  exact ht.ne
open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
lemma exists_sq_eq_one_sub_four_mul {t : F} (ht : valuation F t < 1) :
    ∃ w : F, (1 + 2 * w) ^ 2 = 1 - 4 * t := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  have hH : HenselianRing 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[F]) :=
    IsAdicComplete.henselianRing _ _
  have htmem : t ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 ht.le
  have hf : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) :
      Polynomial 𝒪[F]).Monic := by
    monicity!
  have h1 : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[F]))
      (Polynomial.eval 0 (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.X +
        Polynomial.C (⟨t, htmem⟩ : 𝒪[F]) : Polynomial 𝒪[F])))) := by
    simp [Polynomial.derivative_X_pow]
  obtain ⟨w, hw, -⟩ := hH.is_henselian _ hf 0 (eval_zero_quadratic_mem_maximalIdeal t ht htmem) h1
  refine ⟨(w : F), ?_⟩
  have h := congrArg (fun x : 𝒪[F] => (x : F)) hw.eq_zero
  simp at h
  linear_combination 4 * h
open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
lemma valuation_two_le_one : valuation F (2 : F) ≤ 1 := by
  rw [← one_add_one_eq_two]
  exact (valuation F).map_add_le (by simp) (by simp)
open MeasureTheory Matrix in
open ValuativeRel in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem _root_.GlobalTheory.NormBall.val_trace_sq_le {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (a b : F) :
    valuation F (2 * a) ^ 2 ≤ valuation F (a ^ 2 - d * b ^ 2) := by
  rcases eq_or_ne (2 * a) 0 with h2a | h2a
  · simp [h2a]
  by_contra hlt
  push_neg at hlt
  set e := a ^ 2 - d * b ^ 2 with he
  have ha : a ≠ 0 := right_ne_zero_of_mul h2a
  have h2 : (2 : F) ≠ 0 := left_ne_zero_of_mul h2a
  have het : e = e / (2 * a) ^ 2 * (2 * a) ^ 2 := by field_simp
  have ht : valuation F (e / (2 * a) ^ 2) < 1 := by
    by_contra hge
    push_neg at hge
    have hv : valuation F e = valuation F (e / (2 * a) ^ 2) * valuation F (2 * a) ^ 2 := by
      rw [← map_pow, ← map_mul, ← het]
    have : valuation F (2 * a) ^ 2 ≤ valuation F e := by
      rw [hv]
      exact le_mul_of_one_le_left' hge
    exact (not_le.2 hlt) this
  obtain ⟨w, hw⟩ := exists_sq_eq_one_sub_four_mul ht
  rcases eq_or_ne b 0 with hb | hb
  · have hea : e = a ^ 2 := by simp [he, hb]
    have : valuation F (2 * a) ^ 2 ≤ valuation F (a ^ 2) := by
      rw [map_mul, map_pow, mul_pow]
      exact mul_le_of_le_one_left' (pow_le_one₀ zero_le valuation_two_le_one)
    rw [hea] at hlt
    exact (not_le.2 hlt) this
  apply hd (a / b * (1 + 2 * w))
  rw [mul_pow, hw]
  field_simp
  rw [he]
  ring
def ballSub {d : F} (hd : ∀ r : F, r ^ 2 ≠ d) (s : Fˣ) : AddSubgroup (F × F) where
  carrier := {p | p.1 ^ 2 - d * p.2 ^ 2 ∈ GlobalTheory.SplitWeil.cball s}
  zero_mem' := by simp [GlobalTheory.SplitWeil.cball]
  neg_mem' := by
    intro p hp
    simpa using hp
  add_mem' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h h'
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at h h' ⊢
    have e : (a + a') ^ 2 - d * (b + b') ^ 2 =
        (a ^ 2 - d * b ^ 2) + (a' ^ 2 - d * b' ^ 2) + 2 * (a * a' - d * b * b') := by ring
    have k := val_trace_sq_le hd (a * a' - d * b * b') (a * b' - b * a')
    have e2 : (a * a' - d * b * b') ^ 2 - d * (a * b' - b * a') ^ 2 =
        (a ^ 2 - d * b ^ 2) * (a' ^ 2 - d * b' ^ 2) := by ring
    rw [e2, map_mul (valuation F) (a ^ 2 - d * b ^ 2)] at k
    have k2 : valuation F (2 * (a * a' - d * b * b')) ≤ valuation F (s : F) := by
      refine le_of_pow_le_pow_left₀ two_ne_zero zero_le (k.trans ?_)
      rw [sq (valuation F (s : F))]
      exact mul_le_mul' h h'
    rw [e]
    exact (valuation F).map_add_le ((valuation F).map_add_le h h') k2
end GlobalTheory.NormBall


