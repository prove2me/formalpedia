-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:48.958584+00:00
-- url     : https://prove2.me/theorems/5a22aee1-dce0-41ed-9022-03f88968629b
-- title:
--   Add Char Mem Valuation Subring
-- statement:
--   Definitions and structural lemmas for Add Char Mem Valuation Subring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AddCharMemValuationSubring.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
namespace GlobalTheory.FourierChainCompare
section Duality
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]
theorem linearIndependent_addChar (A K : Type) [AddCommGroup A] [Field K] :
    LinearIndependent K (fun χ : AddChar A K => (χ : A → K)) :=
  (linearIndependent_monoidHom (Multiplicative A) K).comp AddChar.toMonoidHomEquiv
    AddChar.toMonoidHomEquiv.injective
theorem finite_addChar (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    Finite (AddChar A K) := (linearIndependent_addChar A K).finite
theorem card_addChar_le (A K : Type) [AddCommGroup A] [Fintype A] [Field K] :
    Nat.card (AddChar A K) ≤ Fintype.card A := by
  haveI := finite_addChar A K
  letI := Fintype.ofFinite (AddChar A K)
  rw [Nat.card_eq_fintype_card]
  simpa using (linearIndependent_addChar A K).fintype_card_le_finrank
theorem perfect_flip {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    IsPerfectPairing (fun t a => e a t) :=
  ⟨fun t t' a => he.add_right a t t', fun t a a' => he.add_left a a' t, he.nondeg_right,
    he.nondeg_left⟩
theorem pairing_zero {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) : e 0 t = 1 := by
  have h := he.add_left 0 0 t
  rw [add_zero] at h
  exact left_eq_mul.mp h
def chr {e : A → B → Kˣ} (he : IsPerfectPairing e) (t : B) : AddChar A K where
  toFun a := ((e a t : Kˣ) : K)
  map_zero_eq_one' := by rw [pairing_zero he, Units.val_one]
  map_add_eq_mul' a a' := by rw [he.add_left, Units.val_mul]
theorem chr_injective {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    Function.Injective (chr he) := by
  intro t t' h
  refine sub_eq_zero.mp (he.nondeg_right _ fun a => ?_)
  have h1 : e a t = e a t' := Units.ext (DFunLike.congr_fun h a)
  have h2 := he.add_right a (t - t') t'
  rw [sub_add_cancel, h1] at h2
  exact right_eq_mul.mp h2
variable [Fintype A] [Fintype B]
theorem card_le_of_perfect {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    Fintype.card B ≤ Nat.card (AddChar A K) := by
  haveI := finite_addChar A K
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective _ (chr_injective he)
theorem card_eq_of_perfect {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    Fintype.card A = Fintype.card B :=
  le_antisymm ((card_le_of_perfect (perfect_flip he)).trans (card_addChar_le B K))
    ((card_le_of_perfect he).trans (card_addChar_le A K))
theorem card_addChar_of_perfect {e : A → B → Kˣ} (he : IsPerfectPairing e) :
    Nat.card (AddChar A K) = Fintype.card A :=
  le_antisymm (card_addChar_le A K) ((card_eq_of_perfect he).le.trans (card_le_of_perfect he))
def chrEquiv {e : A → B → Kˣ} (he : IsPerfectPairing e) : B ≃ AddChar A K :=
  haveI := finite_addChar A K
  Equiv.ofBijective (chr he) ((chr_injective he).bijective_of_nat_card_le (by
    rw [card_addChar_of_perfect he, card_eq_of_perfect he, Nat.card_eq_fintype_card]))
def ManyChars (A K : Type) [AddCommGroup A] [Fintype A] [Field K] : Prop :=
  (Fintype.card A : K) ≠ 0 ∧ Nat.card (AddChar A K) = Fintype.card A
def evalPairing (A K : Type) [AddCommGroup A] [Field K] (a : A)
    (χ : Additive (Multiplicative A →* Kˣ)) : Kˣ :=
  (Additive.toMul χ) (Multiplicative.ofAdd a)
end Duality
section Fourier
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K] [Fintype A] [Fintype B]
def CoeffIntAllChars : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (K : Type) [Field K] (O : Subring K) (φ : A → K),
    ManyChars A K → (∀ a, φ a ∈ O) → (∀ (χ : AddChar A K) a, χ a ∈ O) → ∀ χ : AddChar A K,
      (Fintype.card A : K) * ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) ∈ O ∨
        (Fintype.card A : K) = 0
end Fourier
section Chain
variable {R : Type} [CommRing R] {d : ℕ}
def ChainIntOn (s : Set ℤ) : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (O : Type) [CommRing O] (A : OAct O G)
    (ι : Type) [Fintype ι] (u : ι → Fin d → R) (P : MvPolynomial ι R) (k : ℕ),
      P.IsHomogeneous k → ∀ n ∈ s, ∀ f : PS R 1 d,
        constantCoeff (DpolyOf G.F u P (ev ![A.act (n : O)] f)) =
          (n : R) ^ k * constantCoeff (DpolyOf G.F u P f)
end Chain
end GlobalTheory.FourierChainCompare


