-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:32.641801+00:00
-- url     : https://prove2.me/theorems/53692f8c-a3b4-40b2-a9d3-883218c00adc
-- title:
--   Vp Bounds
-- statement:
--   Definitions and structural lemmas for Vp Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/VpBounds.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory.CMVal
namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
variable {E : Type} [Field E] [NumberField E]
def ValGe_vp (l : ℕ) (r : ℝ) (a : ℂ) : Prop :=
  ∀ (m : ℤ) (n : ℕ), 0 < n → r ≤ (m : ℝ) / n → IntAt l ((l : ℂ) ^ m * a ^ n)
def IsClassZeta (C : ClassGroup (OF E)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun 𝔞 : {𝔞 : (Ideal (OF E))⁰ // ClassGroup.mk0 𝔞 = C} =>
      ((Ideal.absNorm (𝔞.1 : Ideal (OF E)) : ℕ) : ℂ) ^ (-s)) (Z s)
def IsClassZetaVals (k : ℕ) (z : ClassGroup (OF E) → ℚ) : Prop :=
  ∀ C, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (z C : ℂ)
def cE_vp (l : ℕ) (z : ClassGroup (OF E) → ℚ) : ℕ :=
  Finset.univ.sup fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat
def delta_vp (E : Type) [Field E] [NumberField E] (l : ℕ) : ℝ :=
  (padicValInt l (discr E) : ℝ) / (Module.finrank ℚ E : ℝ)
def a0 (𝔣 : Ideal (OF E)) (l : ℕ) : ℕ :=
  sSup {n | ∃ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal ∧ expIn 𝔣 v = n}
open Classical in

def c_vp (𝔣 : Ideal (OF E)) (l : ℕ) : ℝ :=
  if ∃ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal ∧ v.asIdeal ∣ 𝔣 then (a0 𝔣 l : ℝ) else delta_vp E l
variable {I : Type} [Fintype I]
open Classical in

def n_vp (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (l : ℕ) : ℝ :=
  if c_vp 𝔣 l = 0 then 0
  else Formalism.PairingDivisionLocalBalance.nl ((2 * s * Fintype.card I : ℕ) : ℝ) (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) (c_vp 𝔣 l)
    ((if l = 2 then 1 else 0) + (if l = d then 1 / 2 else 0))
def IsFieldData (d : ℕ) (φ : I → E →+* ℂ) : Prop :=
  d.Prime ∧ 4 < d ∧ UnramFin E ∧ (∀ x : E, IsOfFinOrder x → ∏ i, φ i x = 1) ∧ (2 : ℤ) ∣ discr E ∧
    2 ≤ Fintype.card I ∧ IsCMType φ ∧ ∃ w : E, w ^ 2 = -(d : E) ∧ ∀ i, φ i w = Complex.I * (Real.sqrt d : ℝ)
def IsIntLattice (d : ℕ) (Λ : PeriodPair) : Prop :=
  ∀ x : ℂ, x ∈ Λ.lattice ↔ IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))
def IsClassTerm (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (y : (Af E)ˣ) (T : ℂ) : Prop :=
  ∃ S : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y) S ∧ T = ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0
def IsPicChar (c : Ideal (OF E)) (ψ : HChar E) : Prop :=
  (∀ x : Eˣ, infPart ψ x = 1) ∧ ∀ u ∈ hatOUnits c, finPart ψ u = 1
def IsLevelChar (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (χ : HChar E) : Prop :=
  IsUnitary χ ∧ TrivOnF χ ∧ HasInf χ φ (fun i => (κ i : ℤ) + s) ∧
    ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Over P v → LevelLe χ P (expIn 𝔣 v)
def betaBound_vp (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (z : ClassGroup (OF E) → ℚ) (l : ℕ) : ℝ :=
  12 * ((cE_vp l z : ℝ) + n_vp d s κ 𝔣 l + (Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ : ℝ) * (a0 𝔣 l : ℝ))
def DenomBound (d s : ℕ) (φ : I → E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Λ : PeriodPair)
    (z : ClassGroup (OF E) → ℚ) (χ : HChar E) : Prop :=
  ∀ l : ℕ, l.Prime → ∀ Q : Finset (HeightOneSpectrum (OF E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    (∀ (y : (Af E)ˣ) (T : ℂ), IsClassTerm φ s κ (condQ 𝔣 Q) χ y T →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ T)) ∧
    (∀ (ψ : HChar E) (T : ℂ), IsPicChar (condQ 𝔣 Q) ψ → IsToricSum φ s κ (condQ 𝔣 Q) (χ * ψ) T →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ T))
def ToricDenominator : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I]
    (d : ℕ) (φ : I → E →+* ℂ) (s : ℕ), IsFieldData d φ → 1 ≤ s →
    ∃ z : ClassGroup (OF E) → ℚ, IsClassZetaVals (2 * s) z ∧
      ∀ (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Λ : PeriodPair) (χ : HChar E),
        IsBaseCond 𝔣 → IsIntLattice d Λ → IsValChar φ s κ 𝔣 ∅ χ → DenomBound d s φ κ 𝔣 Λ z χ
def ToricDenominatorLevel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I]
    (d : ℕ) (φ : I → E →+* ℂ) (s : ℕ), IsFieldData d φ → 1 ≤ s →
    ∃ z : ClassGroup (OF E) → ℚ, IsClassZetaVals (2 * s) z ∧
      ∀ (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Λ : PeriodPair) (χ : HChar E),
        IsBaseCond 𝔣 → IsIntLattice d Λ → IsLevelChar φ s κ 𝔣 χ → DenomBound d s φ κ 𝔣 Λ z χ
example (l : ℕ) (a : ℂ) (h : ValGe_vp l 0 a) : IntAt l a := by
  simpa using h 0 1 one_pos (by simp)
example (c : Ideal (OF E)) : IsPicChar c (1 : HChar E) := ⟨fun _ => rfl, fun _ _ => rfl⟩
end GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds


