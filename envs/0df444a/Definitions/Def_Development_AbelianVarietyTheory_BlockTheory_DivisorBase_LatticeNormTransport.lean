-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:53.019479+00:00
-- url     : https://prove2.me/theorems/6a9c34a9-286a-4a59-ab36-784313d6585c
-- title:
--   Lattice Norm Transport
-- statement:
--   Definitions and structural lemmas for Lattice Norm Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/LatticeNormTransport.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Theorems.Thm_GlobalTheory_CMVal_beta_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors
namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
section Quadratic
variable {K : Type} [Field K] [NumberField K]
def Fixes (φK : K →+* ℂ) (σ : ℂ ≃+* ℂ) : Prop := ∀ x : K, σ (φK x) = φK x
def IsInvIdealOf (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Prop :=
  ∀ x : K, x ∈ 𝔞 ↔ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) x) v) ≤ 1
def IsLatOf (φK : K →+* ℂ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (Λ : PeriodPair) : Prop :=
  (Λ.lattice : Set ℂ) = φK '' (𝔞 : Set K)
def jLat (Λ : PeriodPair) : ℂ := 1728 * Λ.g₂ ^ 3 / latDisc Λ
def nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ := ((FractionalIdeal.absNorm 𝔞 : ℚ) : ℝ)
def Equidistributed (φK : K →+* ℂ) (j₀ : ℂ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Prop :=
  IsAlgebraic ℚ j₀ ∧
  (∀ σ σ' : ℂ ≃+* ℂ, Fixes φK σ → Fixes φK σ' →
    (ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') ↔ σ j₀ = σ' j₀)) ∧
  ∀ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L → IsGalois ℚ L → (∀ x : K, φK x ∈ L) → j₀ ∈ L →
    ∀ C : ClassGroup (𝓞 K),
      Nat.card {τ : L →+* ℂ // ∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧ ClassGroup.mk K (𝔞 σ) = C}
        * (2 * classNumber K) = Module.finrank ℚ L
end Quadratic
section CM
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
def lamF (s : ℕ) (χ : HChar E) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)
def IsConjWt (φ : I → E →+* ℂ) (σ : ℂ ≃+* ℂ) (κ κ' : I → ℕ) : Prop :=
  ∀ i j : I, (∀ x : E, σ (φ i x) = φ j x) → κ' j = κ i
def IsConjChar (φ : I → E →+* ℂ) (s : ℕ) (κ' : I → ℕ) (σ : ℂ ≃+* ℂ) (χ χ' : HChar E) : Prop :=
  (∀ y : (Af E)ˣ, lamF s χ' y = σ (lamF s χ y)) ∧ HasInf χ' φ (fun i => (κ' i : ℤ) + s)
def IsValSum (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E)))
    (χ : HChar E) (T : ℂ) : Prop :=
  IsFinSetSplitPlacesCoprimeConductor 𝔣 Q ∧ IsValChar φ s κ 𝔣 Q χ ∧ IsToricSum φ s κ (condQ 𝔣 Q) χ T
def IsConjSum (φ : I → E →+* ℂ) (s : ℕ) (κ' : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E)))
    (σ : ℂ ≃+* ℂ) (χ χ' : HChar E) (T' : ℂ) : Prop :=
  IsConjChar φ s κ' σ χ χ' ∧ IsToricSum φ s κ' (condQ 𝔣 Q) χ' T'
end CM
def upIdele (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] : (Af K)ˣ →* (Af E)ˣ :=
  Units.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K E).toMonoidHom
def TransportFor {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I]
    (d : ℕ) (φK : K →+* ℂ) (ΛK : PeriodPair) (t : (ℂ ≃+* ℂ) → (Af K)ˣ)
    (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair)
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) : Prop :=
  (∀ (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ), IsValSum φ s κ 𝔣 Q χ T →
    IsAlgebraic ℚ (beta E d s κ ΛK T) ∧
    ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∀ κ' : I → ℕ, IsConjWt φ σ κ κ' →
      ∀ (χ' : HChar E) (T' : ℂ), IsConjSum φ s κ' 𝔣 Q σ χ χ' T' →
        σ (beta E d s κ ΛK T) =
          ((C0 E d (2 * s) κ : ℂ) * ((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ (∑ i, κ i))⁻¹ *
              (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') ^ 12 / latDisc (Λ σ) ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i) ∧
        ‖σ (beta E d s κ ΛK T)‖ =
          (C0 E d (2 * s) κ * ‖T'‖) ^ 12 *
            ((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (Λ σ)‖) ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i))⁻¹) ∧
  (∀ (Q₁ Q₂ : Finset (HeightOneSpectrum (OF E))) (χ₁ χ₂ : HChar E) (T₁ T₂ : ℂ),
    IsValSum φ s κ 𝔣 Q₁ χ₁ T₁ → IsValSum φ s κ 𝔣 Q₂ χ₂ T₂ → T₂ ≠ 0 →
    IsAlgebraic ℚ (T₁ / T₂) ∧
    ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∀ κ' : I → ℕ, IsConjWt φ σ κ κ' →
      ∀ (χ₁' χ₂' : HChar E) (T₁' T₂' : ℂ), IsConjSum φ s κ' 𝔣 Q₁ σ χ₁ χ₁' T₁' → IsConjSum φ s κ' 𝔣 Q₂ σ χ₂ χ₂' T₂' →
        T₂' ≠ 0 ∧
        σ (T₁ / T₂) = ((lamF s χ₁' (upIdele K E (t σ)))⁻¹ * T₁') / ((lamF s χ₂' (upIdele K E (t σ)))⁻¹ * T₂'))
def Transport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ), 4 < d → Module.finrank ℚ K = 2 → discr K = -(d : ℤ) →
  ∀ (φK : K →+* ℂ) (ΛK : PeriodPair), IsLatOf φK 1 ΛK →
  ∃ (t : (ℂ ≃+* ℂ) → (Af K)ˣ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair),
    (∀ σ : ℂ ≃+* ℂ, Fixes φK σ →
      IsInvIdealOf (t σ) (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ∧ IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) (Λ σ) ∧
        jLat (Λ σ) = σ (jLat ΛK)) ∧
    Equidistributed φK (jLat ΛK) 𝔞 ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] [Algebra K E], UnramFin E →
    ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ), 2 ≤ Fintype.card I → IsCMType φ →
      (∀ i, (φ i).comp (algebraMap K E) = φK) →
    ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)), 1 ≤ s → (∀ i, 1 ≤ κ i) → IsBaseCond 𝔣 →
      TransportFor d φK ΛK t 𝔞 Λ φ s κ 𝔣
example {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Λ : PeriodPair) (n l T : ℂ) :
    ((C0 E d (2 * s) κ : ℂ) * n * l * T) ^ 12 / latDisc Λ ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i) =
      beta E d s κ Λ (n * l * T) := by
  rw [beta_eq]; ring
example {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (χ : HChar E)
    (h : HasInf χ φ fun i => (κ i : ℤ) + s) : IsConjChar φ s κ (RingEquiv.refl ℂ) χ χ := ⟨fun _ => rfl, h⟩
end GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport


