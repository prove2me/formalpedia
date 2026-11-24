-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:12:20.669862+00:00
-- url     : https://prove2.me/theorems/2e8c7b30-1888-4953-85a2-ba0aa272b878
-- title:
--   Part Short Of
-- statement:
--   Definitions and structural lemmas for Part Short Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/PartShortOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix ComplexOrder
section Defs
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def gramTr {m N : ℕ} (J : Matrix (Fin m) (Fin m) E) (e : Fin N → Fin m → E) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j))
def IsMajFam {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ φ : E →+* ℂ, (H φ).PosDef ∧ (H φ).det = ((‖(J.map φ).det‖ : ℝ) : ℂ) ∧
    (∀ z : Fin m → ℂ, ‖star z ⬝ᵥ (J.map φ *ᵥ z)‖ ≤ (star z ⬝ᵥ (H φ *ᵥ z)).re) ∧
    H (ComplexEmbedding.conjugate φ) = (H φ).map (starRingEnd ℂ)
end Defs
def SvCodiffAt (E : Type) [Field E] [NumberField E] (δ : ℕ) : Prop :=
  ∀ y : E, (∀ a : 𝓞 E, Algebra.trace ℚ E (algebraMap (𝓞 E) E a * y) ∈ (algebraMap ℤ ℚ).range) →
    (δ : E) * y ∈ (algebraMap (𝓞 E) E).range
def SvCodiff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], ∃ δ : ℕ, 1 ≤ δ ∧ SvCodiffAt E δ
def SvMaj : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.IsHermitian → J.det ≠ 0 →
    ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ H.det = ((‖J.det‖ : ℝ) : ℂ) ∧
      ∀ z : Fin n → ℂ, ‖star z ⬝ᵥ (J *ᵥ z)‖ ≤ (star z ⬝ᵥ (H *ᵥ z)).re
def SvMajE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J → J.det ≠ 0 →
      ∃ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H
def SvBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (M : Submodule (𝓞 E) (Fin m → E)),
    M.FG → Submodule.span E (M : Set (Fin m → E)) = ⊤ →
      ∃ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e ∧ (∀ i, e i ∈ M) ∧
        ∀ x ∈ M, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i
def SvGramDet : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ m d δ : ℕ, 1 ≤ d → 1 ≤ δ → SvCodiffAt E δ → ∀ p ∈ Lat E m d,
      ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e → (∀ i, e i ∈ p.2) →
        (∀ x ∈ p.2, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i) →
          (gramTr p.1 e).det ≠ 0 ∧ |(gramTr p.1 e).det| ≤ ((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E)
def SvReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J →
      ∀ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H →
        ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, (gramTr J e).det ≠ 0 →
          ∃ R : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℝ,
            R.PosDef ∧ R.det = |((gramTr J e).det : ℝ)| ∧
              ∀ c : Fin (m * Module.finrank ℚ E) → ℤ,
                ∑ φ : E →+* ℂ, ‖φ (hform (starRingEnd E) J (∑ i, (c i : E) • e i) (∑ i, (c i : E) • e i))‖ ≤
                  (fun i => (c i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (c i : ℝ))
end PIW.AdelClassFin


