-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:08.60944+00:00
-- url     : https://prove2.me/theorems/c0e38bb1-ad52-4ed7-aa48-9e00ef256965
-- title:
--   St Genus Of
-- statement:
--   Definitions and structural lemmas for St Genus Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/StGenusOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelClassFin
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
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
def StCong : Prop :=
  ∀ (I : AutInst) (U : Subgroup I.Gf), IsOpen (U : Set I.Gf) → ∃ g : ℕ, 1 ≤ g ∧ I.Kg g ⊆ (U : Set I.Gf)
def StKFin : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ T : Finset I.Gf, ∀ k ∈ I.Kset, ∃ t ∈ T, ∃ u ∈ I.Kg g, k = t * u
def StGenus : Prop :=
  ∀ I : AutInst, ∃ S : Finset I.Gf, ∀ x : I.Gf, ∃ γ ∈ GFf I, ∃ s ∈ S, ∃ k ∈ I.Kset, x = γ * s * k
def StTop : Prop := StCong → StKFin → StGenus → PI.AdelClassFin.AdelClassFin
def SelfDual {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (M : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ x : Fin n → E, x ∈ M ↔ ∀ y ∈ M, Formalism.UG.hform (starRingEnd E) J y x ∈ (algebraMap (𝓞 E) E).range
def IsImg {E : Type} [Field E] [NumberField E] {n : ℕ} (γ : GL (Fin n) E) (M₀ M : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v : Fin n → E, v ∈ M ↔ ∃ w ∈ M₀, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v
def StH : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Formalism.UG.IsHerm (starRingEnd E) J → J.det ≠ 0 →
    ∃ T : Finset (Submodule (𝓞 E) (Fin n → E)), ∀ M : Submodule (𝓞 E) (Fin n → E), M.FG →
      Submodule.span E (M : Set (Fin n → E)) = ⊤ → SelfDual J M →
      ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧ ∃ M₀ ∈ T, IsImg γ M₀ M
def StDict : Prop :=
  ∀ I : AutInst, ∃ Λ : I.Gf → Submodule (𝓞 I.E) (Fin I.n → I.E),
    (∀ x, (Λ x).FG ∧ Submodule.span I.E ((Λ x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = ⊤ ∧ SelfDual I.J (Λ x)) ∧
    (∀ x y, Λ x = Λ y → ∃ k ∈ I.Kset, y = x * k) ∧
    (∀ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J →
      ∃ c ∈ GFf I, I.fmat c = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) ∧
        ∀ x, IsImg γ (Λ x) (Λ (c * x)))
def StGenusOf : Prop := StDict → StH → StGenus
end PIW.AdelClassFin


