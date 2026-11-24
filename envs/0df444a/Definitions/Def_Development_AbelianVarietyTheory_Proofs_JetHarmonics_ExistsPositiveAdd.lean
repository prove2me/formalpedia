-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPositiveAdd
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPositiveAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:37.118148+00:00
-- url     : https://prove2.me/theorems/4ff2945f-48b5-4ce2-a7e7-0a10afa02dd3
-- title:
--   Exists Positive Add
-- statement:
--   Definitions and structural lemmas for Exists Positive Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPositiveAdd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_BalancedHermitianSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LeastExponentCompare
open NumberField NumberField.IsCMField TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
section Comparison₂
variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
def IntegralAreSums (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z) →
    ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Bil Y) (x i) (x' i)
end Comparison₂
section AtLattice
variable (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
def SpanBound (S : Submodule ℝ (Bil Y)) (φ : S → ℝ) (w : 𝓞 E) : Prop :=
  ∀ (β : S), (∀ a, 0 ≤ (β : Bil Y) a a) → ∀ (k : ℕ) (x : Fin k → Y),
    (∀ y : Y, ∃ n : ℕ, 0 < n ∧ n • y ∈ Submodule.span (𝓞 E) (Set.range x)) →
    φ β ≤ ∑ b, (β : Bil Y) (w • x b) (x b)
def MinimaBound (S : Submodule ℝ (Bil Y)) (φ : S → ℝ) : Prop :=
  ∀ (β : S), (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
      (Matrix.of fun i j => (β : Bil Y) (b i) (b j)).PosDef) →
    ∃ v : Fin (Module.finrank ℤ Y) → Y, LinearIndependent ℤ v ∧
      ∀ i, (β : Bil Y) (v i) (v i) / 2 ≤
        (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
            (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * φ β
variable [IsCMField E]
end AtLattice
section Families
abbrev SpaceRule : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Bil Y)
abbrev ValueRule (S : SpaceRule) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ
def Matches (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    IsBalancedSpace E (S E (fun z => complexConj E z) Y) ∧
      φ E (fun z => complexConj E z) Y = leastExponent (S E (fun z => complexConj E z) Y)
def ForAllLattices (P : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y], Submodule ℝ (Bil Y) → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], HasTraceOne E →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (S : Submodule ℝ (Bil Y)), IsBalancedSpace E S → P E Y S
def SpanAll (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] (w : 𝓞 E), (w : E) + cj w = 1 →
      SpanBound E (S E cj Y) (φ E cj Y) w
def SpanCM (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Free ℤ Y] [Module.Finite ℤ Y] (w : 𝓞 E), (w : E) + complexConj E w = 1 →
      SpanBound E (S E (fun z => complexConj E z) Y) (φ E (fun z => complexConj E z) Y) w
def MinimaAll (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (σ : E →+* ℂ) (z : E), σ (cj z) = star (σ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w : 𝓞 E), (w : E) + cj w = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y],
      MinimaBound E (S E cj Y) (φ E cj Y)
def SumsAll (S : SpaceRule) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y], IntegralAreSums (S E cj Y)
def SumsCM (S : SpaceRule) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], HasTraceOne E → ∀ (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y],
      IntegralAreSums (S E (fun z => complexConj E z) Y)
variable {S : SpaceRule} {φ : ValueRule S}
end Families
end GlobalTheory.LeastExponentCompare


