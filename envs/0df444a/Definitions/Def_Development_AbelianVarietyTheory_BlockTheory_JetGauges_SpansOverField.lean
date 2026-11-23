-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SpansOverField
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_SpansOverField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:41.323444+00:00
-- url     : https://prove2.me/theorems/a83cdf7b-e8f5-427c-9bfa-d2a5ed0351ab
-- title:
--   Spans Over Field
-- statement:
--   Definitions and structural lemmas for Spans Over Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SpansOverField.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement
open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
section Lattice
variable (E : Type) [Field E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
def GenMod (r₁ : ℕ) {ι : Type} (y : ι → X) : Prop :=
  ∀ x : X, ∃ z : X, x - r₁ • z ∈ Submodule.span (𝓞 E) (Set.range y)
def SpansOverField {ι : Type} (x : ι → X) : Prop :=
  ∀ u : X, ∃ n : ℕ, 0 < n ∧ n • u ∈ Submodule.span (𝓞 E) (Set.range x)
end Lattice
def LatticeStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (r₁ R : ℕ), 2 ≤ r₁ → r₁ ∣ R →
    ∀ (r : ℕ) (y : Fin r → X), GenMod E r₁ y →
    ∀ z : Fin r → X, SpansOverField E (fun b => y b + R • z b)
section PhiC
variable (E : Type) [Field E] [NumberField E] [IsCMField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
abbrev bar (a : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a
def outer {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) : 𝓞 E :=
  ∑ i, η (x i) * bar E (η' (x' i))
def IsPosHerm (l : Module.Dual (𝓞 E) X → Module.Dual (𝓞 E) X → 𝓞 E) : Prop :=
  (∀ η η', l η' η = bar E (l η η')) ∧
    ∀ η, η ≠ 0 → ∀ τ : E →+* ℂ, 0 < (τ (l η η : E)).re
def IsBalanced (B : X → X → ℝ) : Prop :=
  ∀ (a : 𝓞 E) (x x' : X), B (a • x) x' = B x (bar E a • x')
def pairing (B : X → X → ℝ) {n : ℕ} (x x' : Fin n → X) : ℝ := (∑ i, B (x i) (x' i)) / 2
def phiC (B : X → X → ℝ) : EReal :=
  sInf {t : EReal | ∃ (n : ℕ) (x x' : Fin n → X), IsPosHerm E (outer E x x') ∧ t = (pairing B x x' : ℝ)}
example [Subsingleton X] (B : X → X → ℝ) (hB : B 0 0 = 0) : phiC E B = 0 := by
  have hp : ∀ {n : ℕ} (x x' : Fin n → X), pairing B x x' = 0 := by
    intro n x x'
    simp [pairing, fun i => Subsingleton.elim (x i) 0, fun i => Subsingleton.elim (x' i) 0, hB]
  have : {t : EReal | ∃ (n : ℕ) (x x' : Fin n → X), IsPosHerm E (outer E x x') ∧
      t = (pairing B x x' : ℝ)} = {0} := by
    ext t
    constructor
    · rintro ⟨n, x, x', -, rfl⟩
      simp [hp]
    · rintro rfl
      refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun _ _ => by simp [outer], fun η hη => ?_⟩, by simp [hp]⟩
      exact absurd (LinearMap.ext fun a => by simp [Subsingleton.elim a 0]) hη
  rw [phiC, this, sInf_singleton]
end PhiC
def valToEReal (t : WithTop ℚ) : EReal :=
  WithTop.recTopCoe (⊤ : EReal) (fun q : ℚ => (((q : ℝ)) : EReal)) t
def ValuationStep_vw : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Module (𝓞 E) D.toPre.X],
      IsBalanced E (fun χ χ' : D.toPre.X => (bOf D.toPre Q χ χ' : ℝ)) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (r₁ R : ℕ), 2 ≤ r₁ → 1 ≤ R → r₁ ∣ R →
    ∀ (r : ℕ) (y : Fin r → D.toPre.X), GenMod E r₁ y →
    ∀ (s : Fin r → Fam D.toPre F (R ^ 2)) (w : Fin r → F),
      (∀ b, NuGe D Q F v (R ^ 2) (s b) 0) →
      (∀ b, ∀ α : D.toPre.X, (∀ z : D.toPre.X, α ≠ y b + R • z) → ∀ j, ((s b).s α).f j = 0) →
      (∀ b, ValAt0 D F v (R ^ 2) (s b) (w b)) →
      phiC E (fun χ χ' : D.toPre.X => (bOf D.toPre Q χ χ' : ℝ)) / (((R : ℝ) ^ 2 : ℝ) : EReal) ≤
        valToEReal (∑ b, v (w b))
def PointStep : Prop := LatticeStep ∧ ValuationStep_vw
end GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement


