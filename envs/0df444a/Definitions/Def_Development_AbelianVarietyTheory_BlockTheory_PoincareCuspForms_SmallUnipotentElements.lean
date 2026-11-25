-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_SmallUnipotentElements
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_SmallUnipotentElements
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:22:44.005184+00:00
-- url     : https://prove2.me/theorems/c0c85739-3c32-430f-bb50-64cceb7096fb
-- title:
--   Small Unipotent Elements
-- statement:
--   Definitions and structural lemmas for Small Unipotent Elements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/SmallUnipotentElements.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements
open NumberField ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def OpNormLe {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) E)
    (c : ℝ) : Prop :=
  ∀ u : Fin r → ℂ, X.maj x τ ((A.map τ.1).mulVec u) ≤ c ^ 2 * X.maj x τ u
def OpNormLtOne {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) E) :
    Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ OpNormLe X x τ A c
def IsLatEnd {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E)) (N : Matrix (Fin r) (Fin r) E) : Prop :=
  ∀ v ∈ L, N.mulVec v ∈ L
def NoContraction {r : ℕ} (X : DataX E r) (x : Frame X.Ψ r) : Prop :=
  ∀ N : Matrix (Fin r) (Fin r) E, IsLatEnd X.L' N → (∀ τ : X.Ψ, OpNormLtOne X.toData x τ N) → N = 0
def NoShortVector {r : ℕ} (X : DataX E r) (x : Frame X.Ψ r) : Prop :=
  ∀ v ∈ X.L', v ≠ 0 → (fdeg E : ℝ) ≤ ∑ τ : X.Ψ, X.maj x τ (Data.emb τ.1 v)
def IsTotallySplitPrime (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E
def IsUnipotentModOver {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E)) (g : ℕ) (γ : GL (Fin r) E) : Prop :=
  ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), ∃ k : ℕ, ∀ v ∈ L,
    (((γ : Matrix (Fin r) (Fin r) E) - 1) ^ k).mulVec v ∈ P • L
def BalancedPointStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : DataX E r), ∃ x ∈ X.dom, NoContraction X x ∧ NoShortVector X x
def SmallElementStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (g : ℕ), IsTotallySplitPrime E g → 3 * r < g →
    ∀ Γo : Subgroup (GL (Fin r) E), (∀ γ ∈ Γo, IsUStab X.Gm X.L' γ) →
    (∀ γ ∈ Γo, IsUnipotentModOver X.L' g γ) →
    ∀ x ∈ X.dom, NoContraction X x →
    ∀ γ ∈ Γo, (∀ τ : X.Ψ, OpNormLe X.toData x τ (γ : Matrix (Fin r) (Fin r) E)
      (Real.exp (1 / (3 * (r : ℝ))))) → γ = 1
def BalancedBallStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  BalancedPointStatement E ∧ SmallElementStatement E
end
end GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements


