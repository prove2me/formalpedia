-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:22.565553+00:00
-- url     : https://prove2.me/theorems/4afcd873-6731-49ce-9a24-06a1bbe5e193
-- title:
--   Deriv Exists All Pos Statement
-- statement:
--   Definitions and structural lemmas for Deriv Exists All Pos Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/DerivExistsAllPosStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
def URepHomStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (Kset ε) σ →
    ∃ τ : KG ε →* unitary (H →L[ℂ] H), Continuous τ ∧
      ∀ k : KG ε, ((τ k : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = σ (toMK k)
def DerivExistsStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (τ : KG ε →* unitary (V →L[ℂ] V)), Continuous τ →
    ∃ dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V),
      ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
        (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0
def DerivExistsAllPosStatement : Prop :=
  ∀ (k : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (τ : KG (fun _ : Fin k => true) →* unitary (V →L[ℂ] V)), Continuous τ →
    ∃ dτ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] (V →L[ℂ] V),
      ∀ X, inK (fun _ : Fin k => true) X → ∀ γ : ℝ → KG (fun _ : Fin k => true),
        (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0
structure KRep (ε : Fin n → Bool) where
  V : Type
  [instNACG : NormedAddCommGroup V]
  [instIPS : InnerProductSpace ℂ V]
  [instFD : FiniteDimensional ℂ V]
  [instCS : CompleteSpace V]
  τ : KG ε →* unitary (V →L[ℂ] V)
  cont : Continuous τ
  dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V)
  hasDeriv : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
    (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0
attribute [instance] KRep.instNACG KRep.instIPS KRep.instFD KRep.instCS
abbrev KRep.op {ε : Fin n → Bool} (R : KRep ε) (k : KG ε) : R.V →L[ℂ] R.V :=
  ((R.τ k : unitary (R.V →L[ℂ] R.V)) : R.V →L[ℂ] R.V)
def KRep.units {ε : Fin n → Bool} (R : KRep ε) : Fin n → Fin n → Module.End ℂ R.V :=
  fun a b => ((R.dτ (Matrix.single a b 1) : R.V →L[ℂ] R.V) : Module.End ℂ R.V)
def KType.toKRep {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : KRep ε where
  V := T.V
  τ := T.τ
  cont := T.cont
  dτ := T.dτ
  hasDeriv := T.hasDeriv
def KRepRelStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : KRep ε),
    Formalism.REAL.KRel ε R.units ∧ Formalism.REAL.KUnit ε R.units
def KRepStableStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : KRep ε) (W : Submodule ℂ R.V),
    (∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W) ↔ Formalism.REAL.KStable ε R.units W
def KRepPieceStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : KRep ε) (μ : Fin n → ℝ) (x : R.V),
    x ≠ 0 → Formalism.REAL.KHighest ε R.units μ x →
    ∃ (T : KType ε μ) (φ : T.V ≃ₗᵢ[ℂ] Formalism.REAL.kSpan ε R.units x),
      (∀ (k : KG ε) (v : T.V), (φ (T.op k v) : R.V) = R.op k (φ v)) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, X * Jm ε = Jm ε * X →
        ∀ v : T.V, (φ (T.dτ X v) : R.V) = R.dτ X (φ v)) ∧
      (φ T.w : R.V) = ((‖x‖⁻¹ : ℝ) : ℂ) • x
def CompRedStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : KRep ε),
    ∃ (m : ℕ) (x : Fin m → R.V) (μ : Fin m → Fin n → ℝ),
      (∀ i, x i ≠ 0 ∧ Formalism.REAL.KHighest ε R.units (μ i) (x i)) ∧
      (∀ i i', i ≠ i' → ∀ y ∈ Formalism.REAL.kSpan ε R.units (x i),
        ∀ z ∈ Formalism.REAL.kSpan ε R.units (x i'), ⟪y, z⟫_ℂ = 0) ∧
      (⨆ i, Formalism.REAL.kSpan ε R.units (x i)) = ⊤ ∧
      Module.finrank ℂ R.V = ∑ i, Module.finrank ℂ (Formalism.REAL.kSpan ε R.units (x i)) ∧
      (∀ i, ∀ k : KG ε, ∀ v ∈ Formalism.REAL.kSpan ε R.units (x i),
        R.op k v ∈ Formalism.REAL.kSpan ε R.units (x i)) ∧
      ∀ i, ∃ (T : KType ε (μ i)) (φ : T.V ≃ₗᵢ[ℂ] Formalism.REAL.kSpan ε R.units (x i)),
        Module.finrank ℂ T.V = Module.finrank ℂ (Formalism.REAL.kSpan ε R.units (x i)) ∧
        (∀ (k : KG ε) (v : T.V), (φ (T.op k v) : R.V) = R.op k (φ v)) ∧
        (∀ X : Matrix (Fin n) (Fin n) ℂ, X * Jm ε = Jm ε * X →
          ∀ v : T.V, (φ (T.dτ X v) : R.V) = R.dτ X (φ v)) ∧
        (φ T.w : R.V) = ((‖x i‖⁻¹ : ℝ) : ℂ) • x i
def URepCompRedStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (Kset ε) σ →
    ∃ E : Fin n → Fin n → Module.End ℂ H,
      Formalism.REAL.KRel ε E ∧ Formalism.REAL.KUnit ε E ∧
      (∀ X, inK ε X → ∀ v : H,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (actM E X v) 0) ∧
      ∃ (m : ℕ) (x : Fin m → H) (μ : Fin m → Fin n → ℝ),
        (∀ i, x i ≠ 0 ∧ Formalism.REAL.KHighest ε E (μ i) (x i)) ∧
        (∀ i i', i ≠ i' → ∀ y ∈ Formalism.REAL.kSpan ε E (x i),
          ∀ z ∈ Formalism.REAL.kSpan ε E (x i'), ⟪y, z⟫_ℂ = 0) ∧
        (⨆ i, Formalism.REAL.kSpan ε E (x i)) = ⊤ ∧
        (∀ i, ∀ g ∈ Kset ε, ∀ v ∈ Formalism.REAL.kSpan ε E (x i), σ g v ∈ Formalism.REAL.kSpan ε E (x i)) ∧
        ∀ i, ∃ (T : KType ε (μ i)) (φ : T.V ≃ₗᵢ[ℂ] Formalism.REAL.kSpan ε E (x i)),
          (∀ (k : KG ε) (v : T.V), (φ (T.op k v) : H) = σ (toMK k) (φ v)) ∧
          (∀ a b, ε a = ε b → ∀ v : T.V, (φ (T.dτ (Matrix.single a b 1) v) : H) = E a b (φ v)) ∧
          (φ T.w : H) = ((‖x i‖⁻¹ : ℝ) : ℂ) • x i
end ReciprocityTheory.ChartRestriction.DS.HW


