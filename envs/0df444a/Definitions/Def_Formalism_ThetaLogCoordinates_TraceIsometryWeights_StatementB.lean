-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:37.893082+00:00
-- url     : https://prove2.me/theorems/7975b0b1-5a6b-41b9-a3f8-4ba3303f3af3
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/StatementB.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity
def HomInv : Prop :=
  ∀ (K V₁ V₂ : Type) [Field K] [CharZero K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] (n : ℕ)
    (G₁ : GlW K V₁ n) (G₂ : GlW K V₂ n) (W : Submodule K V₂) (l : ℕ), G₂.Stable W → WtBound2 G₁ G₂ W l →
    ∀ φ : V₁ →ₗ[K] V₂, (∀ x, φ x ∈ W) → (∀ c, homAct G₁.E G₂.E c c φ = 0) →
      (∀ a b x, InvOp (homAct G₁.E G₂.E) l (List.finRange n) φ (G₁.E a b x) =
        G₂.E a b (InvOp (homAct G₁.E G₂.E) l (List.finRange n) φ x)) ∧
      (∀ x, InvOp (homAct G₁.E G₂.E) l (List.finRange n) φ x ∈ W) ∧
      InvOp (homAct G₁.E G₂.E) l (List.finRange n) φ - φ ∈
        ⨆ (a : Fin n) (b : Fin n) (_ : a ≠ b), LinearMap.range (homAct G₁.E G₂.E a b)
def SchurTrace : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (G : GlW K V n) (W : Submodule K V)
    (l : ℕ), G.Stable W → FiniteDimensional K W → G.FinW W →
    (∀ (μ ν : Fin n → ℤ) (x y : V), x ≠ 0 → y ≠ 0 → x ∈ W → y ∈ W → G.IsWt μ x → G.IsWt ν y →
      ∀ c, |ν c - μ c| ≤ (l : ℤ)) →
    ∀ (la : Fin n → ℤ) (h : V), G.IsHW la h → h ∈ W → h ≠ 0 →
    ∀ φ : (G.gS {h}) →ₗ[K] (G.gS {h}),
      (∀ c, homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E c c φ = 0) →
      InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ =
        (LinearMap.trace K _ φ / (Module.finrank K (G.gS {h}) : K)) • LinearMap.id
def TypeInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module ℚ_[p] V] (n : ℕ) (G : GlW ℚ_[p] V n)
    (W : Submodule ℚ_[p] V) (M : AddSubgroup V) (l : ℕ), LatData p G W M l → ∀ la : Fin n → ℤ,
    ∃ Q : V →ₗ[ℚ_[p]] V, (∀ x ∈ IsoW G W la, Q x = x) ∧ (∀ mu, mu ≠ la → ∀ x ∈ IsoW G W mu, Q x = 0) ∧
      ∀ m ∈ M, m ∈ W → ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • Q m ∈ M
def WeylInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module ℚ_[p] V] (n : ℕ) (G : GlW ℚ_[p] V n)
    (W : Submodule ℚ_[p] V) (M : AddSubgroup V) (l : ℕ), LatData p G W M l → ∀ la : Fin n → ℤ,
    ∀ x ∈ IsoW G W la, x ∈ M →
      ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • x ∈ DeltaLat p G {h | G.IsHW la h ∧ h ∈ W ∧ h ∈ M}
end Formalism.InvariantFactorPaths.PW


