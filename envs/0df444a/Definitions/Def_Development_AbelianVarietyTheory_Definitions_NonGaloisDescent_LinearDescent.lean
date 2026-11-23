-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:56.932798+00:00
-- url     : https://prove2.me/theorems/05c4b3bd-e9e1-4d35-94f8-fa4385e0b6b9
-- title:
--   Linear Descent
-- statement:
--   Definitions and structural lemmas for Linear Descent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LinearDescent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma
open Polynomial Filter Topology
namespace InvAlg
variable {K : UQ} (B : InvAlg K)
def UU (x w : B.A) : ℕ := Nat.card {L : B.X x // w ∈ (L : Submodule K.O B.A)}
def Lin : Set (Submodule K.O B.A) :=
  {M | IsLat K.O K.E M ∧ (∀ y ∈ M, B.g * y ∈ M) ∧ ∀ y ∈ M, B.σ y ∈ M}
def sgnLat (M : Submodule K.O B.A) : ℚ :=
  let m : Fin (Module.finrank K.E B.A) → B.A :=
    Classical.epsilon fun m => Submodule.span K.O (Set.range m) = M
  K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
    Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det
def GG (u : B.A) : ℚ :=
  ∑ᶠ M ∈ {M ∈ B.Lin | u ∈ M ∧ ∀ z ∈ M, Algebra.trace K.E B.A z ∈ (algebraMap K.O K.E).range}, B.sgnLat M
def rho (w : B.A) : ℕ :=
  Nat.card {k : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
    IsIntegral K.O ((((Quotient.out k : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A)}
def LieReg : Prop := B.σ B.g = B.g ∧ B.P.Separable
def Plus (x : B.A) : Prop := IsUnit x ∧ B.σ x = x
def LinLim (a : K.O) (x : B.A) (ℓ : ℝ) : Prop :=
  Tendsto (fun k : ℕ => (B.GG (x * algebraMap K.O B.A a ^ (2 * k)) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
    atTop (𝓝 ℓ)
end InvAlg
def UQ.Small (K : UQ) (a : K.O) : Prop :=
  a ≠ 0 ∧ a ∈ IsLocalRing.maximalIdeal K.O ∧ K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a
def CountIdentity : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ x w : B.A, B.Plus x → IsUnit w →
    B.GG (x * (w * B.σ w)) = (B.UU x w : ℚ)
def UnitaryLimit : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ x : B.A, B.Plus x →
    Tendsto (fun k : ℕ => (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
      atTop (𝓝 (B.N x : ℝ))
def LinearDescent : Prop :=
  ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable →
    ∀ a : K.O, K.Small a → ∀ (ℓ : (B₁.prod B₂).A → ℝ) (ℓ₁ : B₁.A → ℝ) (ℓ₂ : B₂.A → ℝ),
    (∀ x, (B₁.prod B₂).Plus x → (B₁.prod B₂).LinLim a x (ℓ x)) →
    (∀ x, B₁.Plus x → B₁.LinLim a x (ℓ₁ x)) → (∀ x, B₂.Plus x → B₂.LinLim a x (ℓ₂ x)) →
    ∑ᶠ k : (B₁.prod B₂).Cl, (K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) : ℝ) * ℓ k.rep =
      (-(K.q : ℝ)) ^ (val K.O (resultant B₁.P B₂.P)) *
        ((∑ᶠ k : B₁.Cl, (K.eta (Algebra.norm K.E k.rep) : ℝ) * ℓ₁ k.rep) * ∑ᶠ k : B₂.Cl, ℓ₂ k.rep)
end GlobalTheory.UnitLemma


