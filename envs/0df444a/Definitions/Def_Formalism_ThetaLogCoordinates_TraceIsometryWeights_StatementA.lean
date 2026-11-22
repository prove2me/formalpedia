-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:50.908138+00:00
-- url     : https://prove2.me/theorems/d5456c6f-8f39-40a5-bb96-db9506e9cc76
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/StatementA.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DivStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Finset
def InvInv : Prop :=
  ∀ (K W ι : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [DecidableEq ι]
    (E : ι → ι → Module.End K W), GlRel E → ∀ (l : ℕ) (NN : Submodule K W),
    (∀ a b, ∀ x ∈ NN, E a b x ∈ NN) →
    (∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0) →
    ∀ L : List ι, L.Nodup → ∀ u ∈ NN, (∀ a ∈ L, E a a u = 0) →
      (∀ a ∈ L, ∀ b ∈ L, E a b (InvOp E l L u) = 0) ∧ InvOp E l L u ∈ NN ∧
      InvOp E l L u - u ∈ ⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (E a b)
def InvNat : Prop :=
  ∀ (K W W' ι : Type) [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] [DecidableEq ι]
    (E : ι → ι → Module.End K W) (E' : ι → ι → Module.End K W') (θ : W →ₗ[K] W'),
    (∀ a b x, θ (E a b x) = E' a b (θ x)) → ∀ (l : ℕ) (L : List ι) (x : W),
      θ (InvOp E l L x) = InvOp E' l L (θ x)
def InvInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W ι : Type) [AddCommGroup W] [Module ℚ_[p] W] [DecidableEq ι]
    (E : ι → ι → Module.End ℚ_[p] W), GlRel E → ∀ (M : AddSubgroup W), ZpClosed p M → DivStable E M →
    ∀ (l : ℕ) (L : List ι), L.Nodup → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (L.length.choose 2 * Nat.log p (l + L.length - 1))) • InvOp E l L u ∈ M
def HomRel : Prop :=
  ∀ (K V W ι : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]
    (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W), GlRel EV → GlRel EW → GlRel (homAct EV EW)
def HomDiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V W ι : Type) [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup W] [Module ℚ_[p] W]
    [DecidableEq ι] (EV : ι → ι → Module.End ℚ_[p] V) (EW : ι → ι → Module.End ℚ_[p] W)
    (L : AddSubgroup V) (M : AddSubgroup W), ZpClosed p M → DivStable EV L → DivStable EW M →
      ZpClosed p (HomLat (K := ℚ_[p]) L M) ∧ DivStable (homAct EV EW) (HomLat (K := ℚ_[p]) L M)
def HomTrace : Prop :=
  ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [DecidableEq ι]
    (EV : ι → ι → Module.End K V) (ψ : V →ₗ[K] V),
    ψ ∈ (⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (homAct EV EV a b)) → LinearMap.trace K V ψ = 0
end Formalism.InvariantFactorPaths.PW


