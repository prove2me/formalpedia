-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_StatementCor
-- name    : Formalism_HarderNarasimhan_StatementCor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:20.920629+00:00
-- url     : https://prove2.me/theorems/5b5523a4-b8a7-47af-b834-c6af132a52ea
-- title:
--   Statement Cor
-- statement:
--   Definitions and structural lemmas for Statement Cor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/StatementCor.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
namespace Formalism.HN
def HNCor : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L →
    Antitone (hnStep ρ L) ∧
    (L ≠ ⊥ → ∀ θ : ℝ, hnStep ρ L θ = L ↔ θ ≤ muMin ρ L) ∧
    (∀ θ : ℝ, muMax ρ L < θ → hnStep ρ L θ = ⊥) ∧
    (∀ t : ℝ, (Finset.univ.filter (fun j => slopeList ρ L j < t)).card =
      rk ρ L - rk ρ (hnStep ρ L t)) ∧
    (∀ N : Submodule R V, N ≤ L → N ≠ ⊥ → muMax ρ N ≤ muMax ρ L) ∧
    (∀ (N : Submodule R V) (θ : ℝ), N ≤ L → N ≠ ⊥ → θ ≤ muMin ρ N →
      rk ρ N ≤ (Finset.univ.filter (fun j => θ ≤ slopeList ρ L j)).card)
def ImageStep : Prop :=
  ∀ (R ι W F : Type*) [Ring R] [AddCommGroup W] [Module R W] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (V E : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (ρ : ∀ i, V i →+ E i) (ρ' : W →+ F) (L : ∀ i, Submodule R (V i)) (M : Submodule R W)
    (s : Finset ι) (φ : ∀ i, L i →ₗ[R] M) (C : ι → ℝ) (θ : ℝ),
    (∀ i ∈ s, IsLat (ρ i) (L i)) → IsLat ρ' M →
    (∀ i ∈ s, 0 < C i ∧ (∀ x : L i, ‖ρ' (φ i x : W)‖ ≤ C i * ‖ρ i (x : V i)‖) ∧
      (L i ≠ ⊥ → θ ≤ muMin (ρ i) (L i) - Real.log (C i))) →
    (⨆ i ∈ s, (LinearMap.range (φ i)).map M.subtype) ≤ hnStep ρ' M θ
end Formalism.HN


