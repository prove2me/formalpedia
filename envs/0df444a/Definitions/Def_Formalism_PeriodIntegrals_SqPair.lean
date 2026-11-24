-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SqPair
-- name    : Formalism_PeriodIntegrals_SqPair
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T20:58:17.231942+00:00
-- url     : https://prove2.me/theorems/22767434-c3ca-47e3-8715-d88f5a4b0648
-- title:
--   Sq Pair
-- statement:
--   Definitions and structural lemmas for Sq Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SqPair.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.SqPair
open Formalism.L2.PairingIndexBounds.Eq.SqG
def PLocal (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L' L'' : Submodule (𝓞 E) (Fin N → E)) (n : 𝓞 E) (p : ℕ) : Prop :=
  ∃ e : Matrix (Fin N) (Fin N) E,
    (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
    ∀ M ∈ ({e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)} : Set (Matrix (Fin N) (Fin N) E)),
      ∀ y, (y ∈ L' ∨ y ∈ L'') →
        ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ ∃ m, m ∈ L' ∧ m ∈ L'' ∧ (s : E) • (M *ᵥ y) = (n : E) • m
def PLocalAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ n : 𝓞 E, n ≠ 0 → ∀ p : ℕ, p.Prime → PLocal E N L' L'' n p
def LocCartanPair : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R ≃+* R), (∀ x, σ (σ x) = x) →
    ∀ (R₀ : Subring R), (∀ x, x ∈ R₀ ↔ σ x = x) →
    ∀ [IsDomain R₀] [IsDiscreteValuationRing R₀] [HenselianLocalRing R₀]
      [Finite (IsLocalRing.ResidueField R₀)],
    (∃ θ : R, IsUnit (θ - σ θ)) →
    ∀ ϖ : R₀, Irreducible ϖ →
    ∀ (N : ℕ), Even N → ∀ (k : ℕ) (h : Matrix (Fin N) (Fin N) R),
      (h.map σ)ᵀ * h = ((ϖ : R) ^ (2 * k)) • (1 : Matrix (Fin N) (Fin N) R) →
      ∃ e f : Matrix (Fin N) (Fin N) R, e * e = e ∧ (e.map σ)ᵀ = 1 - e ∧ e * h = h * f
end PI.SqPair


