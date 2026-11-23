-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
-- name    : Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:10.586606+00:00
-- url     : https://prove2.me/theorems/fbc2b3ca-3489-4868-9830-e64e8382eadb
-- title:
--   Split Pair Gen
-- statement:
--   Definitions and structural lemmas for Split Pair Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/SplitPairGen.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
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
namespace Formalism.L2.PairingIndexBounds.Eq.SqG
def stdHG (E : Type) [Field E] [StarRing E] (N : ℕ) (x y : Fin N → E) : E := ∑ i, star (x i) * y i
def IsSDG (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, stdHG E N x y ∈ (algebraMap (𝓞 E) E).range
def SplitPairGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ n : 𝓞 E, n ≠ 0 → ∃ e : Matrix (Fin N) (Fin N) E,
        (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
        ∀ M ∈ ({e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)} : Set (Matrix (Fin N) (Fin N) E)),
          ∀ y, (y ∈ L' ∨ y ∈ L'') → ∃ m, m ∈ L' ∧ m ∈ L'' ∧ M *ᵥ y = (n : E) • m
end Formalism.L2.PairingIndexBounds.Eq.SqG


