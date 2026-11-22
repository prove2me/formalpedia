-- Prove2me | Definitions.Def_Formalism_YangianSpanCharacter_StatementE
-- name    : Formalism_YangianSpanCharacter_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:49:32.221346+00:00
-- url     : https://prove2.me/theorems/69ec298a-59ea-4558-81b7-3f435a33ddb3
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/StatementE.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.YangianSpanCharacter.E
def GGRatio : Prop :=
  ∀ (g : ℝ), 1 < g → ∀ k : ℕ,
    g ^ (∑ i ∈ Finset.Ico 1 k, i) / ∏ i ∈ Finset.Ico 1 k, (g ^ i - 1) =
      ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)⁻¹
def GGProd : Prop :=
  ∀ (g : ℝ), 3 ≤ g → ∀ k : ℕ, ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)⁻¹ ≤ 1 + 3 / g
def GGBound : Prop :=
  ∀ (g : ℝ), 3 ≤ g → ∀ (k : ℕ) (dimπ : ℝ), ∏ i ∈ Finset.Ico 1 k, (g ^ i - 1) ≤ dimπ →
    g ^ (∑ i ∈ Finset.Ico 1 k, i) / dimπ ≤ 1 + 3 / g
def SpanChar : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (O : Subring K) (θ : K),
    θ ∈ O → θ ≠ 0 → ∀ (n : ℕ) (f f' : Fin n → V), LinearIndependent K (Sum.elim f f') →
    ∀ α α' : Fin n → K,
      (θ⁻¹ • (∑ i, α i • f i + ∑ i, α' i • f' i) ∈
          Submodule.span O (Set.range f ∪ Set.range (fun i => θ⁻¹ • (f' i - f i))) ↔
        ∀ i, α' i ∈ O ∧ ∃ x ∈ O, α i + α' i = θ * x)
end Formalism.YangianSpanCharacter.E


