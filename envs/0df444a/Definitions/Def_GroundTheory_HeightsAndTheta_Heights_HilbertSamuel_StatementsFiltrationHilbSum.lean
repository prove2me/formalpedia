-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:27.130174+00:00
-- url     : https://prove2.me/theorems/08cd65c2-88d8-4e34-9673-6bac4ccab1c6
-- title:
--   Statements Filtration Hilb Sum
-- statement:
--   Definitions and structural lemmas for Statements Filtration Hilb Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsFiltrationHilbSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
def FiltrationHilbSum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    ∀ (n : ℕ) (N : Fin (n + 1) → Submodule (MRing ι F) M) (x : Fin n → M) (c : Fin n → K → ℤ)
      (q : Fin n → Ideal (MRing ι F)),
      N 0 = ⊥ → N (Fin.last n) = ⊤ →
      (∀ j : Fin n, x j ∈ piece (c j) ∧
        N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} ∧
        ∀ s : MRing ι F, s • x j ∈ N j.castSucc ↔ s ∈ q j) →
      ∀ m : K → ℤ, (Module.finrank F (piece m) : ℤ) = ∑ j, hilbFn (q j) (m - c j)
section Examples
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
end Examples
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


