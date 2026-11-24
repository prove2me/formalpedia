-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAll
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:39.2608+00:00
-- url     : https://prove2.me/theorems/8c4edbbe-1be2-4dc8-8da0-02aa34d83be4
-- title:
--   PTrans All
-- statement:
--   Definitions and structural lemmas for PTrans All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAll.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz
namespace TA
def TAk (N : ℕ) : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (E : ι → Fin n → Fin n → Module.End ℂ M), (∀ τ, GlRel (E τ)) →
  (∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) →
  ∀ (l : ι → Fin n → ℤ), (∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → (∀ τ, IsWh (E τ) ℓ) →
  ∀ (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = N →
  ∀ (lab : P → ι) (C : Type) [DecidableEq C] (col : P → C) (b co : P → Fin n),
    (∀ p q, col p = col q → lab p = lab q) → IsTab col b → (∀ p q, col p = col q → co p = co q → p = q) →
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S)
end TA
end PositivityTheory.Rg.Cz
end


