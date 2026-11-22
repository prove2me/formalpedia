-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:12:31.79598+00:00
-- url     : https://prove2.me/theorems/7c3d7b95-b79b-47d8-bda6-c3e6a588b43f
-- title:
--   Subspace Count
-- statement:
--   Definitions and structural lemmas for Subspace Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/SubspaceCount.lean

import Definitions.Def_Formalism_SubspaceCounting_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
namespace Formalism.G0
namespace SubspaceCountP
def P (q : ℤ) (m k : ℕ) : ℤ := ∏ i ∈ Finset.range k, (q ^ m - q ^ i)
end SubspaceCountP
namespace SubspaceCountP
abbrev LI (F V : Type) [Field F] [AddCommGroup V] [Module F V] (k : ℕ) :=
  {s : Fin k → V // LinearIndependent F s}
abbrev Gr (F W : Type) [Field F] [AddCommGroup W] [Module F W] (k : ℕ) :=
  {U : Submodule F W // finrank F U = k}
variable {F W : Type} [Field F] [AddCommGroup W] [Module F W]
def spanMap (k : ℕ) (s : LI F W k) : Gr F W k :=
  ⟨Submodule.span F (Set.range s.1), (finrank_span_eq_card s.2).trans (Fintype.card_fin k)⟩
variable [Finite W]
def fiberEquiv (k : ℕ) (U : Gr F W k) : {s : LI F W k // spanMap k s = U} ≃ LI F U.1 k where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      have h := congrArg Subtype.val s.2
      simp only [spanMap] at h
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩⟩, by
      apply LinearIndependent.of_comp U.1.subtype
      exact s.1.2⟩
  invFun t := ⟨⟨U.1.subtype ∘ t.1, t.2.map' _ (Submodule.ker_subtype _)⟩, by
      apply Subtype.ext
      apply Submodule.eq_of_le_of_finrank_eq
      · show Submodule.span F (Set.range (U.1.subtype ∘ t.1)) ≤ U.1
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (t.1 i).2
      · rw [(spanMap k _).2, U.2]⟩
  left_inv s := rfl
  right_inv t := rfl
end SubspaceCountP
namespace SubspaceCountP
variable {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W]
end SubspaceCountP
end Formalism.G0


