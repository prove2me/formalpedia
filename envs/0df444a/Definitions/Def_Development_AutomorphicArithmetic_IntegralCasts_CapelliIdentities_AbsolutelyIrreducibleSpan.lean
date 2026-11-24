-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AbsolutelyIrreducibleSpan
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AbsolutelyIrreducibleSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:55.191738+00:00
-- url     : https://prove2.me/theorems/84cb52f2-940c-4b98-b38a-f3258417d320
-- title:
--   Absolutely Irreducible Span
-- statement:
--   Definitions and structural lemmas for Absolutely Irreducible Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AbsolutelyIrreducibleSpan.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr.{u_1, u_2, u_3} :
    {k : Type u_1} → [Field k] → {n : Type u_2} → [Fintype n] → [DecidableEq n] → {G : Type u_3} → (G → Matrix n n k) → Prop :=
    fun {k : Type u_1} [Field k] {n : Type u_2} [Fintype n] [DecidableEq n] {G : Type u_3} (ρ : G → Matrix n n k) ↦
      (∀ (W : Submodule k (n → k)), (∀ (g : G), ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
        ∀ (M : Matrix n n k), (∀ (g : G), M * ρ g = ρ g * M) → ∃ (c : k), M = c • (1 : Matrix n n k)
noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan :
    Prop :=
    ∀ (O : Type) [inst : CommRing O] [inst_1 : IsLocalRing O] (n : Type) [inst_2 : Fintype n] [inst_3 : DecidableEq n]
      (G : Type) [inst_4 : Monoid G] (ρ : G →* Matrix n n O),
      (UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr fun (g : G) ↦
          ((ρ : G → Matrix n n O) g).map (⇑(IsLocalRing.residue O) : O → IsLocalRing.ResidueField O)) →
        Submodule.span O (Set.range (⇑ρ : G → Matrix n n O)) = ⊤


