-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchurIrreducible
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchurIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:49.59896+00:00
-- url     : https://prove2.me/theorems/17e34794-4938-4454-9532-1f9ba63312ec
-- title:
--   Schur Irreducible
-- statement:
--   Definitions and structural lemmas for Schur Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchurIrreducible.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.SchurIrreducible.Irr :
    {G : Type} → [inst : Group G] → {N : ℕ} → (G →* GL (Fin N) ℂ) → Prop :=
    fun {G : Type} [Group G] {N : ℕ} (ρ : G →* GL (Fin N) ℂ) ↦
      ∀ (S : Submodule ℂ (Fin N → ℂ)),
        (∀ (g : G), ∀ v ∈ S, (↑((ρ : G → GL (Fin N) ℂ) g) : Matrix (Fin N) (Fin N) ℂ).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤
noncomputable def UpperTheory.Reformulated.B.SchurIrreducible.SchurStep :
    Prop :=
    ∀ (G : Type) [inst : Group G] (M : ℕ) (σ : G →* GL (Fin M) ℂ),
      UpperTheory.Reformulated.B.SchurIrreducible.Irr σ →
        ∀ (C : Matrix (Fin M) (Fin M) ℂ),
          (∀ (g : G),
              (↑((σ : G → GL (Fin M) ℂ) g) : Matrix (Fin M) (Fin M) ℂ) * C =
                C * (↑((σ : G → GL (Fin M) ℂ) g) : Matrix (Fin M) (Fin M) ℂ)) →
            ∃ (c : ℂ), C = c • (1 : Matrix (Fin M) (Fin M) ℂ)


