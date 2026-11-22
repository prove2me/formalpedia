-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
-- name    : Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:16:07.94913+00:00
-- url     : https://prove2.me/theorems/5f26d6e9-69e8-4b4f-a6bd-48c353419c8c
-- title:
--   Substitution Bound
-- statement:
--   Definitions and structural lemmas for Substitution Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.CyclotomicNorms
namespace SubstitutionExponents
variable {r : ℕ}
def weight (n : Fin r → ℕ) (d : Fin r →₀ ℕ) : ℕ := ∑ i, d i * n i
def revLex : (Fin r →₀ ℕ) → (Fin r →₀ ℕ) → Prop :=
  Finsupp.Lex (· > ·) (· < ·)
end SubstitutionExponents
end Formalism.CyclotomicNorms


