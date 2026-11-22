-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:19.698812+00:00
-- url     : https://prove2.me/theorems/eb57e015-93e5-4bc1-b603-38b832adbbb9
-- title:
--   Tail Concavity
-- statement:
--   Definitions and structural lemmas for Tail Concavity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean

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
open Finset
namespace Formalism.G0
namespace TailConcavityP
def g (k : ℕ) (b : ℝ) : ℝ := ∑ i ∈ range k, 1 / (b + i + 1)
def cn (k N : ℕ) (B : Fin N → ℕ) (l : ℕ) : ℝ :=
  if h : l < N then g k (B ⟨l, h⟩) else 0
def en (k N : ℕ) (B : Fin N → ℕ) (u : ℕ) : ℝ :=
  cn k N B u - (if u = 0 then 0 else cn k N B (u - 1))
end TailConcavityP
end Formalism.G0


