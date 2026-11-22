-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:46.150474+00:00
-- url     : https://prove2.me/theorems/25fc5c10-91b7-43a6-aa65-babc0a19ce68
-- title:
--   LBidetdom Lemmas
-- statement:
--   Definitions and structural lemmas for LBidetdom Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
namespace Formalism.GradedWeylDivisibility
def rowPart {r n : ℕ} (k : ℕ) (m : Fin r × Fin n →₀ ℕ) : ℕ :=
  ∑ a : Fin r with a.val < k, rowDeg m a
def rowTot {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) : ℕ := ∑ a : Fin r, rowDeg m a
end Formalism.GradedWeylDivisibility


