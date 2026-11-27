-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-27T05:16:48.53417+00:00
-- url     : https://prove2.me/theorems/9b26f257-d1a8-5aa6-91a4-1e39233f5cba
-- title:
--   Up Mk Apply Inl
-- statement:
--   Definitions and structural lemmas for Up Mk Apply Inl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UpMkApplyInl.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
noncomputable def upMk {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ)) :
    UXVar D N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun p => ab.2 (some p)) (fun i => ab.1 i))
noncomputable def upMono (D N n n' : ℕ) : Finset (UXVar D N →₀ ℕ) :=
  ((Finset.univ : Finset (Fin (D + 2))).finsuppAntidiag n ×ˢ
    (Finset.univ : Finset (Option (Fin (D + 2) × Fin (N + 1)))).finsuppAntidiag n').image upMk
end ReciprocityTheory.ChartRestriction.G.T0


