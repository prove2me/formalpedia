-- Prove2me | Definitions.Def_MaxCompForest_Phi
-- name    : MaxCompForest_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:46.094097+00:00
-- url     : https://prove2.me/theorems/9a0e8ddb-039d-4a2b-9641-2b72a45e92ac
-- title:
--   Completion weight $\Phi_G(F)=\sum_{T\supseteq F}c(T)$
-- statement:
--   The **completion weight** of a label set $F$ is the total weight of all spanning trees containing it,
--   $$
--   \Phi_G(F)=\sum_{T\supseteq F}c(T).
--   $$
--   A cyclic set has completion weight zero, since no tree contains it.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.1, (3.1) p.14

import Mathlib
import Definitions.Def_MaxCompForest_IsSpanningTree
import Definitions.Def_MaxCompForest_weight
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

open Classical in
/-- **The completion weight** `Φ_G(F) = ∑_{T ⊇ F} c(T)`, the total weight of the spanning trees
containing `F`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.1, (3.1) p.14.

**Formalization Note.** Defined for every label set; a cyclic `F` gets `0` because no tree contains it,
without a special case. The product formula `c(F) τ_c(G/F)` is a clause of `eq_3_2_transfer_current`. -/
noncomputable def Phi (G : WGraph V E) (F : Finset E) : ℝ :=
  ∑ T ∈ Finset.univ.filter (fun T => IsSpanningTree G T ∧ F ⊆ T), weight G T

end MaxCompForest


