-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SobLeafP
-- name    : Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SobLeafP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:22:35.885134+00:00
-- url     : https://prove2.me/theorems/5544dbc3-5df3-4994-823a-4e6868578c58
-- title:
--   Sob Leaf P
-- statement:
--   Definitions and structural lemmas for Sob Leaf P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HaarTransfer/SobLeafP.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace
namespace Formalism.IndefR.Leaf.HaarTransferContinuity
variable (F : Type) [Field F] [NumberField F]
abbrev W := ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // ¬ v.IsReal} → ℂ)
noncomputable def E (x : InfiniteAdeleRing F) : W F :=
  (fun v => Completion.extensionEmbeddingOfIsReal v.2 (x v.1),
   fun v => Completion.extensionEmbedding v.1 (x v.1))
open scoped Classical in
noncomputable def G (w : W F) : InfiniteAdeleRing F := fun v =>
  if h : v.IsReal then (Completion.isometryEquivRealOfIsReal h).symm (w.1 ⟨v, h⟩)
  else (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp h)).symm (w.2 ⟨v, h⟩)
end Formalism.IndefR.Leaf.HaarTransferContinuity


