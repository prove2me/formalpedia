-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
-- name    : Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:16.333805+00:00
-- url     : https://prove2.me/theorems/af0b749f-bdb2-436d-9579-e4b24f1cee29
-- title:
--   Smul Sub Mul Le
-- statement:
--   Definitions and structural lemmas for Smul Sub Mul Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
namespace Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]
def smulSub (k : ℕ) (H : AddSubgroup W) : AddSubgroup W := H.map (nsmulAddMonoidHom k)
abbrev Qt (k : ℕ) (H : AddSubgroup W) : Type _ := ↥H ⧸ (smulSub k H).addSubgroupOf H
def IsInv (k : ℕ) (H : AddSubgroup W) (g : W → ℂ) : Prop := ∀ t ∈ H, ∀ u ∈ H, g (t + k • u) = g t
def avg (k : ℕ) (H : AddSubgroup W) (g : W → ℂ) : ℂ :=
  (Nat.card (Qt k H) : ℂ)⁻¹ * ∑ᶠ q : Qt k H, g ((q.out : H) : W)
open Classical in

def integ (H : AddSubgroup W) (g : W → ℂ) : ℂ :=
  if h : ∃ k, 0 < k ∧ IsInv k H g then avg h.choose H g else 0
section Integ
variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin
end Integ
end Formalism.IndefR.Fin.Four
end


