-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:52.956821+00:00
-- url     : https://prove2.me/theorems/e7dea5e9-fa67-415d-a101-10f7c0a0da1a
-- title:
--   Xi Plucker Rel
-- statement:
--   Definitions and structural lemmas for Xi Plucker Rel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/XiPluckerRel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace ProjectiveLineBundle
variable {D : ℕ} (S : ProjectiveLineBundle D)
def pluckerWW (k m : S.κ) : MRing S.WIdx :=
  X ⟨.line0, k⟩ * X ⟨.line1, m⟩ - X ⟨.line0, m⟩ * X ⟨.line1, k⟩
def IsPluckerRel (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx) : Prop :=
  (∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3))) ∧
    ∀ i l k m, S.g * rename (T.yyEmb 0) (F i l k m) -
      S.h * S.pluckerWW k m * X ⟨.det, l⟩ * X ⟨.base, i⟩ ^ N ∈ S.WW
end ProjectiveLineBundle
def PluckerRel.Statement : Prop :=
  ∀ (D : ℕ) (S : ProjectiveLineBundle D), ∃ (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx), S.IsPluckerRel N F
section Inhabit
def exPluckerF : Unit → Unit → Unit ⊕ Unit → Unit ⊕ Unit → MRing ExY
  | _, _, .inl _, .inr _ => X ⟨.base, ()⟩ ^ 3
  | _, _, .inr _, .inl _ => -X ⟨.base, ()⟩ ^ 3
  | _, _, _, _ => 0
end Inhabit
end
end GroundTheory.Heights₂.Heights.Inter


