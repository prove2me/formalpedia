-- Prove2me | Definitions.Def_CK_CKLaneC3_CompactCoverF
-- name    : CK_CKLaneC3_CompactCoverF
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:55:59.709644+00:00
-- url     : https://prove2.me/theorems/a14fee63-dda2-4bcf-aa64-1f99c0af0153
-- title:
--   Courtade–Kumar proof module `CKLaneC3.CompactCoverF` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.CompactCoverF` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.CompactCoverF` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.CompactCoverF (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/CompactCoverF.lean)

import Definitions.Def_CK_CKLaneC3_SlopeChainF
import Definitions.Def_CK_CKLaneC3_CompactCover

-- ===== source module CKLaneC3.CompactCoverF =====
section

/-!
# Lane C3 — cell checks and the cover theorem over memoised chains

`checkF T F w` is `CellW.check T w` evaluated with `chainJetF T F` in place of `chainJet T`.
Under `FullValid T F` the two Boolean checks are equal (`checkF_eq`), so the cover theorem
`positive_of_cover` transfers verbatim (`positive_of_coverF`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.CompactCoverF

open GeneralCK GeneralCK.Certificates
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry E8TAxisRationalTreeBridgeKernel
open E8CompactAnchorInterval
open CKLaneC3.SlopeTable CKLaneC3.SlopeChain CKLaneC3.SlopeChainF CKLaneC3.CompactCell
open CKLaneC3.CompactCover

/-- `CellW.boxes`, parametric in the chain evaluator. -/
def boxesWith (ch : List (ℕ × ℕ) → ℚ → ℚ → Option (DyadicJet5Enclosure P)) (w : CellW) :
    Option (Boxes P × Boxes P) :=
  match ch [w.ra] w.cT w.cT, ch [w.rb] (2 * w.cS + w.cT) (2 * w.cS + w.cT),
      ch [w.rc] (w.cS + w.cT) (w.cS + w.cT), ch [w.rd] w.cS w.cS,
      ch w.wa w.t0 w.t1, ch w.wb (2 * w.s0 + w.t0) (2 * w.s1 + w.t1),
      ch w.wc (w.s0 + w.t0) (w.s1 + w.t1), ch w.wd w.s0 w.s1 with
  | some a, some b, some c, some d, some a', some b', some c', some d' =>
    some (⟨a, b, c, d⟩, ⟨a', b', c', d'⟩)
  | _, _, _, _, _, _, _, _ => none

/-- `CellW.check`, parametric in the chain evaluator. -/
def checkWith (ch : List (ℕ × ℕ) → ℚ → ℚ → Option (DyadicJet5Enclosure P)) (w : CellW) : Bool :=
  decide (w.s0 ≤ w.cS) && decide (w.cS ≤ w.s1) && decide (w.t0 ≤ w.cT) && decide (w.cT ≤ w.t1) &&
  (match boxesWith ch w with
   | some (pc, bb) =>
     (replay pc bb (offBox (w.s0 - w.cS) (w.s1 - w.cS))
       (offBox (w.t0 - w.cT) (w.t1 - w.cT))).positiveCheck
   | none => false)

theorem check_eq_checkWith (T : List (List Piece)) (w : CellW) :
    w.check T = checkWith (chainJet T) w := rfl

/-- The cell check over memoised chains. -/
def checkF (T : List (List Piece)) (F : JTable) (w : CellW) : Bool := checkWith (chainJetF T F) w

theorem checkF_eq {T : List (List Piece)} {F : JTable} (hF : FullValid T F) (w : CellW) :
    checkF T F w = w.check T := by
  rw [check_eq_checkWith, checkF, chainJetF_fun hF]

def tagOKF (T : List (List Piece)) (F : JTable) : Tag → Bool
  | .inl q => decide (q.s1 + q.t1 ≤ 2 / 25)
  | .inr w => checkF T F w

theorem tagOKF_eq {T : List (List Piece)} {F : JTable} (hF : FullValid T F) :
    tagOKF T F = tagOK T := by
  funext g
  cases g with
  | inl q => rfl
  | inr w => exact checkF_eq hF w

theorem positive_of_coverF {T : List (List Piece)} (hT : TableValid T) {F : JTable}
    (hF : FullValid T F) {tree : Tree} {D : RatRect} {L : List Tag}
    (horigin : E8PositiveOn fun s t => s + t ≤ 2 / 25)
    (hv : qValid tree D) (hleaves : qLeaves tree D = L.map tagRect)
    (hok : L.all (tagOKF T F) = true) :
    ∀ s t : ℝ, E8Admissible s t → D.real.Covers s t → 0 < e8Delta e8Q s t := by
  rw [tagOKF_eq hF] at hok
  exact positive_of_cover hT horigin hv hleaves hok

end CKLaneC3.CompactCoverF

#print axioms CKLaneC3.CompactCoverF.checkF_eq
#print axioms CKLaneC3.CompactCoverF.positive_of_coverF

end


