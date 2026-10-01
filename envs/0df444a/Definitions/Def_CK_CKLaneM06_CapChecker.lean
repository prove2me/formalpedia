-- Prove2me | Definitions.Def_CK_CKLaneM06_CapChecker
-- name    : CK_CKLaneM06_CapChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:25:14.965774+00:00
-- url     : https://prove2.me/theorems/0b68b26f-ee33-4bc4-b69e-b79b499b766f
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapChecker.lean)

import Definitions.Def_CK_CKLaneM06_CapBounds

-- ===== source module CKLaneM06.CapChecker =====
section

/-!
# Lane M06: reflective Boolean checker for cap boxes (theorem (5))

A certificate is a closed rational mean box `B = [a0,a1] × [b0,b1]` with `a1 ≤ 1/2` and either
`b1 ≤ 1/2` (same-side) or `1/2 ≤ b0` (cross-half), a depth `S`, and a witness `w`
(two slope anchors `vS, vI`, a slope choice `plane`, and a log-sum constant `kap`).

`check B S w = true` certifies `CapOn B S`: every finite interior law with `a < b`, `a + b ≤ 1`,
means in `B` and mean deficit `s ≤ S` satisfies `ζ ≥ R_ψ` (`candidateGap psi ≤ cost`), for every
feasible entropy split.  Acceptance (archive criterion (3), RESTORED_CAP_PROOF.md §2, with the
sextic bonus of §5 truncated):

    K · max(0, pbar - 4) ≤ W + lam · S

* `K ≥ Δ/d²` (`min(DHi/dLo², K6)`, `K6` = lane E quartic-exact normalized bound),
* `W ≤ (j - 4Δ)/d²` (sextic bonus `interiorCost_sub_four_drop6`),
* `lam ≤ λ/d²` : kappa log-sum slope (M07) or mean-contact plane slope (corpus Theorem 3.10),
* `pbar ≥ (P'(S) + P'(S + Δ))/2` (lane E slope anchors).
Every enclosure is recomputed by the kernel from the box (lane E `FastPoint` rational log/H bounds).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM06.Cap

open GeneralCK CKLaneE.FP

/-- A closed rational mean box `[a0,a1] × [b0,b1]`. -/
structure CBox where
  a0 : ℚ
  a1 : ℚ
  b0 : ℚ
  b1 : ℚ
  deriving DecidableEq, Repr

/-- The cap claim on a mean box at depth `S` (canonical laws, strictly ordered means). -/
def CapOn (B : CBox) (S : ℚ) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → μ.a + μ.b ≤ 1 →
    (B.a0 : ℝ) ≤ μ.a → μ.a ≤ (B.a1 : ℝ) → (B.b0 : ℝ) ≤ μ.b → μ.b ≤ (B.b1 : ℝ) →
    (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ (S : ℝ) →
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-- Witness: slope anchors, slope choice, log-sum constant.  No margin is stored. -/
structure CWit where
  vS : ℚ
  vI : ℚ
  plane : Bool
  kap : ℚ
  deriving DecidableEq, Repr

namespace CBox

variable (B : CBox)

def HaLo : ℚ := Hlo B.a0
def HbLo : ℚ := if B.b1 ≤ 1 / 2 then Hlo B.b0 else Hlo B.b1
def mq : ℚ := (B.a1 + B.b1) / 2
def HmHi : ℚ := if B.mq ≤ 1 / 2 then Hhi B.mq else 1
def DHi : ℚ := B.HmHi - (B.HaLo + B.HbLo) / 2
def dLo : ℚ := if B.a1 < B.b0 then B.b0 - B.a1 else 0
def dHi : ℚ := B.b1 - B.a0
def mL : ℚ := (B.a0 + B.b0) / 2
def mH : ℚ := (B.a1 + B.b1) / 2
def rhoH : ℚ := B.dHi / (B.a0 + B.b0)
def kapH : ℚ := B.dHi / (2 - B.a1 - B.b1)
def rhoL : ℚ := B.dLo / (B.a1 + B.b1)
def kapL : ℚ := B.dLo / (2 - B.a0 - B.b0)
def K6 : ℚ :=
  ((1 + B.rhoH ^ 2 / 6 + 2 / 5 * B.rhoH ^ 4) / B.mL +
    (1 + B.kapH ^ 2 / 6 + 2 / 5 * B.kapH ^ 4) / (1 - B.mH)) / (8 * LqLo)
def K1 : ℚ := B.DHi / (B.dLo * B.dLo)
def K : ℚ := if 0 < B.dLo ∧ B.K1 ≤ B.K6 then B.K1 else B.K6
def W : ℚ :=
  ((B.rhoL ^ 2 + 4 / 5 * B.rhoL ^ 4) / B.mH + (B.kapL ^ 2 + 4 / 5 * B.kapL ^ 4) / (1 - B.mL)) /
    (12 * LqHi)
def m11l : ℚ := -lHi B.a1
def m11h : ℚ := -lLo B.a0
def m12l : ℚ := -lHi B.b1
def m12h : ℚ := -lLo B.b0
def m21l : ℚ := -l1Hi B.a0
def m21h : ℚ := -l1Lo B.a1
def m22l : ℚ := -l1Hi B.b0
def m22h : ℚ := -l1Lo B.b1
def detL : ℚ := B.m11l * B.m22l - B.m12h * B.m21h
def detH : ℚ := B.m11h * B.m22h - B.m12l * B.m21l
def nAL : ℚ := B.m22l / (2 * B.a1 * B.b1) - B.m12h / (2 * (1 - B.a1) * (1 - B.b1))
def nDL : ℚ := B.m11l / (2 * (1 - B.a0) * (1 - B.b0)) - B.m21h / (2 * B.a0 * B.b0)
def planeL : ℚ := if B.nAL ≤ B.nDL then B.nAL / B.detH else B.nDL / B.detH

def planeOk : Bool :=
  decide (0 ≤ B.m11l ∧ 0 ≤ B.m12l ∧ 0 ≤ B.m21l ∧ 0 ≤ B.m22l ∧ 0 < B.detL ∧ 0 < B.nAL ∧ 0 < B.nDL)

def kapOk (κ : ℚ) : Bool :=
  decide (0 ≤ κ ∧ κ ≤ 2 ∧ κ * (-l1Lo B.a1) ≤ B.a0 / (1 - B.a0) ∧ κ * (-lLo B.a0) ≤ (1 - B.a1) / B.a1 ∧
    κ * (-l1Lo B.b1) ≤ B.b0 / (1 - B.b0) ∧ κ * (-lLo B.b0) ≤ (1 - B.b1) / B.b1)

def boxOk : Bool :=
  decide (0 < B.a0 ∧ B.a0 ≤ B.a1 ∧ B.a1 ≤ 1 / 2 ∧ 0 < B.b0 ∧ B.b0 ≤ B.b1 ∧ B.b1 < 1 ∧
      (B.b1 ≤ 1 / 2 ∨ 1 / 2 ≤ B.b0)) &&
    ptOk B.a0 && ptOk B.a1 && ptOk B.b0 && ptOk B.b1 && (decide (1 / 2 < B.mq) || ptOk B.mq)

end CBox

def CWit.lam (w : CWit) (B : CBox) : ℚ :=
  if w.plane then 2 * B.planeL else w.kap / (2 * B.b1 * (1 - B.a0))

def CWit.slopeOk (w : CWit) (B : CBox) : Bool :=
  if w.plane then B.planeOk else B.kapOk w.kap

def pbar (w : CWit) : ℚ := (P1up w.vS + P1up w.vI) / 2

def excess (w : CWit) : ℚ := if 0 ≤ pbar w - 4 then pbar w - 4 else 0

/-- The Boolean checker of one cap box at depth `S`. -/
def check (B : CBox) (S : ℚ) (w : CWit) : Bool :=
  B.boxOk && decide (0 ≤ S ∧ S + B.DHi < 1) &&
    anchorOk w.vS S && anchorOk w.vI (S + B.DHi) && w.slopeOk B &&
    decide (0 ≤ B.K ∧ B.K * excess w ≤ B.W + w.lam B * S)

end CKLaneM06.Cap

end


