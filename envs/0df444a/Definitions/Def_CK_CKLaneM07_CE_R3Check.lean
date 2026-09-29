-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Check
-- name    : CK_CKLaneM07_CE_R3Check
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:08:51.151761+00:00
-- url     : https://prove2.me/theorems/1287c7a7-069e-45d3-b312-6fe594eca778
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Check` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Check` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Check` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Check (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Check.lean)

import Definitions.Def_CK_CKLaneN1_CapSlope

-- ===== source module CKLaneM07.CE.R3Check =====
section

/-!
# Lane M07 / CE-stat row 3: exact-rational box checker for the stationarity-free bound

A box is a `CKLaneN1.B3` in coordinates `(a, z, y)`: `a ∈ [a0,a1]`, `z ∈ [b0,b1] ⊂ [0,1]`,
`y ∈ [c0,c1]`, meaning `b = a + z y`, `c = a + y`.  `r3BoxOK B w` certifies, for every point of the box,
either `A = y/(H a + H b) > 1/20` (vacuous) or `gapLB (H a) (H b) c ≥ y² · Plo ≥ 0` with

`Plo = α(1 − b1²) + β b0² − T3 − T4`, where (all rational, Lane E / N1 certified bounds)
* `α = slopeLo v / X / (4 h_hi)`, `X = c1/(2 h_lo)` (ratio bound; witness `v` brackets `Θ(X)`),
* `β = 1/((2 a1 + b1 c1) log2⁺)` (interior cost),
* `T3 = slopeHi q · 2 · JH⁺ / (J_M y²)` (Jensen penalty, normalized or direct),
* `T4` = mean-value form `D (1 − b0)(2κ(1 − b0) + b1/2 + E1/J_M)` or direct
  `(slopeHi q − slopeLo t)(1 − b0)/c0`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE.R3

open CKLaneE.FP CKLaneN1 CKLaneN1.Capital

/-- witness of one row-3 box -/
structure RWit where
  v : ℚ
  q : ℚ
  t : ℚ
  mvt : Bool
  deriving Repr

section box

variable (B : B3)

def bLo : ℚ := B.a0 + B.b0 * B.c0
def bHi : ℚ := B.a1 + B.b1 * B.c1
def cHi : ℚ := B.a1 + B.c1
def MLo : ℚ := B.a0 + B.b0 * B.c0 / 2
def MHi : ℚ := B.a1 + B.b1 * B.c1 / 2
def Ha0 : ℚ := Hlo B.a0
def Ha1 : ℚ := Hhi B.a1
def Hb0 : ℚ := Hlo (bLo B)
def Hb1 : ℚ := Hhi (bHi B)
def hLo : ℚ := (Ha0 B + Hb0 B) / 2
def hHi : ℚ := (Ha1 B + Hb1 B) / 2
def Xq : ℚ := B.c1 / (2 * hLo B)
def betaQ : ℚ := 1 / ((2 * B.a1 + B.b1 * B.c1) * LqHi)
def JMq : ℚ := lamLo (MHi B) / LqHi
def rhoHi : ℚ := B.b1 * B.c1 / (2 * B.a0 + B.b1 * B.c1)
def rhopHi : ℚ := B.b1 * B.c1 / (2 * (1 - MHi B))

/-- upper bound of `C(r)/r²`, `C(r) = (1+r) log(1+r) + (1-r) log(1-r)` -/
def chatHi (r : ℚ) : ℚ := ((1 + r) * (-l1Lo (r / (1 + r))) + (1 - r) * l1Hi r) / r ^ 2

/-- `JH ≤ (b − a)² · JHn` -/
def JHn : ℚ := (chatHi (rhoHi B) / MLo B + chatHi (rhopHi B) / (1 - MHi B)) / (8 * LqLo)
/-- `JH ≤ JHd` -/
def JHd : ℚ := Hhi (MHi B) - (Ha0 B + Hb0 B) / 2
/-- the box maximum of `JH` -/
def JHup : ℚ := if 0 < B.c0 then min (B.b1 ^ 2 * B.c1 ^ 2 * JHn B) (JHd B) else B.b1 ^ 2 * B.c1 ^ 2 * JHn B

def kappaQ : ℚ := Hhi (cHi B) / ((1 - 2 * cHi B) * (lamLo (cHi B) / LqHi) + 2 * Hb0 B)
def DQ (q : ℚ) : ℚ :=
  HnumHi (cHi B) * (2 * kapHiQ q) / (4 * LqLo * q ^ 2 * (1 - cHi B) ^ 2 * kapLoQ (cHi B) ^ 2)

def T3q (q : ℚ) : ℚ :=
  if 0 < B.c0 then min (slopeHi q * 2 * (B.b1 ^ 2 * JHn B) / JMq B)
    (slopeHi q * 2 * JHd B / (JMq B * B.c0 ^ 2))
  else slopeHi q * 2 * (B.b1 ^ 2 * JHn B) / JMq B

def E1q : ℚ := if 0 < B.c0 then min (B.b1 ^ 2 * B.c1 * JHn B) (JHd B / B.c0) else B.b1 ^ 2 * B.c1 * JHn B

def T4q (w : RWit) : ℚ :=
  if w.mvt then DQ B w.q * (1 - B.b0) * (2 * kappaQ B * (1 - B.b0) + B.b1 / 2 + E1q B / JMq B)
  else (slopeHi w.q - slopeLo w.t) * (1 - B.b0) / B.c0

def alphaQ (w : RWit) : ℚ := slopeLo w.v / Xq B / (4 * hHi B)

def PloQ (w : RWit) : ℚ := alphaQ B w * (1 - B.b1 ^ 2) + betaQ B * B.b0 ^ 2 - T3q B w.q - T4q B w

/-- geometry and point certificates -/
def geomOK : Bool :=
  decide (0 < B.a0) && decide (B.a0 ≤ B.a1) && decide (0 ≤ B.b0) && decide (B.b0 ≤ B.b1) &&
    decide (B.b1 ≤ 1) && decide (0 ≤ B.c0) && decide (B.c0 ≤ B.c1) && decide (cHi B < 1 / 2) &&
    ptOk B.a0 && ptOk B.a1 && ptOk (bLo B) && ptOk (bHi B)

/-- the vacuous case: `A > 1/20` on the whole box -/
def vacOK : Bool := decide (Ha1 B + Hb1 B < 20 * B.c0)

def okH : Bool :=
  decide (0 < hLo B) && ptOk (MHi B) && decide (0 ≤ lamLo (MHi B)) && decide (0 < JMq B) &&
    decide (0 < MLo B) && decide (MHi B < 1)

def okC : Bool :=
  ptOk (cHi B) && decide (0 ≤ lamLo (cHi B)) && decide (0 < kapLoQ (cHi B)) &&
    decide (0 < (1 - 2 * cHi B) * (lamLo (cHi B) / LqHi) + 2 * Hb0 B) && decide (0 < B.c1)

def okTheta (w : RWit) : Bool :=
  slopeLoOk w.v && decide (0 ≤ slopeLo w.v) && decide (1 - 2 * w.v ≤ 2 * Xq B * Hlo w.v)

def okQ (w : RWit) : Bool :=
  decide (0 < w.q) && slopeHiOk w.q && decide (w.q ≤ B.a0 ∨ w.q ≤ MLo B - JHup B / JMq B)

def okRho : Bool :=
  decide (0 < rhoHi B) && decide (rhoHi B < 1) && ptOk (rhoHi B) && ptOk (rhoHi B / (1 + rhoHi B)) &&
    decide (0 < rhopHi B) && decide (rhopHi B < 1) && ptOk (rhopHi B) &&
    ptOk (rhopHi B / (1 + rhopHi B))

def okT4 (w : RWit) : Bool :=
  if w.mvt then decide (w.q ≤ cHi B) && decide (0 < 1 - 2 * cHi B)
  else decide (0 < B.c0) && slopeLoOk w.t && decide (w.t < 1 / 2) &&
    decide (min (cHi B) (bHi B + 2 * kappaQ B * (1 - B.b0) * B.c1) ≤ w.t) &&
    decide (0 ≤ slopeHi w.q - slopeLo w.t)

def boundOK (w : RWit) : Bool :=
  okH B && okC B && okTheta B w && okQ B w && okRho B && okT4 B w && decide (0 < PloQ B w)

def r3BoxOK (w : RWit) : Bool := geomOK B && (vacOK B || boundOK B w)

end box

end CKLaneM07.CE.R3

end


