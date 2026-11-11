-- Prove2me | Definitions.Def_NecklacePPAD_Main_Reading
-- name    : NecklacePPAD_Main_Reading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:07:08.756203+00:00
-- url     : https://prove2.me/theorems/1e42dd65-4564-4934-9f5d-80430915202c
-- title:
--   The readings R_c(i) (Definition 4.4) and the threshold segment σ(κ) (equation (1))
-- statement:
--   Values in $\{0,1,\bot\}$ are the published `LpBallVI.Affine.PVal`; `PVal.ofBool` sends a label to $0$ or $1$, and `PVal.neg` is $1-x$ on $\{0,1\}$ (and fixes $\bot$). The **reading** of colour $c$ at segment $i$ (Definition 4.4) is $R_c(i)=\bot$ if $j(c)=i$, and $R_c(i)=\tau(c)\oplus[j(c)<i]$ otherwise. The segment realising threshold $\kappa$ (equation (1)) is $\sigma(\kappa)=\kappa+b-s$ if $\tau=0$ and $\sigma(\kappa)=b-\kappa$ if $\tau=1$, for half-size $b$ and $s$ sensor beads; natural-number subtraction, which never truncates in the range the paper uses ($b\ge s+1$, $1\le\kappa\le b-1$).
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Definition 4.4 and equation (1), p. 6 (PDF 8)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Rigid
import Definitions.Def_LpBallVI_Affine_PureCircuit

set_option autoImplicit false

namespace NecklacePPAD.Main

open LpBallVI.Affine

/-- A label `0`/`1` (`false`/`true`) as a value in `{0, 1, ⊥}`. -/
def PVal.ofBool : Bool → PVal
  | false => .zero
  | true => .one

/-- `1 − x` on the pure values `{0, 1}`; `⊥` is sent to `⊥`. -/
def PVal.neg : PVal → PVal
  | .zero => .one
  | .one => .zero
  | .bot => .bot

/-- **The reading `R_c(i)`** (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, sha256 d5b5449c…,
Definition 4.4, p. 6 (PDF 8)): `R_c(i) = ⊥` if `j(c) = i`, and `R_c(i) = τ(c) ⊕ [j(c) < i]`
otherwise, a value in `{0, 1, ⊥}`. `j(c)` is `Blocks.jCut` and `τ(c)` is `Blocks.tau`; the index
`i` is 1-based as on the page (Definition 4.4 is used for `i ∈ [1, m_c − 1]`). -/
def reading (a : Necklace) (B : Blocks a.n) (ℓ : Fin a.N → Bool) (c : Fin a.n) (i : ℕ) : PVal :=
  if Blocks.jCut a B ℓ c = i then .bot
  else if (B.tau c + (if Blocks.jCut a B ℓ c < i then 1 else 0)) % 2 = 1 then .one else .zero

/-- **The segment `σ(κ)` realising threshold `κ`**, equation (1), p. 6 (PDF 8):
`σ(κ) = κ + b_c − s_c` if `τ(c) = 0` and `σ(κ) = b_c − κ` if `τ(c) = 1`, for half-size `b = b_c`,
`s = s_c` sensor beads and orientation `τ`.

**Formalization Note** Natural-number subtraction; the paper uses (1) only when `b_c ≥ s_c + 1` and
`1 ≤ κ ≤ b_c − 1`, where no truncation occurs. -/
def sigmaSeg (b s τ κ : ℕ) : ℕ :=
  if τ = 0 then κ + b - s else b - κ

end NecklacePPAD.Main


