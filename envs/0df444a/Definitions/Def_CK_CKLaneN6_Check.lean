-- Prove2me | Definitions.Def_CK_CKLaneN6_Check
-- name    : CK_CKLaneN6_Check
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:26:17.763533+00:00
-- url     : https://prove2.me/theorems/57b840d6-7072-46c4-99a9-faddf2577ce8
-- title:
--   Courtade–Kumar proof module `CKLaneN6.Check` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN6.Check` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN6.Check` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN6.Check (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN6/Check.lean)

import Definitions.Def_CK_CKLaneN6_Rad
import Definitions.Def_CK_CKLaneN6_LSKW
import Definitions.Def_CK_CKLaneN6_APar
import Definitions.Def_CK_CKLaneN6_PLog

-- ===== source module CKLaneN6.Check =====
section

/-!
# Lane N6: the unified per-cell certificate of SMALL_RATIO Theorem 3

`W.check B w = true → LeafOK B` for every certificate constructor (`W.check_sound`):

| constructor | archived owners it serves | kernel |
|---|---|---|
| `irr`   | `outside` | `b1 - a0 < 1/100` |
| `prior` | `prior_same_side` | `1/20 ≤ b0 - a1` |
| `csr`   | `central_small_ratio` | `E⁺ ≤ 11/200`, `b1 - a0 ≤ 4 E⁻` |
| `cap`   | `cap` | `(1-t0)(C0hi - EMIN) ≤ 3/40` (`CKLaneM05.FE8.capCheck`) |
| `apar`  | `phi_parent`, `phi_parent_log` | compiled analytic parent dominance (`CKLaneN6.APar`) |
| `par`   | `phi_parent` | monotone parent dominance (`CKLaneM05.FE8.parentCheck`, reused) |
| `plog`  | `phi_parent_log` | archive rule (13) (`CKLaneN6.PLog`) |
| `rad`   | `sum_normalized`, `endpoint_*`, `shifted_logsum`, `logsum*` | radial (`CKLaneN6.Rad`) |
| `lsk`   | `logsum*`, `shifted_logsum` | lane E `LSK` on the bounding box (`CKLaneN6.LSKW`) |

Cells may refine an archived leaf box (`CKLaneM05.FE8.CT`, exact halving); `CT.soundN6` and
`entries_sound` (`CKLaneN6.Base`) lift cell certificates to archived leaves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6

/-- Per-cell certificate. -/
inductive W where
  | irr
  | prior
  | csr
  | cap
  | apar
  | par (u0 v2 u1 : ℚ) (mode : Bool)
  | plog (vm vp v2 : ℚ)
  | rad (vS vI vc : ℚ) (useHm : Bool)
  | lsk (v0S v0I v1S v1I : ℚ)
  deriving Repr

def W.check (B : CKLaneD.Box) : W → Bool
  | .irr => decide (B.bhi - B.alo < 1 / 100)
  | .prior => decide (1 / 20 ≤ B.blo - B.ahi)
  | .csr => csrCheck B
  | .cap => CKLaneM05.FE8.capCheck B
  | .apar => APar.aparCheck B
  | .par u0 v2 u1 mode => CKLaneM05.FE8.parentCheck B ⟨u0, v2, u1, mode⟩
  | .plog vm vp v2 => PLog.plogCheck B ⟨vm, vp, v2⟩
  | .rad vS vI vc useHm => Rad.radCheck B ⟨vS, vI, vc, useHm⟩
  | .lsk v0S v0I v1S v1I => LSKW.lskCheck B ⟨v0S, v0I, v1S, v1I⟩

theorem W.check_sound : ∀ (B : CKLaneD.Box) (w : W), W.check B w = true → LeafOK B
  | _, .irr, h => leafOK_of_irr (by simpa [W.check] using h)
  | _, .prior, h => leafOK_of_prior (by simpa [W.check] using h)
  | _, .csr, h => leafOK_of_csr h
  | _, .cap, h => leafOK_of_cap h
  | _, .apar, h => APar.leafOK_of_aparCheck h
  | _, .par _ _ _ _, h => leafOK_of_parentBox (CKLaneM05.FE8.parentCheck_sound h)
  | _, .plog _ _ _, h => PLog.leafOK_of_plogCheck h
  | _, .rad _ _ _ _, h => Rad.leafOK_of_radCheck h
  | _, .lsk _ _ _ _, h => LSKW.leafOK_of_lskCheck h

/-- Shard form: one kernel-evaluated `List.all` gives every listed archived leaf. -/
theorem shard_sound (L : List (List ℕ × CKLaneM05.FE8.CT W))
    (h : L.all (fun x => x.2.check W.check (CKLaneM05.FE8.feBox x.1)) = true) :
    ∀ q ∈ L.map Prod.fst, LeafOK (CKLaneM05.FE8.feBox q) :=
  entries_sound W.check W.check_sound L h

/-- Compact dyadic literal `n / 2^e` for witness data. -/
def dy (n : ℤ) (e : ℕ) : ℚ := (n : ℚ) / ((2 ^ e : ℕ) : ℚ)

end CKLaneN6

end


