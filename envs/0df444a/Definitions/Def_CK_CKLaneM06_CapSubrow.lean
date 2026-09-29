-- Prove2me | Definitions.Def_CK_CKLaneM06_CapSubrow
-- name    : CK_CKLaneM06_CapSubrow
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:03:36.099656+00:00
-- url     : https://prove2.me/theorems/c12d13fa-d36d-4e70-827a-d9f0a6751d9a
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapSubrow` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapSubrow` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapSubrow` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapSubrow (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapSubrow.lean)

import Definitions.Def_CK_GeneralCK_BellmanAssembly
import Definitions.Def_CK_GeneralCK_EqualMean

-- ===== source module CKLaneM06.CapSubrow =====
section

/-!
# Lane M06: sub-row statements of the cap theorem (5) (CAP_REGION)

Source: `CK_CAP_REGION_CONTINUATION` (nested in CK_OPPOSITE_EXTENSION.zip; extracted copy
`~/ck_lanes_20260923/N1/work/nest/L4/CK_CAP_REGION_CONTINUATION/`), `RESTORED_CAP_PROOF.md` (5):
`a, b ∈ [1/10, 9/10]`, `s = (H(a) - e + H(b) - f)/2 ≤ 3/40` ⟹ `ζ ≥ R_ψ` for every feasible split.

* `PsiActive` / `CentralCap` : verbatim copies of `CKRoute.PsiActive` / `CKLaneN23.CentralCap`
  (row 3 of `CKLaneN23.sameSideHalf_of_certificate_rows`); bind by `Iff.rfl`.
* `CapPsi` : the archive form `ζ ≥ R_ψ` (`candidateGap psi ≤ cost`) on the canonical cap domain;
  it gives `CentralCap` through `hybrid_gap_le_psi` (`centralCap_of_capPsi`).
* `CapSameSide` (SAME_SIDE_CAP root `[1/10,1/2]²`) and `CapCross` (EXPANDED_CAP root
  `[1/10,1/2] × [1/2,9/10]`, at depth `3/40`), both canonical; `capPsi_of_parts` combines them.

Nothing here asserts that any row holds.
-/

set_option autoImplicit false

namespace CKLaneM06.Cap

open GeneralCK

/-- Strict psi-activity at the parent (verbatim copy of `CKRoute.PsiActive`). -/
def PsiActive {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

/-- CAP_REGION central cap theorem (`a,b ∈ [1/10,9/10]`, `s ≤ 3/40`), hybrid form.
Covers: same-side cap square (2,108 leaves) and expanded cap rectangle (14,525 leaves, which
reuses the quantitative cap subrectangle, 29,996 leaves). (Verbatim copy of `CKLaneN23.CentralCap`.) -/
def CentralCap : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ 3 / 40 →
    PsiActive μ → μ.gap ≤ μ.cost

/-- Cap theorem (5), archive form `ζ ≥ R_ψ` for every feasible split, canonical orientation. -/
def CapPsi : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ 3 / 40 →
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-- Same-side cap square (`SAME_SIDE_CAP`, root `[1/10,1/2]²`, `s ≤ 3/40`), canonical. -/
def CapSameSide : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → 1 / 10 ≤ μ.a → μ.b ≤ 1 / 2 →
    (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ 3 / 40 →
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-- Cross-half cap rectangle (`EXPANDED_CAP`, root `[1/10,1/2] × [1/2,9/10]`) at `s ≤ 3/40`,
canonical. -/
def CapCross : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.a ≤ 1 / 2 → 1 / 2 ≤ μ.b →
    (H μ.a + H μ.b) / 2 - μ.meanEntropy ≤ 3 / 40 →
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-- The two roots cover the canonical cap domain. -/
theorem capPsi_of_parts (hs : CapSameSide) (hc : CapCross) : CapPsi := by
  intro k μ hab hsum ha hb hs0
  by_cases hb2 : μ.b ≤ 1 / 2
  · exact hs k μ hab ha hb2 hs0
  · have hb2' : 1 / 2 ≤ μ.b := (lt_of_not_ge hb2).le
    exact hc k μ hab hsum ha (by linarith) hb2' hs0

/-- The archive form gives the hybrid row through `hybrid_gap_le_psi`. -/
theorem centralCap_of_capPsi (h : CapPsi) : CentralCap := by
  intro k μ hab hsum ha hb hs0 hact
  exact (hybrid_gap_le_psi hact.le).trans (h k μ hab hsum ha hb hs0)

theorem centralCap_of_parts (hs : CapSameSide) (hc : CapCross) : CentralCap :=
  centralCap_of_capPsi (capPsi_of_parts hs hc)

end CKLaneM06.Cap

end


