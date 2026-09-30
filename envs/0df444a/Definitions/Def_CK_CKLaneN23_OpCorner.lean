-- Prove2me | Definitions.Def_CK_CKLaneN23_OpCorner
-- name    : CK_CKLaneN23_OpCorner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:00:52.304534+00:00
-- url     : https://prove2.me/theorems/91703113-59d9-4a43-8804-d9dab9c5a841
-- title:
--   Courtade–Kumar proof module `CKLaneN23.OpCorner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.OpCorner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.OpCorner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.OpCorner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/OpCorner.lean)

import Definitions.Def_CK_GeneralCK_PsiEndpointBellman
import Definitions.Def_CK_GeneralCK_PsiOppositeCornerDomain

-- ===== source module CKLaneN23.OpCorner =====
section

/-!
# Lane N23 — row `OP_Corner` of the scope-locked manuscript route

`OP_Corner` and `PsiActive` are copied verbatim from
`~/ck_lanes_20260923/coord/routesrc/CKRoute/Manuscript.lean`
(sha256 5eefe06bd891dd6c492304e881a4574172568b6d04ec1329d0ddf3d6c01aaa04).

Archived owner: `retained/opposite_corner/OPPOSITE_CORNER_PROOF.md`, Theorem 2
(`a + (1-b) ≤ 2^-13`, every positive feasible entropy pair). In the psi-active branch the
archived proof bounds `R_B` by the Proposition 3.4 endpoint value with an entropy-imbalance
(logarithmic barrier) gain and a `q²/E` parent margin, after placing the corner inside
`d ≥ 9/10`, `E ≤ 10^-3`, `q ≤ 1/10`.

The row is discharged by an adapter over two compiled, sorry-free theorems of the F-C
provider (`~/gck_lanes/F-C/work/root`), which prove exactly that psi-branch estimate for
actual finite laws:

* `GeneralCK.PsiOppositeCornerDomain.corner_domain`: on the corner, `0 ≤ q ≤ 1/10`,
  `0 < E ≤ 1/1024`, `8E ≤ b - a` (entropy concavity and `H(2^-14) ≤ 1/1024`);
* `GeneralCK.PsiEndpointBellman.law_gap_le_cost`: for `a + b ≤ 1`, `E ≤ 1/80`,
  `8E ≤ b - a`, `q ≤ 1/10` and `phi ≤ psi` at the parent,
  `gap + (9/100)·q²/E ≤ F(d,E) + d/(2 ln 2)·barrier(t) ≤ cost`
  (endpoint contact with logarithmic imbalance gain, retained child maxima).

No numerical or regional fact is taken as a hypothesis.
-/

namespace CKLaneN23

open GeneralCK

/-- Strict psi-activity at the parent. -/
def PsiActive {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

/-- Row `a + 1 - b ≤ 2^-13`: `retained/opposite_corner/OPPOSITE_CORNER_PROOF.md`, Thm 2. -/
def OP_Corner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a + (1 - μ.b) ≤ 1 / 8192 → PsiActive μ → μ.gap ≤ μ.cost

/-- The opposite deterministic corner row, unconditionally. -/
theorem row_opCorner : OP_Corner := by
  intro k μ _hab hsum _hb hcor hact
  have hc : μ.a + 1 - μ.b ≤ 1 / 8192 := by linarith
  obtain ⟨_hq, hqsmall, _hE, hEi, hd, _ha, _hb'⟩ :=
    PsiOppositeCornerDomain.corner_domain μ hsum hc
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact PsiEndpointBellman.law_gap_le_cost μ hsum (by linarith) hd hqsmall hact'.le

end CKLaneN23

end


