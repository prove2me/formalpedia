-- Prove2me | Definitions.Def_CK_CKLaneM03_Canary
-- name    : CK_CKLaneM03_Canary
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T00:49:38.643467+00:00
-- url     : https://prove2.me/theorems/6ad66744-372b-4369-a118-a79e559fd317
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Canary` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Canary` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Canary` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Canary (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Canary.lean)

import Definitions.Def_CK_CKLaneM03_Kernel

-- ===== source module CKLaneM03.Canary =====
section

/-!
# Lane M03 canary: hardest archived same-side `endpoint` leaves

* `ep_502020301420520430420431`: the archived hardest endpoint witness (hardest_14 id 3,
  archived margin 2.133e-7), box `x ∈ [33/32,17/16]`, `b ∈ [811/8192,413/4096]`, `t ∈ [5/8,41/64]`.
* `ep_50202030043151351241241250340`: the smallest-margin leaf of this checker over the whole
  archived endpoint population (exact-mirror relative margin 8.77e-4).

Negative controls (all evaluated by the kernel): a perturbed contact witness, a perturbed
`2^-x` bracket, and the adjacent `t`-slab box are rejected (`epLeaf … = false`).
-/

namespace CKLaneM03.Canary

open CKLaneM03 GeneralCK

/-- Witness for the archived hardest endpoint leaf. -/
def w1 : EpCert :=
  ⟨dy 4416165660797809419 63, dy 4512867096753504463 63, dy 325330069668407811 60,
    dy 319010530993293683 60, dy 455247276892431805 60, false⟩

/-- Witness for the checker-hardest endpoint leaf. -/
def w2 : EpCert :=
  ⟨dy 9374435328615261675 64, dy 1178167198179750971 61, dy 324486766225223183 60,
    dy 316994809570987911 60, dy 462300755120437943 60, false⟩

/-- The archived path reconstructs the archived box exactly. -/
theorem box1_eq : ssBox [5,0,2,0,2,0,3,0,1,4,2,0,5,2,0,4,3,0,4,2,0,4,3,1] =
    ⟨33 / 32, 17 / 16, 811 / 8192, 413 / 4096, 5 / 8, 41 / 64⟩ := by decide +kernel

theorem leaf1_check : epLeaf [5,0,2,0,2,0,3,0,1,4,2,0,5,2,0,4,3,0,4,2,0,4,3,1] w1 = true := by
  decide +kernel

theorem ep_502020301420520430420431 :
    Sem (ssBox [5,0,2,0,2,0,3,0,1,4,2,0,5,2,0,4,3,0,4,2,0,4,3,1]) :=
  epLeaf_sound leaf1_check

theorem leaf2_check :
    epLeaf [5,0,2,0,2,0,3,0,0,4,3,1,5,1,3,5,1,2,4,1,2,4,1,2,5,0,3,4,0] w2 = true := by
  decide +kernel

theorem ep_50202030043151351241241250340 :
    Sem (ssBox [5,0,2,0,2,0,3,0,0,4,3,1,5,1,3,5,1,2,4,1,2,4,1,2,5,0,3,4,0]) :=
  epLeaf_sound leaf2_check

/-- Owner form on the archived hardest leaf (psi weakly active at the parent). -/
theorem ep_502020301420520430420431_gap {k : ℕ} (μ : InteriorLaw (Fin k))
    (hbox : InSBox (ssBox [5,0,2,0,2,0,3,0,1,4,2,0,5,2,0,4,3,0,4,2,0,4,3,1])
      μ.a μ.b μ.meanEntropy)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  sem_gap_le_cost ep_502020301420520430420431 μ hbox hact

/-! ## Negative controls -/

/-- Contact witness lowered by `2^-20` (below the radial contact). -/
def w1_bad_vc : EpCert := { w1 with vc := dy 455247276892431805 60 - dy 1 20 }

/-- Lower `2^-x` bracket raised by `2^-40` (no longer below `2^-xhi`). -/
def w1_bad_r : EpCert := { w1 with rlo := dy 4416165660797809419 63 + dy 1 40 }

theorem neg_vc : epLeaf [5,0,2,0,2,0,3,0,1,4,2,0,5,2,0,4,3,0,4,2,0,4,3,1] w1_bad_vc = false := by
  decide +kernel

theorem neg_r : epLeaf [5,0,2,0,2,0,3,0,1,4,2,0,5,2,0,4,3,0,4,2,0,4,3,1] w1_bad_r = false := by
  decide +kernel

/-- Wrong box: the adjacent entropy slab `t ∈ [41/64, 21/32]` with the same witness. -/
theorem neg_box : epLeaf [5,0,2,0,2,0,3,0,1,4,2,0,5,2,0,4,3,0,4,2,0,5,3,1] w1 = false := by
  decide +kernel

end CKLaneM03.Canary

end


