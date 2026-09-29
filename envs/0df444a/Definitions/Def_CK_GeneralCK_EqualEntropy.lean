-- Prove2me | Definitions.Def_CK_GeneralCK_EqualEntropy
-- name    : CK_GeneralCK_EqualEntropy
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:37:01.749087+00:00
-- url     : https://prove2.me/theorems/7624ee2f-a20d-42b7-a7fc-0889dfb929ef
-- title:
--   Courtade–Kumar proof module `GeneralCK.EqualEntropy` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EqualEntropy` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EqualEntropy` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EqualEntropy (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EqualEntropy.lean)

import Definitions.Def_CK_GeneralCK_FourMomentDefs
import Definitions.Def_CK_GeneralCK_RadialFourPoint
import Definitions.Def_CK_GeneralCK_FourMomentLowerBound

namespace GeneralCK

/-- The source's equal-entropy pure-gap owner, without assuming the L4 lower bound. -/
theorem pureGap_equal_entropy_nonneg {e : ℝ} (he : 0 < e) (a b : ℝ) :
    0 ≤ pureGap a b e e := by
  have h := equal_entropy_phi_gap_le_radial he a b
  simpa only [pureGap,fourMomentLowerBound,entropyCorrection_self,add_zero,
    show (e+e)/2=e by ring] using sub_nonneg.mpr h

/-- Equal entropies discharge the pure-gap input; the two LB1 inputs remain explicit. -/
theorem InteriorLaw.equal_entropy_phi_of_fourMoment {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (heq : μ.e = μ.f)
    (hreflect : ∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
      entropyCorrection (H u) (H v) ≤ atomCorrection u v)
    (hconvex : ConvexOn ℝ (Set.Ioc (0:ℝ) 1 ×ˢ Set.Ioc (0:ℝ) 1)
      (fun p : ℝ × ℝ => entropyCorrection p.1 p.2)) :
    candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  apply μ.phi_gap_le_cost_of_fourMoment hreflect hconvex
  rw [← heq]
  exact pureGap_equal_entropy_nonneg μ.e_pos μ.a μ.b

end GeneralCK


