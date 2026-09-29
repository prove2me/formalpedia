-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallRatioMidpointJet
-- name    : CK_GeneralCK_ReflectionSmallRatioMidpointJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:52:11.714568+00:00
-- url     : https://prove2.me/theorems/c0466176-3214-45bd-a781-8f2789e64e5c
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallRatioMidpointJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallRatioMidpointJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallRatioMidpointJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallRatioMidpointJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallRatioMidpointJet.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallRatioMidpoint

-- ===== source module GeneralCK.ReflectionSmallRatioMidpointJet =====
section

namespace GeneralCK.Reflection.SmallRatio
open Set Certificates Certificates.Reflection

/-- A sound jet for the radius derivative supplies the quadratic majorant.
Only its midpoint value and uniform second derivative need numerical bounds. -/
theorem curvature_pos_of_midpoint_jet {a z p0 M : ℝ} {j : Jet2}
    (ha : 0<a) (ha' : a<1) (hz : 0<z) (hz' : z<1)
    (hj : j.SoundOn (Icc (a*(1-z)/2) (a*(1+z)/2)))
    (hvalue : ∀ s ∈ Icc (a*(1-z)/2) (a*(1+z)/2),
      j.value s=P a ((biasE a+biasE (a*z))/2) s)
    (hcenter : j.value (a/2) ≤ p0)
    (hsecond : ∀ s ∈ Icc (a*(1-z)/2) (a*(1+z)/2), j.second s ≤ M)
    (haccept : p0+M*(a*z)^2/24<2*a/(1-a^2)^2) : 0<curvature a (a*z) := by
  apply curvature_pos_of_midpoint_bound ha ha' hz hz' (p1 := j.first (a/2)) ?_ haccept
  intro s hs
  have hm : a/2 ∈ Icc (a*(1-z)/2) (a*(1+z)/2) := by
    constructor <;> nlinarith [mul_pos ha hz]
  have h := taylor_upper_on_interval hm ⟨hs.1.le,hs.2.le⟩
    (fun x hx => (hj x hx).1) (fun x hx => (hj x hx).2) hsecond
  rw [hvalue s ⟨hs.1.le,hs.2.le⟩] at h
  linarith

end GeneralCK.Reflection.SmallRatio

end


