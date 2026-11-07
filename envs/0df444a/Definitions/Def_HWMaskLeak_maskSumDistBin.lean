-- Prove2me | Definitions.Def_HWMaskLeak_maskSumDistBin
-- name    : HWMaskLeak_maskSumDistBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:17.264459+00:00
-- url     : https://prove2.me/theorems/3b697bbe-7fdc-42eb-93ee-a4d40c2e0581
-- title:
--   Model last-share-public distance $\Delta^{\mathrm{bin}}_m(N)$, eq. (39)
-- statement:
--   With $W=W_{\mathrm{bin}}=\{0,1,\dots,n\}$, the full-range model of $\Delta_m$ is defined by
--   $$
--   2\,\Delta^{\mathrm{bin}}_m(N):=\sum_{w\in W^m}\frac1N\sum_{s\in G}\Bigl|\sum_{t\ne0}e_N(st)\prod_{j=1}^m\hat B_{w_j}(t)\Bigr|.
--   $$
--   It is the average over $s$ of $E^{\mathrm{bin}}_m(N,s)$ (eq. (41)) and enters Corollary 4.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. D.2, p.52, eq. (39)

import Mathlib
import Definitions.Def_HWMaskLeak_fullRange

namespace HWMaskLeak

/-- **The model last-share-public distance `Δ^bin_m(N)`, eq. (39)** (Biswas, Hwang, Maji, Shkredov,
Ye, *When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding*, preprint
(version of October 31, 2026, sha256 ab686360…), App. D.2, p.52):
`2 · Δ^bin_m(N) := Σ_{w ∈ W^m} (1/N) Σ_{s ∈ G} | Σ_{t ≠ 0} e_N(st) Π_{j=1}^m B̂_{w_j}(t) |`, where in
App. C–D `W = W_bin = {0, 1, …, n}`.

**Formalization Note** The definition is the printed one divided by `2`. -/
noncomputable def maskSumDistBin (n N : ℕ) [NeZero N] (m : ℕ) : ℝ :=
  (1 / 2) * ∑ w ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (n + 1)),
    (1 / (N : ℝ)) * ∑ s : ZMod N,
      ‖∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0),
        ZMod.stdAddChar (s * t) * ∏ j, fullRangeHat n N (w j) t‖

end HWMaskLeak


