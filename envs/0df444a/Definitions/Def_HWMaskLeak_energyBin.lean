-- Prove2me | Definitions.Def_HWMaskLeak_energyBin
-- name    : HWMaskLeak_energyBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:53.577147+00:00
-- url     : https://prove2.me/theorems/a9e0c109-e13b-41c5-8010-ea1cf5f5ffd0
-- title:
--   Model energy $F^{\mathrm{bin}}_m(N)$, eq. (22)
-- statement:
--   With $W_{\mathrm{bin}}:=\{0,1,\dots,n\}$, for $m\ge1$,
--   $$
--   F^{\mathrm{bin}}_m(N):=\sum_{w\in W_{\mathrm{bin}}^m}\Bigl(\sum_{t\ne0}\prod_{j=1}^m\bigl|\hat B_{w_j}(t)\bigr|^2\Bigr)^{1/2},
--   $$
--   the analogue of $F_m$ in the full-range model, over the complete weight range and with $B_w$ in place of $S_w$.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §4.1, p.21, eq. (22)

import Mathlib
import Definitions.Def_HWMaskLeak_fullRange

namespace HWMaskLeak

/-- **The model energy `F^bin_m(N)`, eq. (22)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak
Their Weight: From Additive Sharing to Learning with Physical Rounding*, preprint (version of October
31, 2026, sha256 ab686360…), §4.1, p.21):
`F^bin_m(N) := Σ_{w ∈ W_bin^m} ( Σ_{t ≠ 0} Π_{j=1}^m |B̂_{w_j}(t)|² )^{1/2}`, with
`W_bin = {0, 1, …, n}` and `t` ranging over the nonzero residues of `ℤ/Nℤ`. -/
noncomputable def energyBin (n N : ℕ) [NeZero N] (m : ℕ) : ℝ :=
  ∑ w ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (n + 1)),
    Real.sqrt (∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0),
      ∏ j, ‖fullRangeHat n N (w j) t‖ ^ 2)

end HWMaskLeak


