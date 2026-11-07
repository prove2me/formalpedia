-- Prove2me | Definitions.Def_HWMaskLeak_insecBin
-- name    : HWMaskLeak_insecBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:01.468941+00:00
-- url     : https://prove2.me/theorems/e1ec4b42-cdfa-421b-b97b-70cd8a85674d
-- title:
--   Model insecurity $E^{\mathrm{bin}}_k(N,s)$, eq. (21)
-- statement:
--   With $W_{\mathrm{bin}}=\{0,1,\dots,n\}$, for $k\ge1$ and $s\in G$,
--   $$
--   E^{\mathrm{bin}}_k(N,s):=\frac12\sum_{w\in W_{\mathrm{bin}}^k}\Bigl|\sum_{t\ne0}e_N(st)\prod_{j=1}^k\hat B_{w_j}(t)\Bigr|.
--   $$
--   It is the full-range model of the Fourier form (9) of $E_k(s)$; the transference lemma (Lemma 4.8) compares the two.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §4.1, p.20, eq. (21)

import Mathlib
import Definitions.Def_HWMaskLeak_fullRange

namespace HWMaskLeak

/-- **The model insecurity `E^bin_k(N, s)`, eq. (21)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks
Leak Their Weight: From Additive Sharing to Learning with Physical Rounding*, preprint (version of
October 31, 2026, sha256 ab686360…), §4.1, p.20):
`E^bin_k(N, s) := ½ Σ_{w ∈ W_bin^k} | Σ_{t ≠ 0} e_N(st) Π_{j=1}^k B̂_{w_j}(t) |`, with
`W_bin = {0, 1, …, n}`.

**Formalization Note** `e_N(st)` is `ZMod.stdAddChar (s * t)`; `s` ranges over `ZMod N`, i.e. over
`0 ⩽ s < N`. -/
noncomputable def insecBin (n N : ℕ) [NeZero N] (k : ℕ) (s : ZMod N) : ℝ :=
  (1 / 2) * ∑ w ∈ Fintype.piFinset (fun _ : Fin k => Finset.range (n + 1)),
    ‖∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0),
      ZMod.stdAddChar (s * t) * ∏ j, fullRangeHat n N (w j) t‖

end HWMaskLeak


