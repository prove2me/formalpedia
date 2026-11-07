-- Prove2me | Definitions.Def_HWMaskLeak_slice
-- name    : HWMaskLeak_slice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:49.193454+00:00
-- url     : https://prove2.me/theorems/924a8641-eb69-4951-8014-6488e1f7f3df
-- title:
--   Hamming-weight slice $S_w$ as an indicator function
-- statement:
--   For a weight $w$, the **Hamming-weight slice** is
--   $$
--   S_w:=\{x\in G:\ \mathrm{wt}(x)=w\},
--   $$
--   identified with its indicator function $G\to\mathbb C$ (the paper identifies a set with its indicator). Its Fourier coefficients $\hat S_w(t)$ enter the Fourier form (9) of the insecurity and the energies $F_m$.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §2.1, p.15

import Mathlib
import Definitions.Def_HWMaskLeak_wt

namespace HWMaskLeak

/-- **The Hamming-weight slice `S_w`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their
Weight: From Additive Sharing to Learning with Physical Rounding*, preprint (version of October 31,
2026, sha256 ab686360…), §2.1, p.15): `S_w := {x ∈ G : wt(x) = w}`, identified with its indicator
function `G → ℂ` ("We freely identify a set with its indicator function"). -/
def slice (N : ℕ) (w : ℕ) (x : ZMod N) : ℂ := if wt N x = w then 1 else 0

end HWMaskLeak


