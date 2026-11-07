-- Prove2me | Definitions.Def_HWMaskLeak_Wcent
-- name    : HWMaskLeak_Wcent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:34.420999+00:00
-- url     : https://prove2.me/theorems/a6c83354-6c33-4a08-bb22-0a9d899dcc21
-- title:
--   Central weights $W_{\mathrm{cent}}$
-- statement:
--   The **central weights** are
--   $$
--   W_{\mathrm{cent}}:=\Bigl\{w\in W_{\mathrm{bin}}:\ \bigl|w-\tfrac n2\bigr|\le\sqrt{n\ln n}\Bigr\},\qquad W_{\mathrm{bin}}=\{0,1,\dots,n\},
--   $$
--   with $\ln$ the natural logarithm. The proof of Lemma 4.5 discards the other weights by a binomial tail bound and estimates $\hat B_w(t)$ individually on $W_{\mathrm{cent}}$ (Lemmas 4.10 and 4.11).
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §4.4, p.23

import Mathlib

namespace HWMaskLeak

/-- **The central weights `W_cent`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight:
From Additive Sharing to Learning with Physical Rounding*, preprint (version of October 31, 2026,
sha256 ab686360…), §4.4, p.23): `W_cent := {w ∈ W_bin : |w − n/2| ⩽ √(n ln n)}`, with
`W_bin = {0, 1, …, n}` and `ln` the natural logarithm. -/
noncomputable def Wcent (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun w => |(w : ℝ) - n / 2| ≤ Real.sqrt (n * Real.log n))

end HWMaskLeak


