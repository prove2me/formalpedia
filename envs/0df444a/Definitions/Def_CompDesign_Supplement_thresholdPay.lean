-- Prove2me | Definitions.Def_CompDesign_Supplement_thresholdPay
-- name    : CompDesign_Supplement_thresholdPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:50:50.394574+00:00
-- url     : https://prove2.me/theorems/febfdfeb-6e97-4e82-931f-a3745e00bb2c
-- title:
--   Branches $p_r$ of the randomized threshold-prize rule
-- statement:
--   Let $U=v(A)$ and $\tau_r=U/2^r$. The $r$-th branch of the **threshold-prize rule** pays
--   $$p_r(S)=\begin{cases}B&\text{if }v(S)\ge\tau_r,\\0&\text{if }v(S)<\tau_r.\end{cases}$$
--   The randomized rule draws $r$ uniformly from $\{0,\dots,L\}$ and announces it (Theorems 7.2, 7.3).
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §7.1.2, pp.53–54 (PDF 56–57)

import Mathlib

namespace CompDesign.Supplement

/-- The `r`-th branch of the randomized threshold-prize rule of §7.1.2, pp.53–54 (PDF 56–57), of
Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…): with `U = v(A)` and threshold `τ_r = U/2^r`, `p_r(S) = B` if `v(S) ≥ τ_r`, and `0` otherwise. -/
noncomputable def thresholdPay {m : ℕ} (v : Finset (Fin m) → ℝ) (B : ℝ) (r : ℕ)
    (S : Finset (Fin m)) : ℝ :=
  if v Finset.univ / 2 ^ r ≤ v S then B else 0

end CompDesign.Supplement


