-- Prove2me | Definitions.Def_PreservePast_FC
-- name    : PreservePast_FC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:30.201192+00:00
-- url     : https://prove2.me/theorems/21e32c54-6501-4b69-a9ad-cac41c63b1dc
-- title:
--   Rates $F_C$, $F_R$, the factor $\mathcal L$ and the threshold $N_\beta$
-- statement:
--   For $n,r\ge1$ and $\epsilon>0$ the paper's two rate terms and its logarithmic factor are
--   $$
--   F_C=n^2\log_2\Big(1+\frac1{n\epsilon}\Big),\qquad F_R=nr\log_2\Big(1+\frac1{r\epsilon^2}\Big),\qquad \mathcal L=\log_2(2/\epsilon),
--   $$
--   the **covariance term**, the **response-rank term** and the factor lost by the upper bound. For $0<\beta<1/2$ put $s_\beta=1-2\beta$ and
--   $$
--   N_\beta=\big\lceil\max\{8192,\ 512/\sqrt{s_\beta}\}\big\rceil ,
--   $$
--   the dimension threshold of the lower bound.
--
--   **Formalization Note** $\lceil\cdot\rceil$ is the natural-number ceiling; logarithms are `Real.logb 2`.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8), (15); §C.6, p.24 (PDF p.26), (71)

import Mathlib

namespace PreservePast

/-- **The covariance rate** `F_C = n² log₂(1 + 1/(nϵ))`.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8), (15). -/
noncomputable def FC (n : ℕ) (ε : ℝ) : ℝ := (n : ℝ) ^ 2 * Real.logb 2 (1 + 1 / (n * ε))

/-- **The response-rank rate** `F_R = nr log₂(1 + 1/(rϵ²))`, (15), p.6. -/
noncomputable def FR (n r : ℕ) (ε : ℝ) : ℝ := (n : ℝ) * r * Real.logb 2 (1 + 1 / (r * ε ^ 2))

/-- **The logarithmic factor** `𝓛 = log₂(2/ϵ)`, (15), p.6. -/
noncomputable def calL (ε : ℝ) : ℝ := Real.logb 2 (2 / ε)

/-- **The dimension threshold** `N_β = ⌈max{8192, 512/√s_β}⌉`, `s_β = 1 − 2β`.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.6, p.24 (PDF p.26), (71).

**Formalization Note.** `⌈·⌉` is `Nat.ceil`; used for `0 < β < 1/2`, where `s_β > 0`. -/
noncomputable def Nbeta (β : ℝ) : ℕ := ⌈max 8192 (512 / Real.sqrt (1 - 2 * β))⌉₊

end PreservePast


