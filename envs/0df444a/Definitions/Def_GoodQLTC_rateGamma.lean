-- Prove2me | Definitions.Def_GoodQLTC_rateGamma
-- name    : GoodQLTC_rateGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:45:27.65779+00:00
-- url     : https://prove2.me/theorems/228abb13-e8b5-405f-b4e2-374e7fc34d9f
-- title:
--   Rate function $\Gamma_k(J)$
-- statement:
--   With $\mu_{i,b}=m_{i,b}/n_i$ and $S_i=\mu_{i,0}+\mu_{i,1}$, for a $k$-element set $J\subseteq[t]$,
--   $$
--   \Gamma_k(J)=1-2^{t-k}+\prod_{i\notin J}S_i-\mathrm{sym}_{t-k+1}(S_1,\dots,S_t).
--   $$
--   It is the lower bound on the normalized cohomology dimension in Theorem 5.2.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.5, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_GoodQLTC_esym

namespace GoodQLTC

/-- `S_i := μ_{i,0} + μ_{i,1}`, `μ_{i,b} := m_{i,b}/n_i`, Gay–Jeronimo, arXiv:2609.20780 (held
version), §4.5, p.19. (`m i false = m_{i,0}`, `m i true = m_{i,1}`.) -/
noncomputable def rateS {t : ℕ} (n : Fin t → ℕ) (m : Fin t → Bool → ℕ) (i : Fin t) : ℝ :=
  (m i false : ℝ) / n i + (m i true : ℝ) / n i

/-- The rate function `Γ_k(J) := 1 − 2^{t−k} + ∏_{i∉J} S_i − sym_{t−k+1}(S_1, …, S_t)` for a
`k`-element set `J ⊆ [t]`, Gay–Jeronimo, arXiv:2609.20780 (held version), §4.5, p.19.
**Formalization Note.** Used for `k ≤ t` (here `2 ≤ k ≤ t − 2`), so `t − k` is exact. -/
noncomputable def rateGamma {t : ℕ} (n : Fin t → ℕ) (m : Fin t → Bool → ℕ) (k : ℕ)
    (J : Finset (Fin t)) : ℝ :=
  1 - 2 ^ (t - k) + (∏ i ∈ Jᶜ, rateS n m i) - esym (rateS n m) (t - k + 1)

end GoodQLTC


