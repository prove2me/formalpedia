-- Prove2me | Definitions.Def_HWMaskLeak_alphaBin
-- name    : HWMaskLeak_alphaBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:23.916448+00:00
-- url     : https://prove2.me/theorems/5f204aea-efbe-4241-89fe-682ccd819ee8
-- title:
--   Spectral parameter $\alpha_{\mathrm{bin}}(N)$ and densities $\rho_w(N)$
-- statement:
--   For $w\in W_{\mathrm{bin}}=\{0,1,\dots,n\}$ let $\rho_w(N):=\frac1N\binom nw$, and
--   $$
--   \alpha_{\mathrm{bin}}(N):=\max_{t\ne0}\sum_{w\in W_{\mathrm{bin}}}\frac{|\hat B_w(t)|^2}{\rho_w(N)}.
--   $$
--   This single quantity governs the one-share contraction of the model energies (Lemma 4.4); the key spectral estimate (Lemma 4.5) bounds it by $O(1/n)$.
--
--   **Formalization Note** The maximum over the nonzero residues is a supremum over the finite set $\{t\ne0\}$; for $N\ge2$ it is the maximum (for $N=1$ the set is empty and the value is $0$).
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.4, p.21

import Mathlib
import Definitions.Def_HWMaskLeak_fullRange

namespace HWMaskLeak

/-- **The weight density `ρ_w(N)`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight:
From Additive Sharing to Learning with Physical Rounding*, preprint (version of October 31, 2026,
sha256 ab686360…), Lemma 4.4, p.21): `ρ_w(N) := (1/N) (n choose w)`. -/
noncomputable def rhoW (n N w : ℕ) : ℝ := (n.choose w : ℝ) / N

/-- **The spectral parameter `α_bin(N)`** (same preprint, Lemma 4.4, p.21):
`α_bin(N) := max_{t ≠ 0} Σ_{w ∈ W_bin} |B̂_w(t)|² / ρ_w(N)`, with `W_bin = {0, 1, …, n}`.

**Formalization Note** The maximum over the nonzero residues is a real `⨆` over the finite subtype
`{t : ZMod N // t ≠ 0}`; for `N ⩾ 2` this subtype is nonempty and the `⨆` is the maximum (for `N = 1`
it is empty and the `⨆` is `0`). Every `ρ_w(N)` with `w ⩽ n` is positive. -/
noncomputable def alphaBin (n N : ℕ) [NeZero N] : ℝ :=
  ⨆ t : {t : ZMod N // t ≠ 0},
    ∑ w ∈ Finset.range (n + 1), ‖fullRangeHat n N w t.1‖ ^ 2 / rhoW n N w

end HWMaskLeak


