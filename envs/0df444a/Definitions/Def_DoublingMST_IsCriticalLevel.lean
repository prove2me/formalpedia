-- Prove2me | Definitions.Def_DoublingMST_IsCriticalLevel
-- name    : DoublingMST_IsCriticalLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:33.606619+00:00
-- url     : https://prove2.me/theorems/08043db5-6642-4ee9-b6c9-4b37be25d156
-- title:
--   Critical level $\ell^*$ (15)
-- statement:
--   A level $\ell^*\in\{0,\dots,L\}$ is **critical** if it maximizes $2^{\ell/2}\,|N_\ell|$ over $0\le\ell\le L$:
--
--   $$\ell^*\in\operatorname{argmax}_{0\le\ell\le L}2^{\ell/2}\cdot|N_\ell|. \qquad (15)$$
--
--   **Formalization Note** Ties are not broken; any maximizer is allowed.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), (15), p.17 (PDF p.19); Algorithm 2, Line 2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_DoublingMST_NetHierarchy

namespace DoublingMST

/-- **The critical level ℓ\*.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), (15), p.17 (PDF p.19), and Algorithm 2, Line 2, p.18: "ℓ* := argmax_{0≤ℓ≤L} 2^{ℓ/2} · |N_ℓ|."

`IsCriticalLevel H ℓs`: `ℓs ≤ L` maximizes `2^{ℓ/2}|N_ℓ|` over `0 ≤ ℓ ≤ L`.

**Formalization Note.** Ties are not broken: any maximizer is allowed, and statements quantify
over all of them (or assert one, for the algorithm's run). -/
def IsCriticalLevel {n : ℕ} {d : Fin n → Fin n → ℝ} (H : NetHierarchy d) (ℓs : ℕ) : Prop :=
  ℓs ≤ topLevel d ∧ ∀ ℓ, ℓ ≤ topLevel d →
    (2 : ℝ) ^ ((ℓ : ℝ) / 2) * ((H.N ℓ).card : ℝ) ≤ (2 : ℝ) ^ ((ℓs : ℝ) / 2) * ((H.N ℓs).card : ℝ)

end DoublingMST


