-- Prove2me | Definitions.Def_GaussPart_MatchesMoments
-- name    : GaussPart_MatchesMoments
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:06.49489+00:00
-- url     : https://prove2.me/theorems/e683c9ca-bc69-46bc-93df-075c82079b13
-- title:
--   Directional moment matching with slack $\Delta$ on a subspace
-- statement:
--   Let $P,Q$ be measures on $\mathbb R^d$, $W\subseteq\mathbb R^d$ a subspace, $k\in\mathbb N$ and $\Delta\ge0$. $P$ and $Q$ **match their first $k$ directional moments on $W$ with slack $\Delta$** if for every unit vector $v\in W$ and every $i\in\{1,\dots,k\}$
--   $$\Big|\mathbb E_{x\sim P}[(v\cdot x)^i]-\mathbb E_{x\sim Q}[(v\cdot x)^i]\Big|\le\Delta .$$
--
--   This is the moment-matching guarantee (iii) of the partitioning theorem, applied to $P\mid R$ and $Q\mid R$ on $V_R^\perp$; when $W=\{0\}$ there is no unit vector and the condition holds trivially.
--
--   **Formalization Note** Moments are Bochner integrals. In every use in the mission the integrands are integrable (smoothness, or the polynomial second-moment assumption, controls them), so the convention that a non-integrable function has integral $0$ does not enter.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition 2.2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_GaussPart_Cell

open MeasureTheory
open scoped RealInnerProductSpace

namespace GaussPart

/-- **Definition 2.2** (directional moment matching), arXiv:2611.05264 (sha256 7e0ca6d4…), p.14
(PDF p.16): for every unit `v ∈ W` and every `i ∈ [k]`,
`|E_{x∼P}[(v · x)ⁱ] − E_{x∼Q}[(v · x)ⁱ]| ≤ Δ`.

**Formalization Note.** Moments are Bochner integrals. In the uses in this mission `(v · x)ⁱ` is
integrable under the measures involved: smoothness or the second-moment assumption gives it, so
the junk value `0` does not occur. If `W = {0}` the condition is vacuous, as in the proof of
Claim 3.14. -/
def MatchesMoments {d : ℕ} (P Q : Measure (Vec d)) (W : Submodule ℝ (Vec d)) (k : ℕ) (Δ : ℝ) :
    Prop :=
  ∀ v ∈ W, ‖v‖ = 1 → ∀ i : ℕ, 1 ≤ i → i ≤ k →
    |∫ x, ⟪v, x⟫ ^ i ∂P - ∫ x, ⟪v, x⟫ ^ i ∂Q| ≤ Δ

end GaussPart


