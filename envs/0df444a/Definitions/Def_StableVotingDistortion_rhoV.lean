-- Prove2me | Definitions.Def_StableVotingDistortion_rhoV
-- name    : StableVotingDistortion_rhoV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:14.414789+00:00
-- url     : https://prove2.me/theorems/4a2884cb-c512-4968-9671-a301606bb019
-- title:
--   Biased-metric terms $\rho_v(b)$, $L_v(D)$, $R_v$
-- statement:
--   Let $\rho:C\to\mathbb R_{\ge0}$. For a voter $v$ and candidate $b$,
--   $$\rho_v(b)=\min_{c\preceq_v b}\rho(c),\qquad L_v(D)=\mathbb E_{b\sim D}[\rho_v(b)],\qquad R_v=\max_b\bigl(\rho(b)-\rho_v(b)\bigr).$$
--
--   The minimum includes $c=b$, so $\rho_v(b)\le\rho(b)$. Both the minimum and the maximum include candidates of zero mass, and $R_v$ does not depend on $D$. These terms express a worst-case biased metric through $\rho$ alone.
--
--   **Formalization Note** The definitions take a real-valued $\rho$; the theorems assume $\rho\ge0$.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §4, p.13; p.14

import Mathlib
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

open Classical in
/-- The running minimum `ρ_v(b) = min_{c ⪯_v b} ρ(c)`. The minimum is over all candidates `c` with
`c = b` or `b ≻_v c`, zero mass included, so `ρ_v(b) ≤ ρ(b)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §4, p.13: "we introduce the shorthand ρ_v(b) = min_{c⪯_v b} ρ(c)"; p.14: "both the running
minimum and the max_b include candidates whose block width is zero." -/
noncomputable def rhoV {V C : Type} [Fintype C] (E : Election V C) (ρ : C → ℝ) (v : V) (b : C) : ℝ :=
  (Finset.univ.filter (fun c => c = b ∨ E.prefers v b c)).inf' ⟨b, by simp⟩ ρ

/-- `L_v(D) = E_{b ∼ D}[ρ_v(b)]`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §4, p.13. -/
noncomputable def Lv {V C : Type} [Fintype C] (E : Election V C) (D ρ : C → ℝ) (v : V) : ℝ :=
  ∑ b, D b * rhoV E ρ v b

/-- `R_v = max_b (ρ(b) − ρ_v(b))`. The maximum runs over all candidates, zero mass included, and `R_v`
does not depend on the lottery.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §4, p.13; p.14: "both the running minimum and the max_b include candidates whose block width
is zero." -/
noncomputable def Rv {V C : Type} [Fintype C] [Nonempty C] (E : Election V C) (ρ : C → ℝ) (v : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun b => ρ b - rhoV E ρ v b)

end StableVotingDistortion


