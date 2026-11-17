-- Prove2me | Definitions.Def_BilatMatch_Supplement_IsGridApprox
-- name    : BilatMatch_Supplement_IsGridApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:26:40.069936+00:00
-- url     : https://prove2.me/theorems/e76e5eb3-97f0-43cb-9bd2-473abdb77fb6
-- title:
--   Downward finite-grid approximability of a buyer prior into a class $\mathfrak B$
-- statement:
--   A buyer prior $\mu$ on $\mathbb R$ is **downward finite-grid approximable into a class $\mathfrak B$** of priors if
--
--   1. $\mu$ is bounded: $\mu([-K,K]^{\mathrm c})=0$ for some $K$; and
--   2. for every $\delta>0$ there is a finite nonempty grid $G\subset\mathbb R$ such that, for $\mu$-almost every type $t$, some grid point lies at or below $t$ and
--   $$t-\lfloor t\rfloor_G\le\delta,\qquad \lfloor t\rfloor_G=\max\{g\in G: g\le t\},$$
--   and the induced prior, the law of $\lfloor t\rfloor_G$ for $t\sim\mu$, belongs to $\mathfrak B$.
--
--   This is the condition on buyer priors in the restricted bilateral-to-matching reduction (Theorem 3.9): buyers are rounded down to a grid whose induced priors lie in the class for which bilateral bounds are assumed.
--
--   **Formalization Note** "Mesh $\delta$" is read through the only property the proof uses (the rounding loss of eq. (21)): every type loses at most $\delta$ under downward rounding. Downward rounding is the published `floorTo` of `BilatMatch.rounding`.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), Theorem 3.9, p.16 (pdf p.18); rounding loss eq. (21), p.33 (pdf p.35)

import Mathlib
import Definitions.Def_BilatMatch_rounding

open MeasureTheory

namespace BilatMatch.Supplement

open BilatMatch

/-- **Downward finite-grid approximability into a buyer class** (Liu, Qin, Wang, *From Bilateral
Trade to Matching Markets: Sharp Gains from Trade*, arXiv:2609.30702, held version, sha256
ff1490ad…, Theorem 3.9, p.16 (pdf p.18): "bounded buyer priors admitting downward finite-grid
approximations of vanishing mesh whose induced priors belong to 𝔅"; rounding loss as in eq. (21),
p.33).

`IsGridApprox 𝔅 μ`: the prior `μ` is bounded (it gives full mass to some `[−K, K]`), and for every
`δ > 0` there is a finite nonempty grid `G ⊂ ℝ` such that almost every type `t` has a grid point at
or below it and lies within `δ` above its downward rounding `floorTo G t` (the largest grid point
`≤ t`), and the induced prior, the law of `floorTo G t` for `t ∼ μ`, belongs to `𝔅`.

**Formalization Note** "Mesh δ" is read through the only property the proof uses: every type of the
support loses at most `δ` under downward rounding (a grid of mesh `≤ δ` reaching below the support
has it). The grid is a `Finset`; `floorTo` is the published downward rounding of
`BilatMatch.rounding`. -/
def IsGridApprox (𝔅 : Set (Measure ℝ)) (μ : Measure ℝ) : Prop :=
  (∃ K : ℝ, μ (Set.Icc (-K) K)ᶜ = 0) ∧
    ∀ δ : ℝ, 0 < δ → ∃ G : Finset ℝ, G.Nonempty ∧
      (∀ᵐ t ∂μ, (∃ g ∈ G, g ≤ t) ∧ t - floorTo (↑G) t ≤ δ) ∧
      μ.map (floorTo (↑G)) ∈ 𝔅

end BilatMatch.Supplement


