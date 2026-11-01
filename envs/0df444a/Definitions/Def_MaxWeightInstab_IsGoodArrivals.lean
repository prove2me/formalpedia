-- Prove2me | Definitions.Def_MaxWeightInstab_IsGoodArrivals
-- name    : MaxWeightInstab_IsGoodArrivals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:39.62844+00:00
-- url     : https://prove2.me/theorems/0d746613-220e-4b36-a62a-4ac95a0397b0
-- title:
--   The event $G_M$ of display (15)
-- statement:
--   An arrival path lies in $G_M$ when
--
--   $$
--   \sup_{j\in\{\mathcal A_1,\dots,\mathcal A_J,\mathcal B_1,\dots,\mathcal B_J\}}\ \sup_{0\le s\le t\le T}\left|A_j(t)-A_j(s)-\frac aJ(t-s)\right|\le\varepsilon bT,
--   $$
--
--   with $T$ from (14) and $b$ from (15). It constrains the external arrivals only.
--
--   **Formalization Note** Times $s,t$ are integers with $0\le s\le t\le T$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (15), p.7

import Mathlib
import Definitions.Def_MaxWeightInstab_extCount
import Definitions.Def_MaxWeightInstab_horizon
import Definitions.Def_MaxWeightInstab_bConst

namespace MaxWeightInstab

/-- The event `G_M` of (15) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.7), as a property of the arrival path `e`:
`sup_{j∈{𝒜₁,…,𝒜_J,ℬ₁,…,ℬ_J}} sup_{0≤s≤t≤T} |A_j(t) − A_j(s) − (a/J)(t − s)| ≤ ε b T`, with
`T = horizon a ν M` (14) and `b = bConst a J ν γ`.

**Formalization Note.** Time is discrete: `s` and `t` range over the integers with
`0 ≤ s ≤ t ≤ T`. The suprema are written as a universal bound. -/
def IsGoodArrivals (a : ℝ) (J ν : ℕ) (γ ε M : ℝ) (e : ℕ → ExtArrivals J) : Prop :=
  ∀ k : Fin J ⊕ Fin J, ∀ s t : ℕ, s ≤ t → (t : ℝ) ≤ horizon a ν M →
    |(extCount e k t : ℝ) - extCount e k s - a / J * ((t : ℝ) - s)| ≤
      ε * bConst a J ν γ * horizon a ν M

end MaxWeightInstab


