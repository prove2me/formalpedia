-- Prove2me | Definitions.Def_LipStableCA_profileDist
-- name    : LipStableCA_profileDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:11.862697+00:00
-- url     : https://prove2.me/theorems/109ba9ad-7728-473b-86cf-1bc4a37d254c
-- title:
--   The logarithmic distance between profiles
-- statement:
--   For $a,b\ge 0$, $\mathrm{ld}(a,b)=|\log(a/b)|$ when $a,b>0$, $\mathrm{ld}(0,0)=0$, and $\mathrm{ld}(a,b)=\infty$ otherwise. For profiles $v,w$ and a bidder $i$,
--   $$\delta_i(v,w)=\max_{\emptyset\ne B\subseteq M}\mathrm{ld}(v_i(B),w_i(B)),\qquad d(v,w)=\sum_i\delta_i(v,w).$$
--   So $d(v,w)<\infty$ exactly when $v$ and $w$ have the same zero pattern.
--
--   **Formalization Note.** The values lie in $[0,\infty]$, and `ld` is defined by cases.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Def. 2.3, p.7

import Definitions.Def_LipStableCA_Alloc

open scoped ENNReal

namespace LipStableCA

variable {n m : ℕ}

/-- The logarithmic distance of Definition 2.3, p.7: `ld(a, b) = |log(a/b)|` when `a, b > 0`,
`ld(0, 0) = 0`, and `ld(a, b) = ∞` otherwise. **Formalization Note.** Defined by cases in `ℝ≥0∞` and not
through `Real.log 0 = 0`, so two values with different zero patterns are at distance `⊤`. The paper
defines `ld` for `a, b ≥ 0`; negative arguments get `⊤` here and never occur on valid profiles. -/
noncomputable def ld (a b : ℝ) : ℝ≥0∞ :=
  if a = 0 ∧ b = 0 then 0
  else if 0 < a ∧ 0 < b then ENNReal.ofReal |Real.log (a / b)|
  else ⊤

/-- `δᵢ(v, w) = max_{∅ ≠ B ⊆ M} ld(vᵢ(B), wᵢ(B))`, Definition 2.3, p.7. -/
noncomputable def deltaI (v w : Profile n m) (i : Fin n) : ℝ≥0∞ :=
  ⨆ (B : Finset (Fin m)) (_ : B ≠ ∅), ld (v i B) (w i B)

/-- `d(v, w) = Σᵢ δᵢ(v, w)`, Definition 2.3, p.7. -/
noncomputable def profileDist (v w : Profile n m) : ℝ≥0∞ :=
  ∑ i, deltaI v w i

end LipStableCA


