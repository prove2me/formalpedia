-- Prove2me | Definitions.Def_SkipListConc_Wlev
-- name    : SkipListConc_Wlev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:54:26.485193+00:00
-- url     : https://prove2.me/theorems/d4ce42b4-ed77-4d74-9e15-09b2610baed7
-- title:
--   $W_{\mathrm{lev}}=\sum_{\ell=1}^{L}W_\ell$
-- statement:
--   For a cutoff $L\ge1$, $W_{\mathrm{lev}}=\sum_{\ell=1}^{L}W_\ell$, the number of pairs (charge, level) with $s_t\le\ell\le L$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.12, p.27

import Mathlib
import Definitions.Def_SkipListConc_levelW

namespace SkipListConc

/-- `W_lev = ∑_{ℓ=1}^{L} W_ℓ` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), Lemma 4.12,
p.27). -/
noncomputable def Wlev (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (L : ℕ) (ω : Ω) : ℕ :=
  ∑ ℓ ∈ Finset.Icc 1 L, levelW p ξ σ ℓ ω

end SkipListConc


