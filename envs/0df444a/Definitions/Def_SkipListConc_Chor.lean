-- Prove2me | Definitions.Def_SkipListConc_Chor
-- name    : SkipListConc_Chor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:54:22.671229+00:00
-- url     : https://prove2.me/theorems/29d085cc-34d5-487d-8115-54059a631c9e
-- title:
--   Horizontal cost $C_{\mathrm{hor}}=\sum_{\ell=1}^{L}C_\ell$
-- statement:
--   For a cutoff $L\ge 1$, the **horizontal cost of all searches below the cutoff** is $C_{\mathrm{hor}}=\sum_{\ell=1}^{L}C_\ell$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.12, p.27

import Mathlib
import Definitions.Def_SkipListConc_levelC

namespace SkipListConc

/-- The horizontal cost of all searches below the cutoff, `C_hor = ∑_{ℓ=1}^{L} C_ℓ`
(Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Lemma 4.12, p.27). -/
noncomputable def Chor (p : ℝ) {K : ℕ} {α Ω : Type*} [LinearOrder α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (L : ℕ) (ω : Ω) : ℕ :=
  ∑ ℓ ∈ Finset.Icc 1 L, levelC p ξ σ ℓ ω

end SkipListConc


