-- Prove2me | Definitions.Def_SkipListConc_levelInfo
-- name    : SkipListConc_levelInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:44.950143+00:00
-- url     : https://prove2.me/theorems/8eba876b-19cc-41b2-afe9-a3ab00d21ba4
-- title:
--   Level filtration $\mathcal F_\ell=(T^\ell_y)_y$
-- statement:
--   The **level information** $\mathcal F_\ell=(T^\ell_y)_y$ is the list of the truncated trajectories of all items of $\sigma$. A quantity is **determined by $\mathcal F_\ell$** if it is a function of this list. Since $\min(z,\ell)$ is a function of $\min(z,\ell+1)$, the lists form a filtration; each takes finitely many values.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §3.3, p.18

import Mathlib
import Definitions.Def_SkipListConc_truncTraj

namespace SkipListConc

/-- The level information `F_ℓ = (T^ℓ_y)_y`, the list of the truncated trajectories of all items
of `σ` (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §3.3, p.18). A quantity is determined by `F_ℓ`
if it is a function of this list.

**Formalization Note** A dependent function on the items of `σ`; it takes finitely many values. -/
noncomputable def levelInfo (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (ℓ : ℕ) (ω : Ω) :
    (y : σ.toFinset) → Fin (σ.count (y : α) + 1) → ℕ :=
  fun y => truncTraj p ξ σ ℓ y ω

end SkipListConc


