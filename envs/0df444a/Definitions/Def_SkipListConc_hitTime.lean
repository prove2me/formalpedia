-- Prove2me | Definitions.Def_SkipListConc_hitTime
-- name    : SkipListConc_hitTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:48.8786+00:00
-- url     : https://prove2.me/theorems/9e3aa1a2-3273-45d7-be80-1ddb7826d301
-- title:
--   Morris hitting time $\tau_\ell$
-- statement:
--   The **hitting time** of level $\ell$ by the Morris chain of $x$ is
--   $$
--   \tau_\ell=\min\{j\ge 1:\ M_x(j)\ge \ell\},
--   $$
--   so $\tau_1=1$.
--
--   **Formalization Note** Valued in $\mathbb N\cup\{\infty\}$, with $\tau_\ell=\infty$ on the null event that the chain never reaches $\ell$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 2.6, p.15

import Mathlib
import Definitions.Def_SkipListConc_morris

namespace SkipListConc

open Classical in
/-- The Morris hitting time `τ_ℓ = min {j ≥ 1 : M_x(j) ≥ ℓ}` (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), Lemma 2.6, p.15). So `τ_1 = 1`.

**Formalization Note** Valued in `ℕ∞`, with `τ_ℓ = ⊤` on the (null) event that the chain never
reaches `ℓ`. -/
noncomputable def hitTime (p : ℝ) {K : ℕ} {α Ω : Type*}
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (x : α) (ℓ : ℕ) (ω : Ω) : ℕ∞ :=
  if h : ∃ j, 1 ≤ j ∧ ℓ ≤ morris p ξ x j ω then (Nat.find h : ℕ∞) else ⊤

end SkipListConc


