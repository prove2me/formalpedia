-- Prove2me | Definitions.Def_SkipListConc_heightAt
-- name    : SkipListConc_heightAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:18.71543+00:00
-- url     : https://prove2.me/theorems/2ed2a845-3851-46dc-8d2d-1aef06f6584c
-- title:
--   Height of an item during the search of operation $t$
-- statement:
--   During the search of operation $t$, every present item $y$ is at height $H_y(\mathrm{opCount}(\sigma,y,t))$: an item other than the target is at $H_y(f_y(t))$, and the target $x_t$ is at its **served height** $s_t=H_{x_t}(f_t-1)$, since operation $t$ searches before it promotes.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, p.5

import Mathlib
import Definitions.Def_SkipListConc_height
import Definitions.Def_SkipListConc_opCount

namespace SkipListConc

/-- The height of item `y` during the search of operation `t` (0-based) of `σ` (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), §1.1, p.5): `H_y(f_y(t))` for an item other than the target, and the
served height `s_t = H_{x_t}(f_t − 1)` for the target, since the search precedes the promotion.
Both are `H_y` evaluated at the number of operations on `y` strictly before `t`. -/
noncomputable def heightAt (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (t : ℕ) (y : α) (ω : Ω) : ℕ :=
  height p ξ y (opCount σ y t) ω

end SkipListConc


