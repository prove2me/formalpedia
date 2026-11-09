-- Prove2me | Definitions.Def_SkipListConc_servedHeight
-- name    : SkipListConc_servedHeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:26.977025+00:00
-- url     : https://prove2.me/theorems/416dd5cb-2f0d-40c5-a8a4-49a8e83cc77a
-- title:
--   Served height $s_t=H_{x_t}(f_t-1)$
-- statement:
--   The **served height** of operation $t$ is $s_t=H_{x_t}(f_t-1)$, the height at which its search finds its target $x_t$, i.e. the height that the previous operation on $x_t$ left. For an insertion $s_t=H_{x_t}(0)=1$.
--
--   **Formalization Note** Operations are indexed by $t\in\{0,\dots,F-1\}$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, p.5

import Mathlib
import Definitions.Def_SkipListConc_heightAt

namespace SkipListConc

/-- The served height `s_t = H_{x_t}(f_t − 1)` of operation `t` (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), §1.1, p.5): the height at which the search of operation `t` finds its target
`x_t = σ[t]`; it is `1` for an insertion.

**Formalization Note** Operations are indexed by `t : Fin σ.length` (0-based). -/
noncomputable def servedHeight (p : ℝ) {K : ℕ} {α Ω : Type*} [DecidableEq α]
    (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (σ : List α) (t : Fin σ.length) (ω : Ω) : ℕ :=
  heightAt p ξ σ t (σ.get t) ω

end SkipListConc


