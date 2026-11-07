-- Prove2me | Definitions.Def_OnlineCAP_IsLeftless
-- name    : OnlineCAP_IsLeftless
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:34.279271+00:00
-- url     : https://prove2.me/theorems/8d080d7a-ed1b-42c6-9fe4-82f0974ad785
-- title:
--   Leftless rectangle
-- statement:
--   A **leftless rectangle** is a region
--   $$R_L=\{(x,y)\in\mathbb R^2 : x\le a,\ b\le y\le c\}=(-\infty,a]\times[b,c]$$
--   for some $a,b,c\in\mathbb R$ (empty when $b>c$).
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Definition 1.8, p.4

import Mathlib

namespace OnlineCAP

/-- **Leftless rectangle.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Definition 1.8, p.4 (PDF p.4): "A leftless rectangle is a region
RL = {(x, y) ∈ R2 : x ≤ a, b ≤ y ≤ c} = (−∞, a] × [b, c] for some a, b, c ∈ R."

**Formalization Note.** `b > c` gives the empty rectangle, as in the definition. -/
def IsLeftless (S : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c : ℝ, S = Set.Iic a ×ˢ Set.Icc b c

end OnlineCAP


