-- Prove2me | Definitions.Def_OnlineCAP_IsTopless
-- name    : OnlineCAP_IsTopless
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:32.816836+00:00
-- url     : https://prove2.me/theorems/b9118cfd-e398-4c5f-bd80-04e5db6d70ac
-- title:
--   Topless rectangle
-- statement:
--   A **topless rectangle** is a region
--   $$R_T=\{(x,y)\in\mathbb R^2 : a\le x\le b,\ c\le y\}=[a,b]\times[c,\infty)$$
--   for some $a,b,c\in\mathbb R$ (empty when $a>b$).
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Definition 1.8, p.4

import Mathlib

namespace OnlineCAP

/-- **Topless rectangle.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Definition 1.8, p.4 (PDF p.4): "A topless rectangle is a region
RT = {(x, y) ∈ R2 : a ≤ x ≤ b, c ≤ y} for some a, b, c ∈ R. Equivalently, RT = [a, b] × [c, ∞)."

**Formalization Note.** `a > b` gives the empty rectangle, as in the definition. -/
def IsTopless (S : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c : ℝ, S = Set.Icc a b ×ˢ Set.Ici c

end OnlineCAP


