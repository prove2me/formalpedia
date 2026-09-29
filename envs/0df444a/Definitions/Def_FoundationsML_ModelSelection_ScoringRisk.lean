-- Prove2me | Definitions.Def_FoundationsML_ModelSelection_ScoringRisk
-- name    : FoundationsML_ModelSelection_ScoringRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:49.419973+00:00
-- url     : https://prove2.me/theorems/40e9b667-4ce7-40fd-9aa3-2f904728c602
-- title:
--   Classification risk of a real-valued scoring function
-- statement:
--   **p. 74, PDF p. 91.** For a real-valued hypothesis $h:X\to\mathbb R$ with sign convention
--   $f_h(x)=+1$ iff $h(x)\ge0$, the book derives (and subsequently uses)
--   $R(h) = \mathbb E_{x\sim D_X}[\eta(x)\mathbb 1_{h(x)<0} + (1-\eta(x))\mathbb 1_{h(x)\ge0}]$
--   as an equivalent form of $R(h)=\mathbb E_{(x,y)\sim D}[\mathbb 1_{f_h(x)\ne y}]$; this is the
--   form Lemma 4.5's and Theorem 4.7's proofs work with directly.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 74 (PDF p. 91)

import Mathlib

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- The classification risk of a real-valued scoring function `h : X → ℝ` under the sign
convention `f_h(x) = +1` iff `h(x) ≥ 0`, expressed via the conditional label probability
`η(x) = P[y = +1 | x]` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*,
2nd ed., MIT Press 2018, p. 74, PDF p. 91, the derived form of `R(h) = E_{(x,y)∼D}[1_{f_h(x)≠y}]`
that the book establishes and uses throughout §4.7):
`R(h) = E_{x∼D_X}[η(x) 1_{h(x)<0} + (1 − η(x)) 1_{h(x)≥0}]`. -/
noncomputable def ScoringRisk {X : Type*} [MeasurableSpace X]
    (DX : Measure X) (η : X → ℝ) (h : X → ℝ) : ℝ :=
  ∫ x, (η x * (if h x < 0 then (1 : ℝ) else 0) +
    (1 - η x) * (if h x ≥ 0 then (1 : ℝ) else 0)) ∂DX

end FoundationsML.ModelSelection


