-- Prove2me | Definitions.Def_FoundationsML_SVM_MarginGeneralizationError
-- name    : FoundationsML_SVM_MarginGeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:27:47.161112+00:00
-- url     : https://prove2.me/theorems/8fedec2d-608a-4890-941c-f6f09b32e21f
-- title:
--   Generalization error of a real-valued (confidence-margin) hypothesis
-- statement:
--   **Definition 2.1 (Generalization error), p. 11, PDF p. 28, specialized to a real-valued
--   confidence-margin classifier as used in the proof of Theorem 5.8, p. 94, PDF p. 111.** For a
--   real-valued hypothesis $h:X\to\mathbb R$ and a label $y\in\mathbb R$ drawn jointly from a
--   distribution $D$ on $X\times\mathbb R$, $R(h)=\Pr_{(x,y)\sim D}[y\,h(x)\le 0]$: the
--   probability that $h$'s sign disagrees with (or ties) the true label's sign.
--
--   **Formalization Note.** Restated locally in `SVM` for this chapter's real-valued (rather
--   than $\{-1,+1\}$-valued) hypothesis convention; drafts cannot import another chunk's draft
--   module, and no chunk of this series has yet drafted a real-valued-margin generalization
--   error.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 11, Definition 2.1 (PDF p. 28), specialized p. 94, PDF p. 111

import Mathlib

open MeasureTheory

namespace FoundationsML.SVM

/-- The generalization error of a real-valued hypothesis `h : X → ℝ`, measured through its
sign against a real-valued label `y` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Definition 2.1, p. 11, PDF p. 28, specialized to a
confidence-margin classifier as used in the proof of Theorem 5.8, p. 94, PDF p. 111, where
`R(h) = P_{(x,y)∼D}[y h(x) ≤ 0]` — restated locally for this chapter since drafts cannot
import another chunk's draft module). -/
noncomputable def MarginGeneralizationError {X : Type*} [MeasurableSpace X]
    (D : Measure (X × ℝ)) (h : X → ℝ) : ℝ :=
  (D {p : X × ℝ | p.2 * h p.1 ≤ 0}).toReal

end FoundationsML.SVM


