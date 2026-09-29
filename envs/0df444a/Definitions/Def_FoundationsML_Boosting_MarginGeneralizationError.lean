-- Prove2me | Definitions.Def_FoundationsML_Boosting_MarginGeneralizationError
-- name    : FoundationsML_Boosting_MarginGeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:08:16.412677+00:00
-- url     : https://prove2.me/theorems/b9cf7a61-e14a-4c7e-a4bb-0868a2573c13
-- title:
--   Generalization error of a real-valued (confidence-margin) hypothesis
-- statement:
--   **Definition 2.1, p. 11, PDF p. 28, specialized to the real-valued confidence-margin
--   convention of Chapter 5, reused for the ensemble margin bounds of §7.3.3, p. 158, PDF p.
--   175 (restated locally for this chapter).** $R(h)=\Pr_{(x,y)\sim D}[y\,h(x)\le 0]$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 11, Definition 2.1 (PDF p. 28), specialized p. 158, PDF p. 175

import Mathlib

open MeasureTheory

namespace FoundationsML.Boosting

/-- The generalization error of a real-valued hypothesis `h : X → ℝ`, measured through its
sign against a real-valued label `y` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 2.1, p. 11, PDF p. 28, specialized to a
confidence-margin classifier as in Chapter 5 and reused for the ensemble margin bounds of
§7.3.3, p. 158, PDF p. 175 — restated locally for this chapter since drafts cannot import
another chunk's draft module): `R(h) = P_{(x,y)∼D}[y h(x) ≤ 0]`. -/
noncomputable def MarginGeneralizationError {X : Type*} [MeasurableSpace X]
    (D : Measure (X × ℝ)) (h : X → ℝ) : ℝ :=
  (D {p : X × ℝ | p.2 * h p.1 ≤ 0}).toReal

end FoundationsML.Boosting


