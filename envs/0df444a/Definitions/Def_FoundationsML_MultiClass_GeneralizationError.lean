-- Prove2me | Definitions.Def_FoundationsML_MultiClass_GeneralizationError
-- name    : FoundationsML_MultiClass_GeneralizationError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:28:06.078018+00:00
-- url     : https://prove2.me/theorems/f9651e3c-1b42-4be0-8fad-1788ed7568d9
-- title:
--   Generalization error (mono-label multi-class risk)
-- statement:
--   **Eq. (9.1), p. 214, PDF p. 231.** For a target labeling function $f:X\to Y$ and scoring
--   function $h:X\times Y\to\mathbb R$, the mono-label generalization error is
--   $R(h) = \Pr_{x\sim D}[h(x)\ne f(x)]$, where $h(x)=\arg\max_y h(x,y)$.
--
--   **Formalization Note.** Using the book's own equivalence "$h$ misclassifies $(x,y)$ iff
--   $\rho_h(x,y)\le0$" (p. 215), `GeneralizationError D f h` is
--   `(D {x | MarginFunction h x (f x) ≤ 0}).toReal`, the form the chapter's own proof of
--   Theorem 9.2 works with directly.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (9.1), p. 214 (PDF p. 231)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_MarginFunction

open MeasureTheory

namespace FoundationsML.MultiClass

/-- The generalization error (risk) of a multi-class scoring function `h : X × Y → ℝ` against
a target labeling function `f : X → Y`, in the mono-label case (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq. (9.1), p. 214, PDF
p. 231): `R(h) = P_{x∼D}[h(x) ≠ f(x)]`, where `h(x) = argmax_y h(x,y)` is the classifier
induced by `h`.

**Formalization Note.** Using the book's own established equivalence "`h` misclassifies `(x,y)`
iff `ρ_h(x,y) ≤ 0`" (p. 215, PDF p. 232), `R(h)` is formalized directly as
`P_{x∼D}[ρ_h(x,f(x)) ≤ 0]` via `MarginFunction`, rather than via an explicit `argmax`
classifier; this is the form the chapter's own proof of Theorem 9.2 works with throughout
(`R(h) = E[1_{ρ_h(x,y)≤0}]`, displayed explicitly in the proof on PDF p. 234), not a
weakening. -/
noncomputable def GeneralizationError {X Y : Type*} [MeasurableSpace X]
    (D : Measure X) (f : X → Y) (h : X × Y → ℝ) : ℝ :=
  (D {x | MarginFunction h x (f x) ≤ 0}).toReal

end FoundationsML.MultiClass


