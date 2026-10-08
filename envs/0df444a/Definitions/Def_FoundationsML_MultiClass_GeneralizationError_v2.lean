-- Prove2me | Definitions.Def_FoundationsML_MultiClass_GeneralizationError_v2
-- name    : FoundationsML_MultiClass_GeneralizationError_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:32:20.27332+00:00
-- url     : https://prove2.me/theorems/5ae4a537-0338-42d3-9eb3-d9bcc9c590d0
-- title:
--   Multi-class generalization error (Eq. 9.1) — re-issued on the corrected margin
-- statement:
--   **Generalization error, mono-label multi-class case (Eq. (9.1), p. 214, PDF p. 231).** For a scoring function $h : X\times Y\to\mathbb R$ and target labeling $f : X\to Y$, $R(h) = \mathbb P_{x\sim D}[h(x)\neq f(x)]$ with $h(x)=\operatorname{argmax}_y h(x,y)$, formalized through the book's equivalence (p. 215) as $\mathbb P_{x\sim D}[\rho_h(x,f(x))\le 0]$.
--
--   **Formalization Note.** Identical to the retired module except that it is built on the corrected `MarginFunction` (`_v2`, maximum over exactly the labels $y'\neq y$); it must be re-issued because a Lean theorem cannot import both the old and the corrected `MarginFunction` (same full name).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (9.1), p. 214 (PDF p. 231)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_MarginFunction_v2

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
weakening. Re-issued on top of the corrected `MarginFunction` (module
`..._MarginFunction_v2`, maximum over exactly the labels `y' ≠ y`). -/
noncomputable def GeneralizationError {X Y : Type*} [MeasurableSpace X]
    (D : Measure X) (f : X → Y) (h : X × Y → ℝ) : ℝ :=
  (D {x | MarginFunction h x (f x) ≤ 0}).toReal

end FoundationsML.MultiClass


