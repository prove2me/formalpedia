-- Prove2me | Definitions.Def_AgnHalfMem_err
-- name    : AgnHalfMem_err
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:43.241001+00:00
-- url     : https://prove2.me/theorems/14231e5d-4ec0-4c63-bb9d-47a65b551290
-- title:
--   Error $\mathrm{err}(f,D)$ and optimal error $\mathrm{OPT}_{\mathcal H}(D)$
-- statement:
--   Let $D$ be a probability distribution on $X\times\{-1,1\}$ and $f:X\to\{-1,1\}$ a classifier. Its **error** and the **optimal error** of a class $\mathcal H$ are
--   $$
--   \mathrm{err}(f,D)=\Pr_{(x,y)\sim D}[f(x)\ne y],\qquad \mathrm{OPT}_{\mathcal H}(D)=\inf_{h\in\mathcal H}\mathrm{err}(h,D).
--   $$
--   Agnostic learning asks for a classifier whose error is within $\varepsilon$ of $\mathrm{OPT}_{\mathcal H}(D)$.
--
--   **Formalization Note** The infimum runs over the class only; it is used for nonempty classes, where it is the true infimum of numbers in $[0,1]$. The printed $\mathrm{err}(f,D)$ inside the infimum is a typo for $\mathrm{err}(h,D)$.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §2, p.6

import Mathlib

open MeasureTheory

namespace AgnHalfMem

/-- **Error and optimal error.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically
Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §2, p.6:
"For a distribution D over X × {−1, 1} and a classifier f : X → {−1, 1}, define
err(f, D) := Pr_{(x,y)∼D}[f(x) ≠ y], OPT_H(D) := inf_{h∈H} err(h, D)."

`err D f` is the probability under `D` that `f` disagrees with the label.

**Formalization Note.** Labels are `Bool` (`true ↔ +1`). `D` is used only for probability
measures; the value is `D` of the disagreement set, converted to a real number. The printed
`err(f, D)` inside the infimum of `OPT` is a typo for `err(h, D)`. -/
noncomputable def err {X : Type*} [MeasurableSpace X] (D : Measure (X × Bool)) (f : X → Bool) : ℝ :=
  (D {p | f p.1 ≠ p.2}).toReal

/-- `OPT_G(D) = inf_{g ∈ G} err(g, D)`, the infimum over the class `G` only (p.6).

**Formalization Note.** Wherever it is used the class `G` is nonempty (`H_d` with `d ≥ 1`, or a
class containing a nonempty family); the errors are bounded below by `0`, so the infimum is the
true infimum. -/
noncomputable def opt {X : Type*} [MeasurableSpace X] (D : Measure (X × Bool)) (G : Set (X → Bool)) : ℝ :=
  ⨅ g : G, err D g

end AgnHalfMem


