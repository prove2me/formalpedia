-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_IsACloc
-- name    : TeschlQM_SturmLiouville_IsACloc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:40:42.960766+00:00
-- url     : https://prove2.me/theorems/1d69da1d-7b03-4885-8f97-dd952b8ded04
-- title:
--   Locally absolutely continuous functions $AC_{loc}(I)$
-- statement:
--   Let $I \subseteq \mathbb{R}$ be an open interval. A function $f : I \to \mathbb{C}$ is **locally absolutely continuous**, $f \in AC_{loc}(I)$, if it is absolutely continuous on every compact subinterval of $I$. Equivalently, there is $h \in L^1_{loc}(I)$ with
--   $$f(y) - f(x) = \int_x^y h(t)\,dt, \qquad x, y \in I;$$
--   then $f' = h$ almost everywhere.
--
--   This is the regularity class in which solutions of the Sturm–Liouville equation (9.1) are taken.
--
--   **Formalization Note.** The integral characterization (fundamental theorem of calculus for absolutely continuous functions) is used as the definition.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 181, Section 9.1, Eq. (9.1)

import Mathlib

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- `AC_loc(I)` for a complex-valued function on an open interval `I`: `f` is absolutely
continuous on every compact subinterval of `I`. Equivalently (fundamental theorem of calculus for
absolutely continuous functions), there is a locally integrable `h` on `I` with
`f(y) − f(x) = ∫_x^y h(t) dt` for all `x, y ∈ I`; `h` is then the a.e. derivative `f′`.
This integral form is the encoding used here. -/
def IsACloc (I : Set ℝ) (f : ℝ → ℂ) : Prop :=
  ∃ h : ℝ → ℂ, LocallyIntegrableOn h I ∧
    ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, h t

end TeschlQM.SturmLiouville


