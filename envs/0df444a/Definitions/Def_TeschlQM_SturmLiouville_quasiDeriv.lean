-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_quasiDeriv
-- name    : TeschlQM_SturmLiouville_quasiDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:41:24.001609+00:00
-- url     : https://prove2.me/theorems/c36ff2c1-de25-4021-99af-10701349e301
-- title:
--   The quasi-derivative $pf'$ with $f, pf' \in AC_{loc}(I)$
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data. For $f : I \to \mathbb{C}$ we say that $f, pf' \in AC_{loc}(I)$ with **quasi-derivative** $f^{[1]} = pf'$ if $f^{[1]} \in AC_{loc}(I)$, $f^{[1]}/p \in L^1_{loc}(I)$ and
--   $$f(y) - f(x) = \int_x^y \frac{f^{[1]}(t)}{p(t)}\,dt, \qquad x, y \in I.$$
--   Then $f \in AC_{loc}(I)$ and $pf' = f^{[1]}$ almost everywhere; $f^{[1]}$ is the continuous representative of $pf'$ that the book evaluates pointwise, as in $(pf')(c)$ and in the Wronskian. On $I$ it is uniquely determined by $f$.
--
--   **Formalization Note.** `IsQuasiDerivative L f f1` is the property above, and `quasiDeriv L f` is a choice of such an $f^{[1]}$ (unique on $I$). It is $0$ when no such function exists; every statement of the mission applies it only to functions with $f, pf' \in AC_{loc}(I)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 181, Section 9.1, Eq. (9.1)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_SLData
import Definitions.Def_TeschlQM_SturmLiouville_IsACloc

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl (9.1), p. 181: `f, p f′ ∈ AC_loc(I)` with `f1 = p f′`. That is, `f1` is locally
absolutely continuous on `I`, `f1 / p` is locally integrable on `I`, and `f` is its integral:
`f(y) − f(x) = ∫_x^y f1(t)/p(t) dt` for `x, y ∈ I` (so `f ∈ AC_loc(I)` and `f′ = f1/p` a.e.).
`f1` is the continuous representative of `p f′` used in `(p f′)(c)` and in the Wronskian. -/
def IsQuasiDerivative (L : SLData) (f f1 : ℝ → ℂ) : Prop :=
  IsACloc L.I f1 ∧ LocallyIntegrableOn (fun t => f1 t / (L.p t : ℂ)) L.I ∧
    ∀ x ∈ L.I, ∀ y ∈ L.I, f y - f x = ∫ t in x..y, f1 t / (L.p t : ℂ)

/-- The quasi-derivative `p f′` of `f` (Teschl writes `(p f′)(x)`). On `I` it is uniquely
determined by `f` whenever `f, p f′ ∈ AC_loc(I)` (two continuous functions equal a.e. on `I`
agree on `I`); it is chosen by `Classical.choose`. It is `0` if `f` has no locally absolutely
continuous quasi-derivative; every statement of the mission applies it only to such `f`. -/
noncomputable def quasiDeriv (L : SLData) (f : ℝ → ℂ) : ℝ → ℂ :=
  open Classical in
  if h : ∃ f1, IsQuasiDerivative L f f1 then h.choose else 0

end TeschlQM.SturmLiouville


