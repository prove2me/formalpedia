-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_SolvesTau
-- name    : TeschlQM_SturmLiouville_SolvesTau
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:42:06.750062+00:00
-- url     : https://prove2.me/theorems/6f437144-31cb-460f-9fb4-d19ea13e8721
-- title:
--   The equations $\tau f = g$ and $(\tau - z)f = g$ (9.1), (9.8)
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data. For functions $f, g$ on $I$, **$\tau f = g$** means: $f, pf' \in AC_{loc}(I)$ and
--   $$-(pf')' + q f = r g \quad \text{a.e. on } I,$$
--   that is, $qf - rg \in L^1_{loc}(I)$ and $(pf')(y) - (pf')(x) = \int_x^y (q f - r g)(t)\,dt$ for $x, y \in I$. For $z \in \mathbb{C}$, $f$ is a **solution of** $(\tau - z) f = g$ if $\tau f = z f + g$ in this sense; for $g = 0$ these are the solutions of $\tau u = z u$.
--
--   Solutions are complex-valued and taken in the class $AC_{loc}(I)$, with $L^1_{loc}$ coefficients.
--
--   **Formalization Note.** `SolvesTau L f g` is $\tau f = g$; `IsSolution L z g f` is $(\tau - z) f = g$. The quasi-derivative is `quasiDeriv L f`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 181–182, Section 9.1, Eqs. (9.1), (9.8)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_quasiDeriv

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl (9.1), p. 181: `f, p f′ ∈ AC_loc(I)` and `τ f = g` a.e. on `I`, where
`τ f = (1/r)(−(p f′)′ + q f)`. Since `r > 0` this says `(p f′)′ = q f − r g` a.e., encoded as:
`q f − r g ∈ L¹_loc(I)` and `(p f′)(y) − (p f′)(x) = ∫_x^y (q f − r g)(t) dt` for `x, y ∈ I`. -/
def SolvesTau (L : SLData) (f g : ℝ → ℂ) : Prop :=
  IsQuasiDerivative L f (quasiDeriv L f) ∧
    LocallyIntegrableOn (fun t => (L.q t : ℂ) * f t - (L.r t : ℂ) * g t) L.I ∧
    ∀ x ∈ L.I, ∀ y ∈ L.I, quasiDeriv L f y - quasiDeriv L f x =
      ∫ t in x..y, ((L.q t : ℂ) * f t - (L.r t : ℂ) * g t)

/-- Teschl (9.8), p. 182: `f` is a solution of `(τ − z) f = g`, i.e. `τ f = z f + g`, with
`f, p f′ ∈ AC_loc(I)`. For `g = 0` this is `τ u = z u`. -/
def IsSolution (L : SLData) (z : ℂ) (g f : ℝ → ℂ) : Prop :=
  SolvesTau L f (fun x => z * f x + g x)

end TeschlQM.SturmLiouville


