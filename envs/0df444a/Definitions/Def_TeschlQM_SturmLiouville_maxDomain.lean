-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_maxDomain
-- name    : TeschlQM_SturmLiouville_maxDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:42:53.633148+00:00
-- url     : https://prove2.me/theorems/fb68e5f9-ef41-4b64-9af7-740f11d58615
-- title:
--   The maximal domain $\mathfrak{D}(\tau)$ (9.3)
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data. The **maximal domain** of $\tau$ in $L^2(I, r\,dx)$ is
--   $$\mathfrak{D}(\tau) = \{ f \in L^2(I, r\,dx) \mid f, pf' \in AC_{loc}(I),\ \tau f \in L^2(I, r\,dx) \}.$$
--
--   All boundary Wronskians, the limit circle/limit point notion and the self-adjoint realizations of $\tau$ are defined in terms of $\mathfrak{D}(\tau)$.
--
--   **Formalization Note.** `InMaxDomain L f` is a predicate on functions $f : \mathbb{R} \to \mathbb{C}$ (the $AC_{loc}$ representative): $f \in L^2(I, r\,dx)$ and there is $g \in L^2(I, r\,dx)$ with $\tau f = g$ in the sense of `SolvesTau`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 182, Section 9.1, Eq. (9.3)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_SolvesTau

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl (9.3), p. 182: the maximal domain
`D(τ) = {f ∈ L²(I, r dx) | f, p f′ ∈ AC_loc(I), τ f ∈ L²(I, r dx)}`.
`f` is a function (the `AC_loc` representative), `L.measure` is `r dx` on `I`. -/
def InMaxDomain (L : SLData) (f : ℝ → ℂ) : Prop :=
  MemLp f 2 L.measure ∧ ∃ g : ℝ → ℂ, SolvesTau L f g ∧ MemLp g 2 L.measure

end TeschlQM.SturmLiouville


