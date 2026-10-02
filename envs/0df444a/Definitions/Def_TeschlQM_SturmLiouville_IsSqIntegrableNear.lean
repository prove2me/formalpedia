-- Prove2me | Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear
-- name    : TeschlQM_SturmLiouville_IsSqIntegrableNear
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:44:38.561324+00:00
-- url     : https://prove2.me/theorems/a04ec407-431c-40b9-92dc-5f02cf6b50ac
-- title:
--   Square integrability near an endpoint
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data. A function $u$ is **square integrable near $a$** if $u \in L^2((a,c), r\,dx)$ for some $c \in I$, i.e.
--   $$\int_a^c |u(x)|^2\, r(x)\,dx < \infty,$$
--   and **square integrable near $b$** if $u \in L^2((c,b), r\,dx)$ for some $c \in I$. The weight is $r$.
--
--   For solutions of $(\tau - z)u = 0$, which are continuous on $I$, "for some $c$" and "for every $c$" agree.
--
--   **Formalization Note.** `IsSqIntegrableNearLeft L u` is `MemLp u 2` for the measure $r\,dx$ restricted to $(a,c)$, for some $c \in I$; similarly on the right.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 188, 191, Section 9.2, Lemma 9.7 and Theorem 9.9

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_SLData

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl, pp. 188, 191: `u` is *square integrable near `a`*, i.e. `u ∈ L²((a, c), r dx)` for
some `c ∈ I`: `∫_a^c |u(x)|² r(x) dx < ∞` (with `u` a.e.-strongly measurable there). -/
def IsSqIntegrableNearLeft (L : SLData) (u : ℝ → ℂ) : Prop :=
  ∃ c ∈ L.I, MemLp u 2 ((volume.restrict {x : ℝ | L.a < (x : EReal) ∧ x < c}).withDensity
    (fun x => ENNReal.ofReal (L.r x)))

/-- Teschl, pp. 188, 191: `u` is square integrable near `b`, i.e. `u ∈ L²((c, b), r dx)` for some
`c ∈ I`. -/
def IsSqIntegrableNearRight (L : SLData) (u : ℝ → ℂ) : Prop :=
  ∃ c ∈ L.I, MemLp u 2 ((volume.restrict {x : ℝ | c < x ∧ (x : EReal) < L.b}).withDensity
    (fun x => ENNReal.ofReal (L.r x)))

end TeschlQM.SturmLiouville


