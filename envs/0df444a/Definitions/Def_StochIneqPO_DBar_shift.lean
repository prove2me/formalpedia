-- Prove2me | Definitions.Def_StochIneqPO_DBar_shift
-- name    : StochIneqPO_DBar_shift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:54.917343+00:00
-- url     : https://prove2.me/theorems/75b93339-afc0-40d1-8a0a-dddab12f60eb
-- title:
--   Sec. 7, p. 909 — shift of a two-sided path
-- statement:
--   A **two-sided path** in $E$ is a sequence $\omega=(\omega^n)_{n\in\mathbb Z}$. The shift $T$ moves the coordinate origin one step forward:
--
--   $$(T\omega)^n=\omega^{n+1}\qquad(n\in\mathbb Z).$$
--
--   This is the shift whose invariant laws are the stationary process laws in Sections 7 and 8.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Sec. 7, p. 909 and Sec. 8, p. 910 (PDF pp. 11–12)

import Mathlib

namespace StochIneqPO.DBar

/-- The left shift on two-sided paths: coordinate `n` after shifting is the old `n+1`. -/
def shift {E : Type*} (ω : ℤ → E) (n : ℤ) : E := ω (n + 1)

end StochIneqPO.DBar


