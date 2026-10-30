-- Prove2me | Definitions.Def_PorteusGenSS_InCa
-- name    : PorteusGenSS_InCa
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:12:46.220279+00:00
-- url     : https://prove2.me/theorems/307f4795-bca4-4701-a7e0-e85851a16f9d
-- title:
--   The class $C_a(K)$
-- statement:
--   Let $K\ge0$ and $a\in\mathbb R$. A function $f:\mathbb R\to\mathbb R$ belongs to **$C_a(K)$** if, for some $I\in\{(-\infty,a),(-\infty,a]\}$, $f$ is
--
--   1. piecewise continuous,
--   2. PF-integrable,
--   3. nonincreasing on $I$,
--   4. non-$K$-decreasing on $\mathbb R\setminus I$,
--
--   and 5. $f(x)\to\infty$ as $|x|\to\infty$.
--
--   **Formalization Note** $|x|\to\infty$ is the cocompact filter of $\mathbb R$; the requirement $K\ge0$ is part of membership.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 2, p. 414

import Mathlib
import Definitions.Def_PorteusGenSS_NonKDecreasingOn
import Definitions.Def_PorteusGenSS_PiecewiseContinuous
import Definitions.Def_PorteusGenSS_PFIntegrable

open Filter

namespace PorteusGenSS

/-- **The class C_a(K) (Definition 2).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 2, p. 414: "Let Ca(K), for K ≥ 0 and a ∈ R, denote the class of functions f
which, for some I ∈ {(−∞, a), (−∞, a]}, are (i) piecewise continuous, (ii) PF-integrable,
(iii) nonincreasing on I, (iv) non-K-decreasing on R − I, and which satisfy (v) f(x) → ∞ as
|x| → ∞."

`InCa K a f` says `0 ≤ K` and, for `I = (−∞, a)` or `I = (−∞, a]`, `f` is piecewise continuous,
PF-integrable, nonincreasing on `I`, non-K-decreasing on `ℝ ∖ I`, and `f x → ∞` as `|x| → ∞`.

**Formalization Note.** "Nonincreasing" is `AntitoneOn`. "|x| → ∞" is the cocompact filter of
`ℝ` (both `x → −∞` and `x → +∞`). The class is only defined for `K ≥ 0`, which is therefore part
of membership. -/
def InCa (K a : ℝ) (f : ℝ → ℝ) : Prop :=
  0 ≤ K ∧ ∃ I : Set ℝ, (I = Set.Iio a ∨ I = Set.Iic a) ∧ PiecewiseContinuous f ∧ PFIntegrable f ∧
    AntitoneOn f I ∧ NonKDecreasingOn K f Iᶜ ∧ Tendsto f (cocompact ℝ) atTop

end PorteusGenSS


