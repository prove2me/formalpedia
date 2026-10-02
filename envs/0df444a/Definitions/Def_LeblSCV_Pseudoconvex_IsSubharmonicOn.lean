-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsSubharmonicOn
-- name    : LeblSCV_Pseudoconvex_IsSubharmonicOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:42:09.257051+00:00
-- url     : https://prove2.me/theorems/c16a809a-046c-49fd-90e8-175ea71dd49d
-- title:
--   Definition 2.4.1 — subharmonic function (on an open subset of ℂ)
-- statement:
--   Let $U \subset \mathbb{C}$ be open. A function $f : U \to \mathbb{R} \cup \{-\infty\}$ is **subharmonic** if it is upper-semicontinuous and the following holds. Take any disc $B_r(a)$ with $r > 0$ and $\overline{B_r(a)} \subset U$, and any function $g$ that is continuous on $\overline{B_r(a)}$ and harmonic on $B_r(a)$. If
--   $$f(x) \le g(x) \quad \text{for } x \in \partial B_r(a),$$
--   then $f(x) \le g(x)$ for all $x \in B_r(a)$.
--
--   In other words, $f$ lies below every harmonic function on every disc wherever that holds on the boundary circle. This is the one-variable model of plurisubharmonicity.
--
--   **Formalization Note.** Values in $\mathbb{R}\cup\{-\infty\}$ are modelled in `EReal` together with the requirement $f \neq +\infty$ on $U$; upper semicontinuity is Mathlib's `UpperSemicontinuousOn` for the order of `EReal`. Only the case $n = 2$ ($\mathbb{C}$) of the book's definition is formalized. It is the case every later result of the chapter uses. The constant $-\infty$ is subharmonic under this definition, as it is in the book.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 78, Definition 2.4.1

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsHarmonicOn

namespace LeblSCV.Pseudoconvex

/-- Definition 2.4.1, second part (Lebl, p. 78), for open `U ⊂ ℂ`: a function
`f : U → ℝ ∪ {−∞}` is *subharmonic* if it is upper-semicontinuous and for every ball `B_r(a)`
with `closure B_r(a) ⊂ U`, and every `g` continuous on `closure B_r(a)` and harmonic on `B_r(a)`
with `f ≤ g` on `∂B_r(a)`, we have `f ≤ g` on `B_r(a)`.
Values in `ℝ ∪ {−∞}` are modelled in `EReal` with the value `⊤ = +∞` excluded on `U`. -/
def IsSubharmonicOn (f : ℂ → EReal) (U : Set ℂ) : Prop :=
  UpperSemicontinuousOn f U ∧ (∀ z ∈ U, f z ≠ ⊤) ∧
    ∀ (a : ℂ) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ U →
      ∀ g : ℂ → ℝ, ContinuousOn g (Metric.closedBall a r) → IsHarmonicOn g (Metric.ball a r) →
        (∀ x ∈ Metric.sphere a r, f x ≤ (g x : EReal)) →
          ∀ x ∈ Metric.ball a r, f x ≤ (g x : EReal)

end LeblSCV.Pseudoconvex


