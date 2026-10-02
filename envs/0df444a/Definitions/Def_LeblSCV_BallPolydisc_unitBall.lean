-- Prove2me | Definitions.Def_LeblSCV_BallPolydisc_unitBall
-- name    : LeblSCV_BallPolydisc_unitBall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:15:51.362304+00:00
-- url     : https://prove2.me/theorems/379cb557-6bad-42e7-a354-c11c36b10c45
-- title:
--   Unit ball $\mathbb{B}_n$ (Euclidean norm)
-- statement:
--   For $n \ge 0$, the **unit ball** of $\mathbb{C}^n$ is
--   $$\mathbb{B}_n = \{ z \in \mathbb{C}^n : \|z\| < 1 \} = \{ z \in \mathbb{C}^n : |z_1|^2 + |z_2|^2 + \cdots + |z_n|^2 < 1 \},$$
--   where $\|z\|$ is the Euclidean norm of $z = (z_1, \dots, z_n)$.
--
--   Together with the polydisc it is one of the two most obvious generalizations of the unit disc to several variables; the two are homeomorphic but, as this mission shows, not biholomorphic.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`. Its Mathlib norm is the sup norm, whose unit ball is the polydisc, so the Euclidean condition $\sum_k |z_k|^2 < 1$ is written out explicitly.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 32 (display defining 𝔹_n and 𝔻^n), with the Euclidean norm of pp. 13–14

import Mathlib

namespace LeblSCV.BallPolydisc

/-- The unit ball `𝔹_n = {z ∈ ℂⁿ : ‖z‖ < 1}` of Lebl, p. 32, for the **Euclidean** norm
`‖z‖ = (|z_1|² + ⋯ + |z_n|²)^{1/2}` (p. 13–14). Written out explicitly because the Mathlib norm on
`Fin n → ℂ` is the sup norm, whose unit ball is the polydisc `𝔻ⁿ`. -/
def unitBall (n : ℕ) : Set (Fin n → ℂ) :=
  {z | ∑ k : Fin n, ‖z k‖ ^ 2 < 1}

end LeblSCV.BallPolydisc


