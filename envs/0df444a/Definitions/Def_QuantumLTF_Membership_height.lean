-- Prove2me | Definitions.Def_QuantumLTF_Membership_height
-- name    : QuantumLTF_Membership_height
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:46.587777+00:00
-- url     : https://prove2.me/theorems/339935a1-d3b4-4dac-abd2-c76ce62e5784
-- title:
--   The height function $h_p$
-- statement:
--   For $w,p\in\mathbb R^n$ with $\langle w,p\rangle\ne0$ and $z\in\mathbb R^n$, the height $h_p(z)$ is the unique scalar with $\langle w,z\rangle+h_p(z)\langle w,p\rangle=\theta$, so
--   $$h_p(z)=\frac{\theta-\langle w,z\rangle}{\langle w,p\rangle}.$$
--   It is an affine function with gradient $-w/\langle w,p\rangle$, which the paper's algorithm estimates.
--
--   **Formalization Note** Every statement using $h_p$ assumes $|\langle w,p\rangle|\ge1/10$, so the Lean value at $\langle w,p\rangle=0$ is never read.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §1.3, Eq. (4), p. 5 (PDF p. 6)

import Mathlib

namespace QuantumLTF.Membership

/-- **The height function.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §1.3, Eq. (4) and below it, p. 5 (PDF p. 6): for
`⟨w, p⟩ ≠ 0`, `h_p(z)` is the unique scalar with `⟨w, z⟩ + h_p(z) ⟨w, p⟩ = θ`, so
`h_p(z) = (θ − ⟨w, z⟩) / ⟨w, p⟩`.

**Formalization Note.** Division by `⟨w, p⟩`: every statement using `height` has the hypothesis
`1/10 ≤ |⟨w, p⟩|`, so the junk value at `⟨w, p⟩ = 0` is never read. -/
noncomputable def height {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (p z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (θ - inner ℝ w z) / inner ℝ w p

end QuantumLTF.Membership


