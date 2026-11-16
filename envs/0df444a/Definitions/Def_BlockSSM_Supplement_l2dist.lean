-- Prove2me | Definitions.Def_BlockSSM_Supplement_l2dist
-- name    : BlockSSM_Supplement_l2dist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:01:03.409332+00:00
-- url     : https://prove2.me/theorems/4f425586-1ea0-4172-b370-c6914d9025e1
-- title:
--   Euclidean distance on the hidden state space $\mathbb C^n$
-- statement:
--   For a block partition $n=n_1+\dots+n_m$, the hidden state space is $\mathbb C^n=\mathbb C^{n_1}\times\dots\times\mathbb C^{n_m}$. Its **Euclidean norm** and **Euclidean distance** are
--   $$
--   \|h\|_2=\Bigl(\sum_{i=1}^m\sum_{k=1}^{n_i}|h_{i,k}|^2\Bigr)^{1/2},\qquad \|x-y\|_2 .
--   $$
--
--   These are the norms in which the prototype separation $\Delta_G$ of Theorem 10 and the margin of Definition 11 are measured.
--
--   **Formalization Note** Mathlib's default norm on a product type is the sup norm, which changes balls and nearest points; the Euclidean norm is therefore written out coordinatewise.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §5, p.5 (PDF p.6), Theorem 10 and Definition 11

import Mathlib
import Definitions.Def_BlockSSM_Tracker

namespace BlockSSM.Supplement

open BlockSSM

/-- The Euclidean (Hermitian `ℓ²`) norm `‖h‖ = (∑ᵢ ∑ₖ |hᵢₖ|²)^{1/2}` on the hidden state space
`ℂⁿ = ℂ^{n₁} × ⋯ × ℂ^{n_m}`. -/
noncomputable def l2norm {m : ℕ} {n : Fin m → ℕ} (h : State n) : ℝ :=
  Real.sqrt (∑ i, ∑ k, ‖h i k‖ ^ 2)

/-- **Euclidean distance on the hidden state space.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §5, p.5 (PDF p.6): the norm
`‖ρ(h)v − ρ(h′)v‖` of Theorem 10 and `‖F_s(h₀) − F_t(h₀)‖` of Definition 11 is the Euclidean norm
of `ℂⁿ`.

**Formalization Note.** Mathlib's default norm on the Pi type `State n` is the sup norm, which
changes balls and nearest points; this definition is the `ℓ²` distance written out coordinatewise,
`‖x − y‖₂ = (∑ᵢ ∑ₖ |xᵢₖ − yᵢₖ|²)^{1/2}`. -/
noncomputable def l2dist {m : ℕ} {n : Fin m → ℕ} (x y : State n) : ℝ :=
  l2norm (x - y)

end BlockSSM.Supplement


