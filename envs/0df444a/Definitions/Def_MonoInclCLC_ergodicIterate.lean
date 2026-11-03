-- Prove2me | Definitions.Def_MonoInclCLC_ergodicIterate
-- name    : MonoInclCLC_ergodicIterate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:22.733194+00:00
-- url     : https://prove2.me/theorems/a556b6b0-c601-497b-b43b-8384efb0e3a2
-- title:
--   Theorem 3.7, p.16 — the ergodic iterate $\tilde z(t)$
-- statement:
--   Along a trajectory $(x,\lambda)$, the **ergodic iterate** is the $\lambda$-weighted average of the resolvent points $z(s)=(I+\lambda(s)A)^{-1}x(s)$:
--   $$
--   \tilde z(t)=\frac{1}{\int_0^t\lambda(s)\,ds}\Big(\int_0^t\lambda(s)\,(I+\lambda(s)A)^{-1}x(s)\,ds\Big).
--   $$
--   The gap function is measured at this average, and the averaging gains a factor $t^{-1/2}$ over the pointwise residue rate.
--
--   **Formalization Note** Both integrals are Bochner interval integrals. Along a solution the integrands are continuous, so no integrability hypothesis is needed. The theorems use $t>0$.
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Theorem 3.7, p.16 (Ergodic Iterate)

import Mathlib

namespace MonoInclCLC

/-- **The ergodic iterate** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Theorem 3.7, p.16):
`z̃(t) = (1 / ∫₀ᵗ λ(s) ds) (∫₀ᵗ λ(s) (I + λ(s)A)⁻¹x(s) ds)`.

**Formalization Note.** `J (lam s) (x s)` is `(I + λ(s)A)⁻¹x(s)`, the pointwise iterate `z(s)`. Both
integrals are Bochner interval integrals. No integrability is assumed, because along a solution of
`IsClosedLoopSolution` on `Set.Ici 0` the integrands are continuous: `lam` is continuous by
Lemma 2.5 (and constant for `p = 1`), and `J (lam s) (x s) = x s + ẋ(s)` with `J` nonexpansive in
`x` and continuous in the step size. So the junk value `0` of a non-integrable integrand never
occurs. The theorems use `t > 0`, where `∫₀ᵗ lam > 0`. -/
noncomputable def ergodicIterate {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : ℝ → H → H) (x : ℝ → H) (lam : ℝ → ℝ) (t : ℝ) : H :=
  (∫ s in (0 : ℝ)..t, lam s)⁻¹ • ∫ s in (0 : ℝ)..t, lam s • J (lam s) (x s)

end MonoInclCLC


