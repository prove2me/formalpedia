-- Prove2me | Definitions.Def_NoSignalPA_uniformExp
-- name    : NoSignalPA_uniformExp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:46.40355+00:00
-- url     : https://prove2.me/theorems/fd22fb2c-e348-465c-bafe-57a6b16d410b
-- title:
--   Expectation under the uniform distribution on a finite set
-- statement:
--   For a finite nonempty set $\Omega$ and $f:\Omega\to\mathbb R$, $\langle f\rangle=\frac{1}{|\Omega|}\sum_{\omega\in\Omega}f(\omega)$, the expectation of $f$ at a uniformly random $\omega$. It is the average $\langle e^{\beta\sum_{\mathbf a}\mu_{\mathbf a}V_{\mathbf a}}\rangle$ over random hash functions in Bernstein's construction.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Appendix, eq. (14), p.5

import Mathlib

namespace NoSignalPA

/-- **The expectation of a real function under the uniform distribution on a finite type.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Appendix, p. 5 (PDF p. 5): `⟨e^{β Σ_a μ_a V_a}⟩` is the average over a uniformly random hash
function `h`.

`uniformExp f = (Σ_ω f ω) / |α|`. -/
noncomputable def uniformExp {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card α

end NoSignalPA


