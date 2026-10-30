-- Prove2me | Definitions.Def_FuchsVdGraaf_kolmogorov
-- name    : FuchsVdGraaf_kolmogorov
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:16.920241+00:00
-- url     : https://prove2.me/theorems/88bc2edb-f5b2-4f60-b063-171b757fe9dc
-- title:
--   Kolmogorov distance $K(p_0,p_1)$ (Definition 5)
-- statement:
--   For two probability distributions $p_0, p_1$ on a finite set $\mathcal X$, the **Kolmogorov distance** is
--
--   $$
--   K(p_0,p_1) = \frac12 \sum_{x\in\mathcal X} |p_0(x) - p_1(x)| .
--   $$
--
--   The factor $\tfrac12$ makes $K$ take values in $[0,1]$: identical distributions have $K = 0$, orthogonal ones $K = 1$. It is the total variation distance, the measure on which the cryptographic notions of exponential and computational indistinguishability are based.
--
--   **Formalization Note** Defined for any real functions on a finite type.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Definition 5, eq. (18), p.11

import Mathlib

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Definition 5, eq. (18), p.11: the
Kolmogorov distance between two probability distributions,
`K(p₀, p₁) = ½ ∑_{x∈X} |p₀(x) − p₁(x)|`.

**Formalization Note.** The factor `½` is the paper's (p.12: "we wanted K to take values between
0 and 1"). Defined for any real functions on a finite type. -/
noncomputable def kolmogorov {X : Type} [Fintype X] (p0 p1 : X → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |p0 x - p1 x|

end FuchsVdGraaf


