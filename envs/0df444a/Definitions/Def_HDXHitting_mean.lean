-- Prove2me | Definitions.Def_HDXHitting_mean
-- name    : HDXHitting_mean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:26.335224+00:00
-- url     : https://prove2.me/theorems/5113802c-7d90-4781-9e37-cdfe655379b1
-- title:
--   Mean $\mathbb E_\pi f$ under the vertex distribution
-- statement:
--   For a $d$-dimensional complex with top distribution $p$ and a function $f$ on the vertices, the **mean** of $f$ is
--   $$
--   \mu = \mathbb E_{\pi} f = \sum_{v} \pi_1(v)\, f(v),
--   $$
--   with $\pi_1$ the vertex distribution. This is the quantity $\mu$ in the bound $\mu(\mu+d\lambda)^{d-1}$ of Lemma 3.2.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Lemma 3.2, p.15 (mean E_π f := µ)

import Mathlib
import Definitions.Def_HDXHitting_vertexMeasure

namespace HDXHitting

/-- The mean `E_π f = ∑_v π_1(v) f(v)` of a function `f` on the vertices under the vertex
distribution `π_1` of the complex (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), Lemma 3.2, p.15, "with mean `E_π f := µ`"). -/
noncomputable def mean {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ)
    (f : V → ℝ) : ℝ :=
  ∑ v, vertexMeasure d p v * f v

end HDXHitting


