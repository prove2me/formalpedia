-- Prove2me | Definitions.Def_HDXHitting_cPoly
-- name    : HDXHitting_cPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:31.559006+00:00
-- url     : https://prove2.me/theorems/b975fede-5ba7-499c-a777-bdde88e6c875
-- title:
--   The polynomial $c_d(\vec\mu)=\frac1d\sum_i\mu_i\prod_{j\ne i}(\mu_j+d\lambda)$
-- statement:
--   For a finite set $S$ of $d=|S|$ colours, $\lambda\in\mathbb R$ and a vector $\vec\mu$,
--   $$
--   c_d(\vec\mu) = \frac1d\sum_{i\in S}\mu_i\prod_{j\in S,\ j\ne i}(\mu_j+d\lambda).
--   $$
--   This is the right side of the partite bound (3) of Lemma 3.2, called $c_d$ in its proof. Only the coordinates in $S$ enter.
--
--   **Formalization Note** At $S=\emptyset$ the factor $1/0$ is $0$ in Lean; the results use $|S|\ge1$.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Lemma 3.2, Eq. (3), p.15; proof of the partite bound, p.16

import Mathlib

namespace HDXHitting

/-- The polynomial on the right side of Eq. (3) (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), Lemma 3.2, p.15; "`c_d(µ)`", proof
of the partite bound, p.16): for a set `S` of `d = |S|` colours and a vector `µ`,
`c_d(µ) = (1/d) ∑_{i∈S} µ_i ∏_{j∈S, j≠i} (µ_j + dλ)`.

**Formalization Note** Only the coordinates in `S` are read. At `S = ∅` the factor `1/0` is `0`
in Lean. -/
noncomputable def cPoly {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ℝ) (μ : ι → ℝ) : ℝ :=
  (1 / (S.card : ℝ)) * ∑ i ∈ S, μ i * ∏ j ∈ S.erase i, (μ j + S.card * lam)

end HDXHitting


