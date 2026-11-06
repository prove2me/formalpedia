-- Prove2me | Definitions.Def_ConeL2G_beta
-- name    : ConeL2G_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:52.91296+00:00
-- url     : https://prove2.me/theorems/d886b7f0-13a0-46e4-ab6f-7f5835273baf
-- title:
--   The constant $\beta_d=1-((s-1)/s)^d$
-- statement:
--   For a real number $s$ and a natural number $d$,
--   $$\beta_d=1-\Big(\frac{s-1}{s}\Big)^d .$$
--   For $s\ge1$, $1-\beta_d$ is a lower bound on the probability that a uniformly random proper coloring of $d$ vertices with enough available colors avoids a given color.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Theorem 1.6, p.4

import Mathlib

namespace ConeL2G

/-- **The constant** `β_d = 1 − ((s − 1)/s)^d`. Li–Oveis Gharan, arXiv:2610.37721, Theorem 1.6,
p.4: "where `D_{H′} = Σ_{i∈H′} Dᵢ` and `β_d = 1 − ((s−1)/s)^d`".

**Formalization Note.** `s` is a real number (the paper takes `s ⩾ 5`; Theorem 1.7 uses the real
value `s = (α − 1)∆`), `d` a natural number. -/
noncomputable def beta (s : ℝ) (d : ℕ) : ℝ :=
  1 - ((s - 1) / s) ^ d

end ConeL2G


