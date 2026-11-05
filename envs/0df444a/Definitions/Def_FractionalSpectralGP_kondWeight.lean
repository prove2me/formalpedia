-- Prove2me | Definitions.Def_FractionalSpectralGP_kondWeight
-- name    : FractionalSpectralGP_kondWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:20.456114+00:00
-- url     : https://prove2.me/theorems/a662a731-8e40-4d53-9d6b-c056f9a08bc4
-- title:
--   The weight $(2\mathbb N)^\beta=2^{\beta_1}(2\cdot2)^{\beta_2}(2\cdot3)^{\beta_3}\cdots$
-- statement:
--   For $\beta\in\ell$,
--
--   $$
--   (2\mathbb N)^\beta=2^{\beta_1}\,(2\times2)^{\beta_2}\,(2\times3)^{\beta_3}\cdots ,
--   $$
--
--   the weight of the Kondratiev norms (4.5)–(4.6) and of the constant $A$ in Våge's inequality (4.8).
--
--   **Formalization Note** Coordinate $n=0,1,\dots$ of $\beta$ is the paper's coordinate $k=n+1$ and carries the factor $2(n+1)$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, p.11

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The weight `(2ℕ)^β = 2^{β₁} (2·2)^{β₂} (2·3)^{β₃} ⋯` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §4, p.11, after (4.6)).

**Formalization Note.** Coordinate `n = 0, 1, …` of `β : ℕ →₀ ℕ` is the paper's coordinate
`k = n + 1`, so it carries the factor `2(n + 1)` (never `2n`, which would vanish at `n = 0`). -/
noncomputable def kondWeight (β : ℕ →₀ ℕ) : ℝ :=
  β.prod fun n k => (2 * ((n : ℝ) + 1)) ^ k

end FractionalSpectralGP


