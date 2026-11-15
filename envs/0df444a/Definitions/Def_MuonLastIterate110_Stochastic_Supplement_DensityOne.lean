-- Prove2me | Definitions.Def_MuonLastIterate110_Stochastic_Supplement_DensityOne
-- name    : MuonLastIterate110_Stochastic_Supplement_DensityOne
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:37:31.257428+00:00
-- url     : https://prove2.me/theorems/ccf11445-03e1-4c36-8afc-9f90831b0342
-- title:
--   Definition 6.2 — density-one rate
-- statement:
--   For real sequences $h_t,\rho_t$ indexed by positive integers, define $h=o_{\mathrm{dens}}(\rho)$ by
--
--   $$
--   \forall c>0,\quad\lim_{T\to\infty}\frac{\#\{1\le t\le T:h_t>c\rho_t\}}{T}=0.
--   $$
--
--   This is the paper's density-one rate: every positive multiple of the reference rate is exceeded on a set of natural density zero. Nonnegativity of $h_t$ and positivity of $\rho_t$ describe the sequences to which the results apply, rather than additional conjuncts inside the predicate. For random trajectories the predicate is applied almost surely, path by path.
--
--   **Formalization Note** The finite set is exactly the interval $[1,T]$ of natural numbers, the comparison is strict, and the cardinality and denominator are coerced to real numbers. The value at $T=0$ is immaterial to the limit at infinity.
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.13, Definition 6.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib

open Filter Topology

namespace MuonLastIterate110.Stochastic.Supplement

/-- Definition 6.2 (p.13): every positive multiple of the reference rate is exceeded on
only a set of natural density zero. The initial segment is exactly 1 ≤ t ≤ T.
Nonnegativity of h and positivity of ρ are supplied where the notion is applied. -/
noncomputable def DensityOne (h ρ : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c →
    Tendsto (fun T : ℕ =>
      ((Finset.Icc 1 T).filter (fun t => h t > c * ρ t)).card / (T : ℝ))
      atTop (𝓝 0)


end MuonLastIterate110.Stochastic.Supplement


