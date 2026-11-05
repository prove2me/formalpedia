-- Prove2me | Definitions.Def_FractionalSpectralGP_multiFactorial
-- name    : FractionalSpectralGP_multiFactorial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:07.122728+00:00
-- url     : https://prove2.me/theorems/70e80b23-b708-4381-baee-ca1dc9337932
-- title:
--   Multi-index factorial $\alpha!=\alpha_1!\alpha_2!\cdots$
-- statement:
--   For a finitely supported multi-index $\alpha\in\ell$,
--
--   $$
--   \alpha!=\alpha_1!\,\alpha_2!\cdots ,
--   $$
--
--   a finite product since $\alpha_k!=1$ whenever $\alpha_k=0$. It is the squared norm of $H_\alpha$ in (4.3) and the weight in the Kondratiev norm (4.5) and in the duality between $S_{-1}$ and $S_1$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, p.10

import Mathlib

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The multi-index factorial `α! = α₁! α₂! ⋯` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §4, p.10, after (4.3)). -/
def multiFactorial (α : ℕ →₀ ℕ) : ℕ :=
  α.prod fun _ k => k.factorial

end FractionalSpectralGP


