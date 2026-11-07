-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Negligible
-- name    : QAdvFew_PoQOracle_Negligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:56.376644+00:00
-- url     : https://prove2.me/theorems/51a769a8-1966-4c06-88e3-b00b43bd90b1
-- title:
--   Negligible function
-- statement:
--   A nonnegative function $\nu(n)$ is **negligible** if for every constant $c>0$, $\nu(n)\le n^{-c}$ for all sufficiently large $n$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.1, p. 11 (PDF p. 13)

import Mathlib

namespace QAdvFew.PoQOracle

/-- A negligible function (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, §3.1, p. 11 (PDF p. 13): "A nonnegative function `ν(n)` is
negligible if for every constant `c > 0`, `ν(n) ≤ n^{−c}` for all sufficiently large `n`"). -/
def Negligible (ν : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ ν n) ∧ ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in Filter.atTop, ν n ≤ (n : ℝ) ^ (-c)

end QAdvFew.PoQOracle


