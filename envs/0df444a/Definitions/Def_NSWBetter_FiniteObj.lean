-- Prove2me | Definitions.Def_NSWBetter_FiniteObj
-- name    : NSWBetter_FiniteObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:37.802191+00:00
-- url     : https://prove2.me/theorems/eaf215a7-45e4-4921-89c9-af4cfc1e20e3
-- title:
--   Configuration LP solution with a well-defined objective value
-- statement:
--   A configuration LP solution $y$ has a **well-defined (finite) objective value** when $y_{i,S}>0$ implies $v_i(S)>0$; then every term $y_{i,S}\ln v_i(S)$ is finite.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2.1, Remark 2.7, p.10; Section 4.2, p.19

import Mathlib

namespace NSWBetter

/-- **Finite objective.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Remark 2.7, p.10: "for any positive variable yi,S, we have vi(S) > 0 and ln vi(S) is well-defined"; Section 4.2, p.19: "a rational configuration LP solution with a well-defined objective value".

`FiniteObj v y`: every bundle with positive weight has positive value, so the objective `(1/n) Σ y_(i,S) ln v_i(S)` is finite. -/
def FiniteObj {n m : ℕ} (v : Fin n → Fin m → ℝ) (y : Fin n → Finset (Fin m) → ℝ) : Prop :=
  ∀ i S, 0 < y i S → 0 < ∑ g ∈ S, v i g

end NSWBetter


