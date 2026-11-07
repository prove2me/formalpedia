-- Prove2me | Definitions.Def_QPSpinParisi_coef
-- name    : QPSpinParisi_coef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:56.881403+00:00
-- url     : https://prove2.me/theorems/7b98e793-2452-47fb-82b4-b0c06fbac574
-- title:
--   The weight $c_pN_{n,p}^{-1/2}$ of a Pauli string
-- statement:
--   The deterministic weight of the string with index $(\bar i,\bar a)$ in $H_n$ is $c_pN_{n,p}^{-1/2}$, where $p$ is the length of $\bar i$ and $N_{n,p}=\binom np$. Since $p\le n$, the binomial coefficient is positive. The weight is shared by $H_n$ and the classical field $X_n$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_QPSpinParisi_Idx

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The deterministic weight `c_p N_{n,p}^{-1/2}` of a string in (2.1) (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3, PDF p.3), where
`N_{n,p} = binom(n, p)` and `p` is the size of the tuple. Here `p ≤ n`, so the binomial coefficient is positive. -/
noncomputable def coef (c : ℕ → ℝ) {n : ℕ} (i : Idx n) : ℝ :=
  c i.1.1.card * (Nat.choose n i.1.1.card : ℝ) ^ (-(1 / 2) : ℝ)

end QPSpinParisi


