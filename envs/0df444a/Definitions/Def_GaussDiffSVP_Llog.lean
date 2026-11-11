-- Prove2me | Definitions.Def_GaussDiffSVP_Llog
-- name    : GaussDiffSVP_Llog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:40.513234+00:00
-- url     : https://prove2.me/theorems/ee8b3cfc-91b3-41d3-a8a3-0c52ecb9fc49
-- title:
--   $L_{\log} = \lceil \log_2(n+2)\rceil$
-- statement:
--   For $n \in \mathbb N$, $L_{\log}(n) = \lceil \log_2(n+2)\rceil$, the least integer $k\ge0$ with $2^k \ge n+2$ (the paper's $\mathrm{clog}_2$ of App. C.1.6). It is at least $1$ and is the logarithmic scale from which all sublinear budgets of the paper are built.
--
--   **Formalization Note** `Nat.clog 2 (n + 2)`; checked at $n = 0,1,2,6$ (values $1,2,2,3$).
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (163), App. C.1.2, p.80; §3.3, p.19; App. C.1.6, p.81

import Mathlib

namespace GaussDiffSVP

/-- The integer `L_log = ⌈log₂(n + 2)⌉` (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (163), p.80; §3.3, p.19).

**Formalization Note.** `Nat.clog 2 (n + 2)` is the least `k` with `n + 2 ≤ 2^k`, which is the
paper's `clog₂ x = min{k ∈ ℤ≥0 : 2^k ≥ x}` (App. C.1.6, p.81) at `x = n + 2`, i.e. the integer
ceiling of `log₂(n + 2)`. It is at least `1` for every `n`. -/
def Llog (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

end GaussDiffSVP


