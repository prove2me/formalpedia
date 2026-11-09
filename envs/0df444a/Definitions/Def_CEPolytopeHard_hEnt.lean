-- Prove2me | Definitions.Def_CEPolytopeHard_hEnt
-- name    : CEPolytopeHard_hEnt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:39.253662+00:00
-- url     : https://prove2.me/theorems/1cc4bb89-4635-487c-b13a-4af60fc6eea7
-- title:
--   Average entropy $h(t) = \mathbb E_{i\sim\mu} H(P_i(t))$
-- statement:
--   For a stochastic matrix $P$ with stationary distribution $\mu$ and $0 < t \le 1$,
--   $$
--   h(t) := \mathbb E_{i \sim \mu} H(P_i(t)) = \sum_i \mu_i \sum_j -P_{ij}(t) \log P_{ij}(t),
--   $$
--   the average entropy (natural logarithm, $0 \log 0 = 0$) of the rows of $P(t)$. Lemma 3.7 shows that $h$ is nonincreasing; this monotonicity drives the choice of a good layer in Section 3.2.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 3.2, p.15

import Mathlib
import Definitions.Def_CEPolytopeHard_geo

set_option autoImplicit false

namespace CEPolytopeHard

/-- The **average entropy `h(t)`** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The
Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of
November 2, 2026, sha256 6aec500a…7820, Section 3.2, p.15: "h(t) := E_{i∼µ} H(P_i(t)) where H is
entropy with natural logarithms"): `h(t) = ∑_i μ_i ∑_j −P_{ij}(t) log P_{ij}(t)`.

**Formalization Note** `Real.negMulLog x = −x log x` (natural logarithm, `0 log 0 = 0`). -/
noncomputable def hEnt {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ) (t : ℝ) : ℝ :=
  ∑ i, μ i * ∑ j, Real.negMulLog (geo P t i j)

end CEPolytopeHard


