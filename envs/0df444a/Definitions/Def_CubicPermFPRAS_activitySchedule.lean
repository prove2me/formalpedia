-- Prove2me | Definitions.Def_CubicPermFPRAS_activitySchedule
-- name    : CubicPermFPRAS_activitySchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:19.619256+00:00
-- url     : https://prove2.me/theorems/859147de-960d-446d-bf3b-91a1491798e9
-- title:
--   The activity schedule $1/n=a_0<\dots<a_m=J$ of Lemma 10 and its construction cost
-- statement:
--   For a constant $K$, let $q(a)$ be the least power of two with $q(a)^2\ge16K(1+\min\{n,n/\sqrt a\})$. The **activity schedule** is
--   $$a_0=\frac1n,\qquad a_{k+1}=\min\Big\{J,\Big(1+\frac1{q(a_k)}\Big)a_k\Big\},$$
--   until $a_m=J$. The construction finds $q(a_0)$ by doubling and maintains $q$ by halving while the defining inequality still holds; its number of inequality tests is $2k_0-k_{m-1}+m$ when $q(a_0)=2^{k_0}$ and $q(a_{m-1})=2^{k_{m-1}}$.
--
--   **Formalization Note** $m$ is the infimum of the indices with $a_m=J$; Lemma 10 asserts that it is reached.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), proof of Lemma 10, steps 2 and 4, pp.44–45 (PDF 46–47)

import Mathlib

set_option autoImplicit false

namespace CubicPermFPRAS

noncomputable section

/-- The exponent of `q(a)`: the least `k ∈ ℕ` with `(2^k)² ≥ 16K(1 + min{n, n/√a})`
(proof of Lemma 10, step 2, p.44 (PDF 46); arXiv:2609.20717, held version sha256 9e14f335…). -/
def qExp (K : ℝ) (n : ℕ) (a : ℝ) : ℕ :=
  sInf {k : ℕ | 16 * K * (1 + min (n : ℝ) (n / Real.sqrt a)) ≤ ((2 : ℝ) ^ k) ^ 2}

/-- `q(a)`, the least power of two with `q(a)² ≥ 16K(1 + min{n, n/√a})` (p.44). -/
def qPow (K : ℝ) (n : ℕ) (a : ℝ) : ℝ := (2 : ℝ) ^ qExp K n a

/-- The assignment-activity schedule (proof of Lemma 10, step 2, p.44):
`a₀ = 1/n`, `a_{k+1} = min{J, (1 + 1/q(a_k)) a_k}`. Once `a_k = J` the sequence stays at `J`. -/
def actSeq (K J : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 1 / (n : ℝ)
  | k + 1 => min J ((1 + 1 / qPow K n (actSeq K J n k)) * actSeq K J n k)

/-- The index `m` of the last activity: the first `k` with `a_k = J` ("until `a_m = J`").
**Formalization Note.** `sInf` of the set of such indices; statements using it assert that
the schedule reaches `J`. -/
def actLen (K J : ℝ) (n : ℕ) : ℕ := sInf {k : ℕ | actSeq K J n k = J}

/-- The number of inequality tests made by the construction of step 4 of the proof of
Lemma 10 (p.44–45): `q(a₀)` is found by doubling from `1` (`k₀ + 1` tests, `q(a₀) = 2^{k₀}`), and
for each of the later activities `a₁, …, a_{m−1}` whose `q` is needed, `q` is halved while the
defining inequality still holds (`k_{j−1} − k_j` successful halvings and one failed test).
In total `2k₀ − k_{m−1} + m` tests when `m ≥ 1`. -/
def actTests (K J : ℝ) (n : ℕ) : ℕ :=
  let m := actLen K J n
  if m = 0 then 0
  else 2 * qExp K n (actSeq K J n 0) - qExp K n (actSeq K J n (m - 1)) + m

end

end CubicPermFPRAS


