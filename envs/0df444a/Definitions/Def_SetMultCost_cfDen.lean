-- Prove2me | Definitions.Def_SetMultCost_cfDen
-- name    : SetMultCost_cfDen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:59.902221+00:00
-- url     : https://prove2.me/theorems/09669d37-8946-45b9-8594-0d63834f9a3f
-- title:
--   Convergents of a continued fraction
-- statement:
--   For a digit sequence $a_0,a_1,\dots$, the convergents $p_i/q_i$ are given by $p_0=a_0$, $q_0=1$, $p_1=a_0a_1+1$, $q_1=a_1$, and for $i\ge1$,
--
--   $$p_{i+1}=a_{i+1}p_i+p_{i-1},\qquad q_{i+1}=a_{i+1}q_i+q_{i-1}.$$
--
--   The number $\alpha$ **has the continued fraction $[a_0,a_1,\dots]$** when $a_i\ge1$ for $i\ge1$ and $p_i/q_i\to\alpha$.
--
--   **Formalization Note** The value is a predicate rather than a limit operator, since a limit operator has a junk value on a non-convergent sequence. The expansion is infinite, so $\alpha$ is irrational.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Definition 5.1, p.16

import Mathlib

namespace SetMultCost

/-- The convergent numerators of a digit sequence. Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), Definition 5.1, p.16: "p0 = a0, … p1 =
a0a1 + 1, … For all i ≥ 1, pi+1 = ai+1pi + pi−1". -/
def cfNum (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => a 0
  | 1 => a 0 * a 1 + 1
  | i + 2 => a (i + 2) * cfNum a (i + 1) + cfNum a i

/-- The convergent denominators of a digit sequence. Definition 5.1, p.16: "q0 = 1, … q1 = a1, …
qi+1 = ai+1qi + qi−1". -/
def cfDen (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => a 1
  | i + 2 => a (i + 2) * cfDen a (i + 1) + cfDen a i

/-- **`α` has the infinite continued fraction `[a₀, a₁, …]`** (Definition 5.1, p.16): `aᵢ ≥ 1` for
`i ≥ 1`, and the convergents `pᵢ/qᵢ` tend to `α`.

**Formalization Note.** A predicate rather than a `limUnder`, which has a junk value on a sequence
with no limit. The expansion is infinite, so `α` is irrational. -/
def IsCFValue (a : ℕ → ℤ) (α : ℝ) : Prop :=
  (∀ i, 1 ≤ i → 1 ≤ a i) ∧
    Filter.Tendsto (fun k => (cfNum a k : ℝ) / (cfDen a k : ℝ)) Filter.atTop (nhds α)

end SetMultCost


