-- Prove2me | Definitions.Def_RadioInitBits_IsType1Phase
-- name    : RadioInitBits_IsType1Phase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:13.999832+00:00
-- url     : https://prove2.me/theorems/615c12ea-710e-4ea2-9cb8-8d69982f1921
-- title:
--   Phase parameters $f_i$, $q_i$ and type 1 phases (Definition 31)
-- statement:
--   Algorithm 8 runs in phases $i=1,2,\dots$. Phase $i$ has $T=q_in$ bins, with
--   $$q_i=\frac{16}{2^i},$$
--   and aims to leave a fraction
--   $$f_i=\frac{f_0}{4^i},\qquad f_0=0.633,$$
--   of the $n$ nodes uninitialized at its end.
--
--   Phase $i$ is a **type 1 phase** if
--   $$\frac{\left(\tfrac78 f_{i-1}\right)^2 n}{q_i}\ \ge\ \log_2 n .$$
--   Then the expected number of colliding nodes is at least logarithmic, so the true number is concentrated. The other phases are **type 2**.
--
--   The definition also provides the type 1 inequality $\left(\tfrac78 f\right)^2 n/q\ge\log_2 n$ for a general fraction $f$ and relative length $q$. Lemma 33 is stated with it.
--
--   **Formalization Note** The logarithm is base $2$. The proof of Lemma 33 turns $2^{-c((7/8)f)^2n/q}$ into $n^{-c}$ with this inequality, and that step needs base 2. The definition is used for $i\ge1$.
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version Definition 31, p.29 (PDF p.50); f₀ = 0.633 on p.26 (PDF p.47); fᵢ and qᵢ in Algorithm 10, line 2, p.42 (PDF p.63) and the proof of Lemma 30, p.28 (PDF p.49)

import Mathlib

set_option autoImplicit false

namespace RadioInitBits

/-- The target fraction `f_i = f₀ / 4^i` of uninitialized nodes at the end of phase `i`, with
`f₀ = 0.633`.
D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version Algorithm 10, line 2, p.42 (PDF p.63),
and proof of Lemma 30, p.28 (PDF p.49): "fin = fi−1 = f0/4^{i−1}, fout = fi = f0/4^i"; p.26
(PDF p.47): "f0 = 0.633 < 1 − 1/e". -/
noncomputable def fPhase (i : ℕ) : ℝ := (633 / 1000 : ℝ) / 4 ^ i

/-- The relative length `q_i = 16 / 2^i` of phase `i`: phase `i` has `T = q_i n` bins
(Algorithm 10, line 2, p.42, PDF p.63: "T ← 16n/2^i"; proof of Lemma 30, p.28: "q = qi = 16/2^i"). -/
noncomputable def qPhase (i : ℕ) : ℝ := 16 / 2 ^ i

/-- The **type 1 condition** of Definition 31 for a phase in which a fraction `f` of the `n`
nodes is targeted to participate and the phase has relative length `q`:
`((7/8) f)² n / q ≥ log n`.

**Formalization Note** `log` is `log₂` (`Real.logb 2`): the proof of Lemma 33 (p.29, PDF p.50)
turns `2^{−6 ((7/8) f)² n / q}` into `n^{−6}` using this inequality, which needs base 2. -/
noncomputable def IsType1 (n : ℕ) (f q : ℝ) : Prop :=
  Real.logb 2 n ≤ ((7 / 8) * f) ^ 2 * n / q

/-- **Definition 31.** Phase `i` is a **type 1 phase** if `((7/8) f_{i−1})² n / q_i ≥ log n`;
the remaining phases are type 2.
Banasik, Dani, Hayes, full version Definition 31, p.29 (PDF p.50): "A type 1 phase is one where
((7/8)fi−1)²n/qi ≥ log n, so that the true number of colliding nodes will not be much greater than
its expectation. The remaining phases are called type 2 phases and contain fewer than log n
colliding nodes in expectation."

**Formalization Note** Phases are numbered from `1` as in Algorithm 8; the definition is used
only for `i ≥ 1` (at `i = 0`, `i − 1` is truncated to `0`). `log` is `log₂` (see `IsType1`). -/
def IsType1Phase (n i : ℕ) : Prop :=
  IsType1 n (fPhase (i - 1)) (qPhase i)

end RadioInitBits


