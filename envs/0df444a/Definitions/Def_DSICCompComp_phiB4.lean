-- Prove2me | Definitions.Def_DSICCompComp_phiB4
-- name    : DSICCompComp_phiB4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:04.588843+00:00
-- url     : https://prove2.me/theorems/68201c23-5f72-4111-848f-3c28fc7b3fd1
-- title:
--   Explicit tail bound $\Phi(x)$ from the proof of Lemma B.4
-- statement:
--   For the parameters $n, \ell, r, a, b, \varepsilon, t, T$ and $x > T$, let
--   $$
--   \Phi(x) = 2b(n-r)\Bigl(\frac{1}{t+1} + \frac{t\,(1+b(\ell-1))}{a-t}\Bigr) + \frac{16b^2(n-r-1)(\ell-1)}{T+x+4} + \frac{4rb\varepsilon}{x-T+2\varepsilon}.
--   $$
--   The proof of Lemma B.4 shows $\mathbb P[p_{i,\{j,k\}}(v_{-i}) - 2a \ge x] \le \Phi(x)$ and then writes $\Phi(x)$ as $O\bigl(nb(1/t + t(1+\ell b)/(a-t)) + (n\ell b^2 + rb\varepsilon)/(x-T)\bigr)$. Lemmas B.5, B.6 and the bound of §B.4 use this quantity in the form $1 - O(\cdot)$; this mission uses $1 - \Phi(\cdot)$.
--
--   **Formalization Note** The differences $n-r$, $n-r-1$, $\ell-1$ are real numbers; under the hypotheses of every statement that uses $\Phi$ they equal the paper's nonnegative counts.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), proof of Lemma B.4, p.30 (pdf p.31)

import Mathlib

namespace DSICCompComp

/-- The explicit tail bound `Φ(x)` printed at the end of the proof of Lemma B.4
(Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, proof of Lemma B.4, p.30
(pdf p.31)):
`Φ(x) = 2b(n − r)(1/(t + 1) + t(1 + b(ℓ − 1))/(a − t)) + 16b²(n − r − 1)(ℓ − 1)/(T + x + 4) + 4rbε/(x − T + 2ε)`.
The paper bounds `P[p_{i,{j,k}}(v_{−i}) − 2a ≥ x]` by `Φ(x)` and then writes it as
`O(nb(1/t + t(1 + ℓb)/(a − t)) + (nℓb² + rbε)/(x − T))`; Lemmas B.5, B.6 and §B.4 use it as
`1 − O(·)`.

**Formalization Note** All differences `n − r`, `n − r − 1`, `ℓ − 1` are taken in `ℝ` (no
truncated `ℕ` subtraction); in every statement that uses `Φ`, the hypotheses make them equal to
the paper's nonnegative counts. -/
noncomputable def phiB4 (n ℓ r : ℕ) (a b ε t T x : ℝ) : ℝ :=
  2 * b * ((n : ℝ) - r) * (1 / (t + 1) + t * (1 + b * ((ℓ : ℝ) - 1)) / (a - t)) +
    16 * b ^ 2 * ((n : ℝ) - r - 1) * ((ℓ : ℝ) - 1) / (T + x + 4) +
    4 * r * b * ε / (x - T + 2 * ε)

end DSICCompComp


