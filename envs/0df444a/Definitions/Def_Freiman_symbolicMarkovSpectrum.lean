-- Prove2me | Definitions.Def_Freiman_symbolicMarkovSpectrum
-- name    : Freiman_symbolicMarkovSpectrum
-- status  : Definition
-- author  : @tp
-- created : 2026-09-08T23:21:27.086807+00:00
-- url     : https://prove2.me/theorems/4db71b35-2f36-4974-a75e-ded175cee6e5
-- title:
--   The symbolic Lagrange and Markov spectra
-- statement:
--   Let $a=(a_i)_{i\in\mathbb Z}$ be a sequence of positive integers. Its local value at position $i$ is
--   $$
--   \lambda_i(a)=a_i+[0;a_{i-1},a_{i-2},\ldots]
--                     +[0;a_{i+1},a_{i+2},\ldots].
--   $$
--   The digits in each fractional tail are read away from position $i$.
--
--   The symbolic Lagrange spectrum consists of the finite real values
--   $$
--   L_{\mathrm{sym}}=
--   \left\{t\in\mathbb R:\exists a,\ \limsup_{n\to+\infty}\lambda_n(a)=t\right\}.
--   $$
--   The symbolic Markov spectrum consists of the finite real values
--   $$
--   M_{\mathrm{sym}}=
--   \left\{t\in\mathbb R:\exists a,\ \sup_{i\in\mathbb Z}\lambda_i(a)=t\right\}.
--   $$
--   The latter equality means that every local value is at most $t$ and, for every $\varepsilon>0$, some local value is greater than $t-\varepsilon$. Attainment of the supremum is not required. These sets will be identified with the classical spectra by separate theorems.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, equation (1.3), p. 7, and the definitions of the symbolic spectra immediately before Theorem 1.3, p. 8.

import Definitions.Def_Freiman_cfValue
import Definitions.Def_Freiman_lagrangeSpectrum

namespace Freiman

noncomputable def localValue (a : ℤ → ℕ+) (i : ℤ) : ℝ :=
  ((a i : ℕ) : ℝ) +
    cfValue (fun n : ℕ => a (i - (n : ℤ) - 1)) +
    cfValue (fun n : ℕ => a (i + (n : ℤ) + 1))

def symbolicLagrangeSpectrum : Set ℝ :=
  {t | ∃ a : ℤ → ℕ+,
    HasFiniteLimsup (fun n : ℕ => localValue a (n : ℤ)) t}

def symbolicMarkovSpectrum : Set ℝ :=
  {t | ∃ a : ℤ → ℕ+,
    (∀ i : ℤ, localValue a i ≤ t) ∧
    ∀ ε : ℝ, 0 < ε → ∃ i : ℤ, t - ε < localValue a i}

end Freiman


