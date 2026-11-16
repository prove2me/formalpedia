-- Prove2me | Definitions.Def_DecDynMatch_Supplement_SCPCParams
-- name    : DecDynMatch_Supplement_SCPCParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:25:18.411778+00:00
-- url     : https://prove2.me/theorems/74208aa4-ee46-4931-bde1-6ada959d3cd6
-- title:
--   SC-PC parameters (46): $\chi_L, \kappa_L, H_L, d_L, b_K, W_L, h_{D,L}, f_L, J_L, G_L, R_{c,L}, \tau_L, E_L, M_L$
-- statement:
--   The constants of SC-PC, functions of the number of arms $K$:
--   $$
--   \begin{aligned}
--   &\chi_L=4K-2,\quad \kappa_L=\chi_L-1,\quad H_L=d_L=\chi_L+1,\quad b_K=2K^2,\\
--   &W_L=K(K-1)^2+(2K-1)b_K=5K^3-4K^2+K,\quad h_{D,L}=2\chi_L+1,\quad f_L=W_L+3\chi_L,\quad J_L=W_L+4\chi_L,\\
--   &G_L=2K+3,\quad R_{c,L}=2K+1,\quad \tau_L=J_L+2\chi_L+3,\quad E_L=\tau_L+1,\quad M_L=E_L+K .
--   \end{aligned}
--   $$
--   $J_L$ is the length of a Work invocation, $H_L$ the minimum waiting (replay) length, $d_L$ the number of PARK rounds that open Work, $[h_{D,L},f_L)$ the deletion window, $G_L$ the period of fair Control rounds at an arm, $\tau_L$ the Business service length, $E_L$ the Seek guard and $M_L$ the minimum Commit duration.
--
--   **Formalization Note** Natural-number arithmetic; for $K\ge 1$ no subtraction truncates. $G_L$ is named `GLmod` (`GL` is reserved notation). The module defines one constant per symbol.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, eq. (46), p.30

import Mathlib

namespace DecDynMatch.Supplement

/-- **SC-PC parameters**, eq. (46). J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), App. C.1, eq. (46), p.30:
"χ_L = 4K − 2, κ_L = χ_L − 1, H_L = d_L = χ_L + 1, b_K = 2K², W_L = K(K − 1)² + (2K − 1)b_K
= 5K³ − 4K² + K, h_{D,L} = 2χ_L + 1, f_L = W_L + 3χ_L, J_L = W_L + 4χ_L, G_L = 2K + 3,
R_{c,L} = 2K + 1, τ_L = J_L + 2χ_L + 3, E_L = τ_L + 1, M_L = E_L + K."

`chiL K` is the timing margin `χ_L`.

**Formalization Note.** Natural-number arithmetic; for `K ≥ 1` no subtraction truncates
(`4K − 2 ≥ 2`, `χ_L − 1 ≥ 1`), and `W_L` is written as `K(K − 1)² + (2K − 1)b_K`, which equals
`5K³ − 4K² + K`. -/
def chiL (K : ℕ) : ℕ := 4 * K - 2

/-- `κ_L = χ_L − 1` (46). -/
def kappaL (K : ℕ) : ℕ := chiL K - 1
/-- `H_L = χ_L + 1`, the minimum waiting length (46). -/
def HL (K : ℕ) : ℕ := chiL K + 1
/-- `d_L = χ_L + 1`, the number of PARK rounds opening Work (46). -/
def dL (K : ℕ) : ℕ := chiL K + 1
/-- `b_K = 2K²` (46). -/
def bKL (K : ℕ) : ℕ := 2 * K ^ 2
/-- `W_L = K(K − 1)² + (2K − 1)b_K` (46). -/
def WL (K : ℕ) : ℕ := K * (K - 1) ^ 2 + (2 * K - 1) * bKL K
/-- `h_{D,L} = 2χ_L + 1`, the start of the deletion window (46). -/
def hDL (K : ℕ) : ℕ := 2 * chiL K + 1
/-- `f_L = W_L + 3χ_L`, the end of the deletion window and last certification round (46). -/
def fL (K : ℕ) : ℕ := WL K + 3 * chiL K
/-- `J_L = W_L + 4χ_L`, the number of rounds of a Work invocation (46). -/
def JL (K : ℕ) : ℕ := WL K + 4 * chiL K
/-- `G_L = 2K + 3` (`GLmod`), the period of fair Control rounds at an arm (46). -/
def GLmod (K : ℕ) : ℕ := 2 * K + 3
/-- `R_{c,L} = 2K + 1`, the run of accepted Commit proposals that triggers Work (46). -/
def RcL (K : ℕ) : ℕ := 2 * K + 1
/-- `τ_L = J_L + 2χ_L + 3`, the Business service length (46). -/
def tauL (K : ℕ) : ℕ := JL K + 2 * chiL K + 3
/-- `E_L = τ_L + 1`, the Seek guard length (46). -/
def EL (K : ℕ) : ℕ := tauL K + 1
/-- `M_L = E_L + K`, the minimum Commit duration (46). -/
def ML (K : ℕ) : ℕ := EL K + K

end DecDynMatch.Supplement


