-- Prove2me | Definitions.Def_RandModSubsetSum_Overhead
-- name    : RandModSubsetSum_Overhead
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:02:11.232206+00:00
-- url     : https://prove2.me/theorems/df1d4e7f-0c58-405a-9ccd-9b215660b6a0
-- title:
--   The overhead bounds $L_\beta$, $A_\beta$, $\Pi_\beta$ and the failure sum $F_\beta$ of Table 10
-- statement:
--   From Appendix C: $L_\beta(n)=\lceil10^6(\beta+1)(n+1)^2\rceil$ and $A_\beta(n)=2^{40}(L_\beta(n)+1)^6$ (56); $\Pi_\beta(n)=2^{100000}(n+1)^{1500000}A_\beta(n)$ (58); $w_{\min}=\min_rw_r$; and $F_\beta(n)$, the sum of the nine failure bounds of Table 10:
--   $$n2^{-n}+16e^{-n/(4\beta)}+2^{16}n2^{-10^{-6}n}+2^{-1.000026\cdot10^{-6}n+736548\log_2n+41042}+19968e^{-10^{-12}(w_{\min}n-2)}$$
--   $$+\,8255e^{-n^2}+\Pi_\beta(n)2^{-0.000406782870n}+\Pi_\beta(n)2^{-0.000316190262n}+26e^{-2\cdot10^{-20}(w_{\min}n-1)}.$$
--   These are used in the length condition and the failure bound of Theorem 1.1.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Appendix C.2–C.3, (56), (58), Table 10, pp. 65–68

import Mathlib
import Definitions.Def_RandModSubsetSum_Strata
import Definitions.Def_RandModSubsetSum_Problem

namespace RandModSubsetSum

/-- The operand bit-length bound `L_β(n) = ⌈10⁶ (β + 1)(n + 1)²⌉` of (56), p. 65.
Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Appendix C.2, (56), p. 65. -/
noncomputable def Lbeta (β : ℝ) (n : ℕ) : ℕ := ⌈(10 : ℝ) ^ 6 * (β + 1) * ((n : ℝ) + 1) ^ 2⌉₊

/-- The per-operation cost bound `A_β(n) = 2⁴⁰ (L_β(n) + 1)⁶` of (56), p. 65. -/
noncomputable def Abeta (β : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ 40 * ((Lbeta β n : ℝ) + 1) ^ 6

/-- The common polynomial overhead `Π_β(n) = 2^{100000} (n + 1)^{1500000} A_β(n)` of (58), p. 67. -/
noncomputable def Pibeta (β : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 100000 * ((n : ℝ) + 1) ^ 1500000 * Abeta β n

/-- `w_min = min_r w_r` for the paper's weights (Appendix C.1, p. 64; it equals
`w₄ = 0.00131475488563929695`). -/
noncomputable def wmin : ℝ := Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ paperWeight

/-- `F_β(n)`: the sum of the nine failure bounds of Table 10 (p. 68), time and space counted
separately (Appendix C.3, p. 67): permutation generation `n 2^{−n}`; prime setup `16 e^{−n/(4β)}`;
deviation from uniform residues `2¹⁶ n 2^{−10⁻⁶ n}`; no representation satisfies all residue
constraints `2^{−1.000026·10⁻⁶ n + 736548 log₂ n + 41042}`; leaf half partitions
`19968 e^{−10⁻¹²(w_min n − 2)}`; coordinate partitions and tag trials `8255 e^{−n²}`; time limit
`Π_β(n) 2^{−0.000406782870 n}`; space limit `Π_β(n) 2^{−0.000316190262 n}`; root not nearly balanced
in every stratum `26 e^{−2·10⁻²⁰ (w_min n − 1)}`. Decimals are exact rationals. -/
noncomputable def Fbeta (β : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (2 : ℝ) ^ (-(n : ℝ)) +
  16 * Real.exp (-(n : ℝ) / (4 * β)) +
  (2 : ℝ) ^ 16 * n * (2 : ℝ) ^ (-(1 / 10 ^ 6) * (n : ℝ)) +
  (2 : ℝ) ^ (-(1000026 / 10 ^ 12) * (n : ℝ) + 736548 * Real.logb 2 n + 41042) +
  19968 * Real.exp (-(1 / 10 ^ 12) * (wmin * n - 2)) +
  8255 * Real.exp (-((n : ℝ) ^ 2)) +
  Pibeta β n * (2 : ℝ) ^ (-(406782870 / 10 ^ 12) * (n : ℝ)) +
  Pibeta β n * (2 : ℝ) ^ (-(316190262 / 10 ^ 12) * (n : ℝ)) +
  26 * Real.exp (-(2 / 10 ^ 20) * (wmin * n - 1))

end RandModSubsetSum


