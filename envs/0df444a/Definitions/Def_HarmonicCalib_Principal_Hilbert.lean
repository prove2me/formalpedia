-- Prove2me | Definitions.Def_HarmonicCalib_Principal_Hilbert
-- name    : HarmonicCalib_Principal_Hilbert
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:05:09.852421+00:00
-- url     : https://prove2.me/theorems/e222c706-5a3e-4480-a16c-96a7f6572bba
-- title:
--   Harmonic numbers $h_t$, the shifted discrete Hilbert matrix $K_T$, its normalization $\widehat K_T$, the class $\widehat{\mathcal H}_T$ and $\|\cdot\|_q$
-- statement:
--   Indices run over $0, \dots, T-1$ (`Fin T`).
--
--   * $h_t = \sum_{j=0}^{t-1} \frac{1}{2j+1}$, so $h_0 = 0$, $h_1 = 1$, $h_2 = 4/3$.
--   * The **shifted discrete Hilbert transform matrix** $(K_T)_{ts} = \dfrac{1}{2(t-s)-1}$ for $0 \le t, s < T$ (the denominator is odd, never $0$).
--   * Its **row–column normalization** $(\widehat K_T)_{ts} = \dfrac{1}{h_t\,(2(t-s)-1)}$ for $s < t$ and $(\widehat K_T)_{ts} = -\dfrac{1}{h_{s+1}\,(2(s-t)+1)}$ for $t \le s$.
--   * The **admissible class** $\widehat{\mathcal H}_T$ of real $T\times T$ matrices $H$ with $H_{ts} \ge 0$ for $s < t$, $H_{ts} \le 0$ for $t \le s$, $\sum_{s=0}^{t-1} H_{ts} = 1$ for every row $1 \le t < T$, and $-\sum_{t=0}^{s} H_{ts} = 1$ for every column $0 \le s < T$.
--   * For $x \in \mathbb R^T$ and $q \ge 1$: $\|x\|_q = \bigl(\sum_{t=0}^{T-1} |x_t|^q\bigr)^{1/q}$.
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), (2) p. 4, (4)–(6) p. 8, (9) p. 10, §3.1 p. 12

import Mathlib

namespace HarmonicCalib.Principal

/-! # Harmonic numbers, the shifted discrete Hilbert matrix and the class `Ĥ_T`
(Fishelson–Mohri 2026, (2) p. 4, (4)–(6) p. 8, (9) p. 10, §3.1 p. 12)

Indices are `0, …, T-1` (`Fin T`), as in the paper. -/

/-- `h_t = ∑_{j=0}^{t-1} 1/(2j+1)`, so `h_0 = 0`, `h_1 = 1`, `h_2 = 4/3` (p. 10). -/
noncomputable def harm (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, 1 / (2 * (j : ℝ) + 1)

/-- The shifted discrete Hilbert transform matrix `(K_T)_{ts} = 1/(2(t-s)-1)`, `0 ≤ t, s < T`
((2), p. 4). The denominator is an odd integer, never zero. -/
noncomputable def hilbertK (T : ℕ) : Matrix (Fin T) (Fin T) ℝ :=
  fun t s => 1 / (2 * ((t : ℝ) - (s : ℝ)) - 1)

/-- The normalized matrix `K̂_T` ((9), p. 10):
`(K̂_T)_{ts} = 1/[h_t (2(t-s)-1)]` for `s < t` and `-1/[h_{s+1} (2(s-t)+1)]` for `t ≤ s`. -/
noncomputable def hilbertKhat (T : ℕ) : Matrix (Fin T) (Fin T) ℝ :=
  fun t s =>
    if s < t then 1 / (harm (t : ℕ) * (2 * ((t : ℝ) - (s : ℝ)) - 1))
    else -1 / (harm ((s : ℕ) + 1) * (2 * ((s : ℝ) - (t : ℝ)) + 1))

/-- The class `Ĥ_T` of (6), p. 8: `H_{ts} ≥ 0` for `s < t`, `H_{ts} ≤ 0` for `t ≤ s`,
every row `t ≥ 1` has `∑_{s<t} H_{ts} = 1`, and every column `s` has `-∑_{t≤s} H_{ts} = 1`. -/
def IsAdmissible (T : ℕ) (H : Matrix (Fin T) (Fin T) ℝ) : Prop :=
  (∀ t s : Fin T, s < t → 0 ≤ H t s) ∧
  (∀ t s : Fin T, t ≤ s → H t s ≤ 0) ∧
  (∀ t : Fin T, 1 ≤ (t : ℕ) → ∑ s ∈ Finset.univ.filter (fun s : Fin T => s < t), H t s = 1) ∧
  (∀ s : Fin T, -(∑ t ∈ Finset.univ.filter (fun t : Fin T => t ≤ s), H t s) = 1)

/-- `‖x‖_q = (∑_{t=0}^{T-1} |x_t|^q)^{1/q}` for `x ∈ ℝ^T` (p. 12). -/
noncomputable def lqNorm (q : ℝ) {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  (∑ t, |x t| ^ q) ^ (1 / q)

end HarmonicCalib.Principal


