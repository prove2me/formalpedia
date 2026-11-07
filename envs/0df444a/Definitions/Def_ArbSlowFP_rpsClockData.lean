-- Prove2me | Definitions.Def_ArbSlowFP_rpsClockData
-- name    : ArbSlowFP_rpsClockData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:50:06.130109+00:00
-- url     : https://prove2.me/theorems/b81ae9ca-e82a-4562-a121-5cc176a178be
-- title:
--   RPS clock data (10)–(11) of Proposition 5.1
-- statement:
--   The rock–paper–scissors clock data are
--   $$A_{\mathrm{RPS}}=\begin{pmatrix}0&-1&1\\1&0&-1\\-1&1&0\end{pmatrix},\quad R_2=\begin{pmatrix}1&1\\-11/3&-2\\2/3&1\end{pmatrix},\quad C_2=\begin{pmatrix}5&3\\6&3\\7&3\end{pmatrix},$$
--   with $W_2(q)=0^{3q+5}1^{3q+6}2^{3q+7}$, entry action $b=0$, counter $v=(0,-1,1)$, $Q_2=1$, $\delta_0=1$, $A_2=1$ and $\hat Q_2(\epsilon)=1$.
--
--   This is the base of the recursive family.
--
--   **Formalization Note** The priority is $0\prec1\prec2$; it never decides a play, by Proposition 5.1.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), pp.16, 32; eqs. (10), (11), Proposition 5.1

import Mathlib
import Definitions.Def_ArbSlowFP_IsClock

open Matrix

namespace ArbSlowFP

/-- The RPS payoff matrix (10), p.16. -/
def rpsA : Matrix (Fin 3) (Fin 3) ℚ := !![0, -1, 1; 1, 0, -1; -1, 1, 0]

/-- The score table `R₂` of (11), p.16. -/
def rpsR : Matrix (Fin 3) (Fin 2) ℚ := !![1, 1; -11 / 3, -2; 2 / 3, 1]

/-- The count table `C₂` of (11), p.16. -/
def rpsC : Matrix (Fin 3) (Fin 2) ℚ := !![5, 3; 6, 3; 7, 3]

/-- The word `W₂(q) = 0^{3q+5} 1^{3q+6} 2^{3q+7}` of (11), p.16. -/
def rpsW (q : ℕ) : List (Fin 3) :=
  List.replicate (3 * q + 5) 0 ++ List.replicate (3 * q + 6) 1 ++ List.replicate (3 * q + 7) 2

/-- The RPS clock data of Proposition 5.1, p.32: (10)–(11), `b = 0`, `v = (0, -1, 1)`, `Q₂ = 1`,
`δ₀ = 1`, `A₂ = 1`, `Q̂₂(ϵ) = 1`.

**Formalization Note.** The priority is `0 ≺ 1 ≺ 2`. Proposition 5.1 asserts unique best responses in
its phase words, so the priority never decides a play. -/
def rpsClockData : ClockData 2 (Fin 3) where
  A := rpsA
  rank := fun i => (i : ℕ)
  R := rpsR
  C := rpsC
  b := 0
  v := ![0, -1, 1]
  Q := 1
  W := rpsW
  δ0 := 1
  Ak := 1
  Qhat := fun _ _ => 1

end ArbSlowFP


