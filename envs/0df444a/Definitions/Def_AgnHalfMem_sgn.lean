-- Prove2me | Definitions.Def_AgnHalfMem_sgn
-- name    : AgnHalfMem_sgn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:37.633251+00:00
-- url     : https://prove2.me/theorems/ee0c1908-b34f-42b4-8409-fcba8e10bfb6
-- title:
--   Labels $\pm1$ and the sign function with $\mathrm{sign}(0)=+1$
-- statement:
--   Labels $y\in\{-1,1\}$ are encoded as Booleans, with `true` standing for $+1$ and `false` for $-1$; $\mathrm{sgn}(y)\in\{-1,1\}$ is the real value of a label. The **sign function** is
--   $$
--   \mathrm{sign}(t)=\begin{cases}+1,& t\ge 0,\\ -1,& t<0,\end{cases}
--   $$
--   returned as a label. In particular $\mathrm{sign}(0)=+1$, as in the paper's footnote.
--
--   These two conversions are used by every statement of the mission: halfspaces output $\mathrm{sign}(\langle w,x\rangle)$, and correlations $\mathbb E[f(x)h(x)]$ use the real values of labels.
--
--   **Formalization Note** This is not Mathlib's `Real.sign`, which has $\mathrm{sign}(0)=0$.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §1, footnote 1, p.2

import Mathlib

namespace AgnHalfMem

/-- **Labels and the sign function.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for
Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), §1, footnote 1, p.2: "The function sign : ℝ → {−1, 1} is defined by
sign(y) = 1 if y ≥ 0 and −1 otherwise."

`sgn b` is the real value `±1` of a label `b : Bool`, and `signB t` is `sign(t)` as a label.

**Formalization Note.** Labels in `{−1, 1}` are encoded as `Bool`, with `true ↔ +1` and
`false ↔ −1`; `sgn` recovers the real value. `signB 0 = true`, i.e. `sign(0) = +1` as in the
footnote (this is not Mathlib's `Real.sign`, which has `Real.sign 0 = 0`). -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- `sign(t)` as a label: `true` (i.e. `+1`) iff `0 ≤ t` (footnote 1, p.2). -/
noncomputable def signB (t : ℝ) : Bool := decide (0 ≤ t)

end AgnHalfMem


