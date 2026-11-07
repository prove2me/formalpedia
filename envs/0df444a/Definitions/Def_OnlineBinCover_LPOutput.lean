-- Prove2me | Definitions.Def_OnlineBinCover_LPOutput
-- name    : OnlineBinCover_LPOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:50:28.740647+00:00
-- url     : https://prove2.me/theorems/a477961c-365d-40e7-aae9-30f5e2787954
-- title:
--   Input and output layout of the offline LP program of Lemma 2.2
-- statement:
--   Lemma 2.2 asserts that an LP solution can be **computed**. On the real RAM:
--
--   1. **Input.** Integer cell $0$ holds $n$; real cell $0$ holds $\varepsilon$, and real cell $1+i$ holds $s_i$.
--   2. **Output.** Integer cell $-1$ holds the number $m$ of output configurations. For $q<m$ and $j<K$, integer cell $-2-qK-j$ holds the count of group $j$ in configuration $C_q$, and real cell $-1-q$ holds the value $x_{C_q}$.
--   3. The decoded solution is $x=\sum_{q<m}x_{C_q}\,\mathbf 1_{C_q}$.
--
--   This fixes what "we can compute $x$" means for the machine statement of Lemma 2.2.
--
--   **Formalization Note** Counts are read with `Int.toNat`; a configuration listed twice adds its values.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma 2.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_OnlineBinCover_ConfigLP

namespace OnlineBinCover

/-!
# Input and output layout of an offline LP program (Lemma 2.2)

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), Lemma 2.2, p.8 ("We can compute a basic
feasible solution x of (3) … in time polynomial in the input size and 1/ε").

**Formalization Note.**
* *Input.* Integer cell `0` holds `n`; real cell `0` holds `ε` and real cell `1 + i` holds `s_i`
  (`PNormReg.initState [n] (ε :: s)`).
* *Output.* Integer cell `−1` holds the number `m` of output configurations. For `q < m` and
  `j < K`, integer cell `−2 − qK − j` holds the count `C_q j` (read with `Int.toNat`), and real cell
  `−1 − q` holds the value `x_{C_q}`. The decoded solution is `∑_q single C_q x_{C_q}`, so a repeated
  configuration adds its values.
-/

/-- The initial state holding `n`, `ε` and the sizes. -/
noncomputable def lpInput {n : ℕ} (s : Fin n → ℝ) (ε : ℝ) : PNormReg.State :=
  PNormReg.initState [(n : ℤ)] (ε :: List.ofFn s)

/-- The configuration number `q` written in the output layout. -/
noncomputable def outConfig (K : ℕ) (st : PNormReg.State) (q : ℕ) : Fin K → ℕ :=
  fun j => (st.integerMemory (-2 - (q : ℤ) * K - (j : ℕ))).toNat

/-- The LP solution decoded from a halted state. -/
noncomputable def decodeLP (ε : ℝ) (st : PNormReg.State) : (Fin (Kof ε) → ℕ) →₀ ℝ :=
  ∑ q ∈ Finset.range (st.integerMemory (-1)).toNat,
    Finsupp.single (outConfig (Kof ε) st q) (st.core.mem (-1 - (q : ℤ)))

end OnlineBinCover


