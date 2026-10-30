-- Prove2me | Definitions.Def_RoslingAssembly_HistOK
-- name    : RoslingAssembly_HistOK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:38:01.184082+00:00
-- url     : https://prove2.me/theorems/43129edf-42c4-42df-be14-27eba638b973
-- title:
--   Consistent pre-horizon history
-- statement:
--   Constraint (3) in the first periods refers to positions $Y_{it}$ and demands $\xi_t$ of periods $t\le0$, before the horizon. A pre-horizon history is **consistent** if it satisfies (3) itself in the periods $-\bar L\le t\le0$, where $\bar L=\max_i l_i$:
--   $$Y_{i,t-1}-\xi_{t-1}\le Y_{it}\le Y_{k,t-l_k}-\sum_{s=t-l_k}^{t-1}\xi_s\qquad(k\in P(i)).$$
--   This says that the history is a state the physical system could have been in.
--
--   **Formalization Note** This is a reading: the paper does not specify the history. Without a condition of this kind problem P may have no feasible policy: with two items, item 2 assembled into item 1, $l_1=0$, $l_2=1$, $Y_{1,0}=5$, $Y_{2,0}=0$ and $\xi_0=0$, constraint (3) at $t=1$ requires $5=X_{11}\le Y_{11}\le X^l_{21}=0$. Only the window $-\bar L\le t\le 0$ is required.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, pp. 566–567, Problem P, (3) (reading)

import Mathlib
import Definitions.Def_RoslingAssembly_Network_P

namespace RoslingAssembly

/-- **Consistent pre-horizon history** (reading of §1, pp. 566–567). Rosling, *Optimal Inventory
Policies for Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 567,
Problem P: "X_it ≤ Y_it ≤ X^l_kt for all k ∈ P(i) and all i, t (3)" with "X^l_kt = Y_{k,t−l_k} −
Σ_{s=t−l_k}^{t−1} ξ_s" and "X_it = Y_{i,t−1} − ξ_{t−1}"; p. 566: "Note that X^l_it ≥ Y_kt if
i ∈ P(k)".

Constraint (3) in periods `t ≥ 1` refers to positions `Y` and demands `ξ` of periods `≤ 0`, which
are given data `Yh`, `ξh`. `HistOK net ℓ Yh ξh` says that this history is a state the system
could have been in: constraint (3) holds, computed from the history alone, in every period
`t` with `−L̄ ≤ t ≤ 0`, where `L̄ = max_i l_i`:
$$Y_{i,t-1}-\xi_{t-1}\le Y_{it}\le Y_{k,t-l_k}-\sum_{s=t-l_k}^{t-1}\xi_s\quad(k\in P(i)).$$

**Formalization Note.** This is a reading: the paper does not state the pre-horizon history,
but without some such condition problem P can have no feasible policy (two items, `l_1 = 0`,
`l_2 = 1`, `Y_{1,0} = 5`, `Y_{2,0} = 0`, `ξ_0 = 0`: then `5 = X_11 ≤ Y_11 ≤ X^l_21 = 0`). Only the
window `−L̄ ≤ t ≤ 0` is required, not the whole past. Periods are integers with the paper's
numbering; `Finset.Ico (t − l_k) t` is the paper's Σ_{s=t−l_k}^{t−1}. -/
def HistOK {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) : Prop :=
  ∀ t : ℤ, -((Finset.univ.sup ℓ : ℕ) : ℤ) ≤ t → t ≤ 0 → ∀ i : Fin N,
    Yh (t - 1) i - ξh (t - 1) ≤ Yh t i ∧
      ∀ k ∈ net.P i, Yh t i ≤ Yh (t - ℓ k) k - ∑ s ∈ Finset.Ico (t - ℓ k) t, ξh s

end RoslingAssembly


