-- Prove2me | Definitions.Def_AllPhotonicRepeater_indirectZSuccess
-- name    : AllPhotonicRepeater_indirectZSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:34.341992+00:00
-- url     : https://prove2.me/theorems/873f46ab-74dd-4003-97b1-db5d79dc2553
-- title:
--   Indirect $Z$-measurement success probability $R_k$ on a tree cluster state
-- statement:
--   A **tree cluster state** with branching parameters $b_0,b_1,\dots,b_l$ encodes one qubit so that it can be measured despite photon loss: each qubit of the $k$th level has $b_k$ children in level $k+1$ ($k=0,\dots,l$), so that the 1st level holds $b_0$ qubits, and every photon is lost independently with probability $\epsilon_0$. A qubit of the $k$th level whose photon is lost can still be measured in the $Z$ basis *indirectly*, through a direct $X$ measurement on one of its children and direct or indirect $Z$ measurements on all of that child's children.
--
--   The success probability $R_k$ of such an indirect $Z$-basis measurement on a qubit of the $k$th level is defined recursively by
--   $$
--   R_k=1-\Big[1-(1-\epsilon_0)\,(1-\epsilon_0+\epsilon_0R_{k+2})^{b_{k+1}}\Big]^{b_k}\qquad(0\le k\le l),
--   $$
--   with $R_k=0$ and $b_k=0$ for $k>l$.
--
--   $R_1$ enters the loss-tolerant $Z$ measurement (A13) and $R_0$ is the loss-tolerant $X$ measurement (A16); both feed the repeater success probability (C1).
--
--   **Formalization Note** The paper prints (A3) "through $1\le k\le l$, $R_{l+1}:=0$, and $b_{l+1}:=0$". It is used here also at $k=0$, as (A16) and (A12) require. Beyond the last level $R_k=0$ and the exponent $b_{k+1}$ is read as $0$; $R_{l+2}$ enters only $R_l$ raised to the power $0$, so its value never matters. Powers are natural-number powers with $0^0=1$, the paper's own convention. Only $b_0,\dots,b_l$ are read.
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. A1, Eq. (A3), p. 7; App. A2, Eqs. (A7), (A9), (A12), p. 8

import Mathlib

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- The success probability `R_k` of an indirect `Z`-basis measurement on a qubit in the `k`th
level of a tree cluster state with branching parameters `b 0, …, b l`, when every photon is lost
independently with probability `ε0` (Azuma, Tamaki, Lo, *All photonic quantum repeaters*,
arXiv:1309.7207v1, App. A1, Eq. (A3), p. 7; App. A2, Eqs. (A7), (A9), (A12), p. 8):

`R_k = 1 − [1 − (1 − ε0)(1 − ε0 + ε0 R_{k+2})^{b_{k+1}}]^{b_k}` for `k ≤ l`, and `R_k = 0` for `k > l`,
with `b_{l+1} := 0`.

**Formalization Note** (A3) is printed "through 1 ≤ k ≤ l"; it is used here also at `k = 0`,
because (A16) reads `P_X = R_0` and (A7), (A9), (A12) give
`R_k = Σ_{m_k=1}^{b_k} T_k(m_k) = 1 − (1 − S_k)^{b_k}` at every level, `k = 0` included.
The paper sets only `R_{l+1} := 0` and `b_{l+1} := 0`; here `R_k = 0` for every `k > l` and the
exponent `b_{k+1}` is read as `0` whenever `k + 1 > l`. `R_{l+2}` enters only `R_l`, raised to
the power `b_{l+1} = 0`, so its value never matters. Only `b 0, …, b l` are read.
Exponents are natural-number powers, and `0 ^ 0 = 1`, which is the paper's convention
(`b_{l+1} = 0` makes the factor `1`). The recursion `R k ↦ R (k + 2)` terminates by the measure
`l + 1 − k`. -/
noncomputable def indirectZSuccess (ε0 : ℝ) (l : ℕ) (b : ℕ → ℕ) (k : ℕ) : ℝ :=
  if hk : k ≤ l then
    1 - (1 - (1 - ε0) * (1 - ε0 + ε0 * indirectZSuccess ε0 l b (k + 2)) ^
      (if k + 1 ≤ l then b (k + 1) else 0)) ^ b k
  else 0
termination_by l + 1 - k
decreasing_by omega

end AllPhotonicRepeater


