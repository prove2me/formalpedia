-- Prove2me | Definitions.Def_AlmostMMS_deficit
-- name    : AlmostMMS_deficit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:21.766101+00:00
-- url     : https://prove2.me/theorems/48e09dcd-b472-438f-a7a1-e5b75fe89040
-- title:
--   Definitions 3.3, 2.11, pp.21, 15 — the deficit $\Delta(\pi)$ and the rate $\tau_i(\pi)$
-- statement:
--   The **deficit** of a head profile $\pi$ is $\Delta(\pi)=(1-1/q-v(\pi))_+$, where $v(\pi)=\sum_{\alpha\in\pi}\alpha$. The **tail load rate** of agent $i$ is
--   $$
--   \tau_i(\pi)=\begin{cases}\Delta(\pi)/T_i & \pi\ne\bot\text{ and }T_i>0,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   It is the fraction of each tail item that agent $i$ needs in order to cover the deficit of $\pi$.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 3.3, p.21; Definition 2.11, p.15

import Mathlib
import Definitions.Def_AlmostMMS_headCount

namespace AlmostMMS

open Finset

/-- **Deficit** `Δ(π) = (1 - 1/q - v(π))₊` of a head profile (Definition 3.3, p.21), where
`v(π) = ∑_{α ∈ π} α` (Definition 2.2, p.12) is `π.sum`.
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…). -/
noncomputable def deficit (q : ℕ) (π : Multiset ℝ) : ℝ :=
  max 0 (1 - 1 / (q : ℝ) - π.sum)

/-- **Tail load rate** `τ_i(π)` (Definition 2.11, p.15): `Δ(π)/T_i` when `π ≠ ⊥` and `T_i > 0`, and
`0` otherwise. The no-profile `⊥` is `none`. -/
noncomputable def tauOf {n m : ℕ} (v : Fin n → Fin m → ℝ) (q : ℕ) (i : Fin n) :
    Option (Multiset ℝ) → ℝ
  | none => 0
  | some π => if 0 < tailVal v q i then deficit q π / tailVal v q i else 0

end AlmostMMS


