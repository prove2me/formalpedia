-- Prove2me | Definitions.Def_StochAutoreg_majF
-- name    : StochAutoreg_majF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:39.678633+00:00
-- url     : https://prove2.me/theorems/4002122c-9a70-46bf-80ee-e18eae20b017
-- title:
--   Majority amplification $F_J(t)=\Pr\{\mathrm{Bin}(J,1/2+t)>J/2\}$
-- statement:
--   For $J\in\mathbb N$ and $t\in\mathbb R$,
--
--   $$F_J(t)=\Pr\{\mathrm{Bin}(J,\tfrac12+t)>J/2\}=\sum_{k\le J,\ 2k>J}\binom Jk\bigl(\tfrac12+t\bigr)^k\bigl(\tfrac12-t\bigr)^{J-k}.$$
--
--   **Formalization Note** The polynomial is defined for every real $t$; the paper uses it for small $t$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §7, p.14

import Mathlib

namespace StochAutoreg

/-- `F_J(t) = Pr{Bin(J, 1/2 + t) > J/2}`, the finite binomial sum over `k` with `2k > J`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §7 "Majority amplification", p.14. -/
noncomputable def majF (J : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (J + 1)).filter (fun k => J < 2 * k),
    (J.choose k : ℝ) * (1 / 2 + t) ^ k * (1 / 2 - t) ^ (J - k)

end StochAutoreg


