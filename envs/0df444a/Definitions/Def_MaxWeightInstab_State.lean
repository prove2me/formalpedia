-- Prove2me | Definitions.Def_MaxWeightInstab_State
-- name    : MaxWeightInstab_State
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:31.096898+00:00
-- url     : https://prove2.me/theorems/56dfa354-8f44-4e02-aa57-230f12918912
-- title:
--   Queue-length vectors $Q\in\mathbb Z_+^{2J+2}$
-- statement:
--   A **queue-length vector** of the network of Figure 1 is $Q=(Q_j:j\in\mathcal J)\in\mathbb Z_+^{2J+2}$, one nonnegative integer per queue $\mathcal A_0,\dots,\mathcal A_J,\mathcal B_0,\dots,\mathcal B_J$. Schedules $\sigma\in\mathbb Z_+^{2J+2}$ (amounts of service allocated to each queue in one time unit) live in the same space.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, p.1 and p.3

import Mathlib
import Definitions.Def_MaxWeightInstab_Queue

namespace MaxWeightInstab

/-- A vector of queue lengths `Q = (Q_j : j ∈ 𝒥) ∈ ℤ₊^{|𝒥|}` for the network of Figure 1
(Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.1 and p.3). The same type carries schedules `σ ∈ ℤ₊^{|𝒥|}` (p.1). -/
abbrev State (J : ℕ) : Type := Queue J → ℕ

end MaxWeightInstab


