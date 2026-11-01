-- Prove2me | Definitions.Def_MaxWeightInstab_maxA
-- name    : MaxWeightInstab_maxA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:22.068811+00:00
-- url     : https://prove2.me/theorems/e7effb90-e00d-41a2-a890-e7a30c18dedf
-- title:
--   Longest externally fed queue of component $\mathcal A$
-- statement:
--   $\max_{j=1,\dots,J}Q_{\mathcal A_j}$, the length of the longest of the queues $\mathcal A_1,\dots,\mathcal A_J$, used in the stopping time $V$ of (21).
--
--   **Formalization Note** It is $0$ when $J=0$, a case excluded wherever it is used ($\nu<J$).
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (21), p.8

import Mathlib
import Definitions.Def_MaxWeightInstab_State

namespace MaxWeightInstab

/-- `max_{j=1,…,J} Q_{𝒜_j}`, the longest externally fed queue of component `𝒜` (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, (21), p.8).

**Formalization Note.** Written as a `Finset.sup` over `ℕ`; it is `0` when `J = 0`, a case every
statement using it excludes (`ν < J`). -/
def maxA {J : ℕ} (x : State J) : ℕ :=
  Finset.univ.sup fun j : Fin J => x (Sum.inl j.succ)

end MaxWeightInstab


